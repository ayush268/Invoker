include "SimpleVerifier.dfy"
include "BoundedInts.dfy"

module SimpleVerifierAnalysis {
  import opened Lang
  import opened E = ConcreteEval
  import opened AbstractEval
  import opened Ints
  import opened BoundedInts

  datatype PathState = PathState(state: E.State, pc: int)

  datatype AbstractPathState = AbstractPathState(state: AbstractState, pc: int, branch_pcs: seq<int>)

  datatype AbstractPath = AbstractPath(path: seq<AbstractPathState>)
  datatype AnalysisResult = AnalysisResult(paths: seq<AbstractPath>)

  datatype VerifierState = VerifierState(insn_idx: nat)
  datatype VerifierStackElem = VerifierStackElem(prev_insn_idx: nat, insn_idx: nat, verifier_state: AbstractPathState)

  predicate state_equal(s1: E.State, s2: E.State) {
    forall r : Reg :: s1(r) == s2(r)
  }

  predicate stmt_step_valid(prog: Program, pc: int, env: E.State, pc': int, env': E.State)
    requires 0 <= pc <= |prog.stmts|
    requires 0 <= pc' <= |prog.stmts|
    requires (pc == |prog.stmts|) ==> (pc' == |prog.stmts|)
  {
    if pc == |prog.stmts| then
      true
    else
      var stmt := prog.stmts[pc];
      match E.stmt_step(env, stmt) {
        case Some((env'', offset)) =>
          (pc + offset == pc') && state_equal(env', env'')
        case None => false
      }
  }

  // TODO: Write predicate for a valid path
  // TODO: Relate 2 states at the same time
  predicate path_valid(prog: Program, path_states: seq<PathState>)
  {
    if |path_states| <= 1 then
      true
    else
    if path_states[0].pc < 0 || path_states[0].pc > |prog.stmts| then
      false
    else if path_states[0].pc == |prog.stmts| then
      (path_states[1].pc == |prog.stmts|) && path_valid(prog, path_states[1..])
    else
      var stmt := prog.stmts[path_states[0].pc];
      match E.stmt_step(path_states[0].state, stmt) {
        case Some((env', offset)) =>
          ((path_states[0].pc + offset) == path_states[1].pc) && path_valid(prog, path_states[1..])
        case None => false
      }
  }

  method m1(prog: Program, a: seq<PathState>, b: seq<PathState>)
    requires |a| > 0
  {
    assert a == [a[0]] + a[1..];
    assert bridges(prog, [a[0]], a[1..]) && path_valid(prog, a[1..]) <==> path_valid(prog, a);
  }


  lemma ValidPathConcat(prog: Program, path_states: seq<PathState>)
    requires |path_states| > 0
    requires path_valid(prog, path_states)
    ensures forall i :: 0 <= i < |path_states| - 1 ==> path_valid(prog, [path_states[i], path_states[i + 1]])
  {

  }

  predicate bridges(prog: Program, a: seq<PathState>, b: seq<PathState>)
  {
    if b == [] || a == [] then
      true
    else
    if a[|a| - 1].pc < 0 || a[|a| - 1].pc > |prog.stmts| then
      false
    else if a[|a| - 1].pc == |prog.stmts| then
      b[0].pc == |prog.stmts| //&& path_valid(prog, b)
    else
      var stmt := prog.stmts[a[|a| - 1].pc];
      match E.stmt_step(a[|a| - 1].state, stmt) {
        case Some((env', offset)) =>
          ((a[|a| - 1].pc + offset) == b[0].pc) //&& path_valid(prog, b)
        case None => false
      }
  }

  lemma ValidPathsConcat(prog: Program, a: seq<PathState>, b: seq<PathState>)
    ensures path_valid(prog, a + b) == (path_valid(prog, a) && bridges(prog, a, b) && path_valid(prog, b))
  {
    if a == [] {
      assert a + b == b;
      assert bridges(prog, a, b);
      assert path_valid(prog, a);
      assert path_valid(prog, a + b) == (path_valid(prog, a) && bridges(prog, a, b) && path_valid(prog, b));
    } else if b == [] {
      assert a + b == a;
      assert bridges(prog, a, b);
      assert path_valid(prog, b);
      assert path_valid(prog, a + b) == (path_valid(prog, a) && bridges(prog, a, b) && path_valid(prog, b));
    } else {
      assert |a + b| >= 2;
      assert a + b == [a[0]] + (a[1..] + b);
      assert path_valid(prog, a + b) == path_valid(prog, [a[0]] + (a[1..] + b));
    }
  }

  lemma PathBridgeConcat(prog: Program, a: seq<PathState>, bridge: PathState, b: seq<PathState>)
    ensures path_valid(prog, a + [bridge]) && bridges(prog, a + [bridge], b) && path_valid(prog, [bridge] + b) <==> path_valid(prog, a + [bridge] + b)
  {
    ValidPathsConcat(prog, a, [bridge]);
    assert path_valid(prog, a + [bridge]) == (path_valid(prog, a) && bridges(prog, a, [bridge]) && path_valid(prog, [bridge]));

    ValidPathsConcat(prog, [bridge], b);
    assert path_valid(prog, [bridge] + b) == (path_valid(prog, [bridge]) && bridges(prog, [bridge], b) && path_valid(prog, b));

    //ValidPathsConcat(prog, a + [bridge], b);
    assert a + ([bridge] + b) == (a + [bridge]) + b ;
    ValidPathsConcat(prog, a + [bridge], b);
    //assert path_valid(prog, a + [bridge] + b) == path_valid(prog, a + [bridge]) && bridges(prog, a + [bridge], b) && path_valid(prog, b);

    assert (a + [bridge] + b) == (a + ([bridge] + b));
    assert path_valid(prog, a + [bridge]) && path_valid(prog, [bridge] + b) ==> path_valid(prog, a) && path_valid(prog, b) && bridges(prog, a, [bridge]) && bridges(prog, [bridge], b);
  }

  function init_abs_reg_state(r: Reg): Val {
    //TODO: Maybe this should be (0, U64_MAX)
    //TODO: All registers are unconstrained
    Interval(0, U64_MAX as int)
  }

  function init_conc_reg_state(r: Reg): u32 {
    0
  }

  function initial_abstract_state(stmt: Stmt): AbstractPathState {
    AbstractPathState(AbstractState(init_abs_reg_state), 0, [])
  }

  function initial_concrete_state(stmt: Stmt): PathState {
    PathState(init_conc_reg_state, 0)
  }

  function push_stack(stack: seq<AbstractPathState>, new_state: AbstractPathState): seq<AbstractPathState> {
    stack + [new_state]
  }

  function backtrack_stack(stack: seq<AbstractPathState>, concrete_stack: seq<PathState>): (seq<AbstractPathState>, seq<PathState>)
    ensures |backtrack_stack(stack, concrete_stack).0| > 0 ==> |backtrack_stack(stack, concrete_stack).0[|backtrack_stack(stack, concrete_stack).0| - 1].branch_pcs| > 0
    ensures |stack| == |concrete_stack| ==> |backtrack_stack(stack, concrete_stack).0| == |backtrack_stack(stack, concrete_stack).1|
    ensures |stack| == |concrete_stack| && (forall j :: 0 <= j < |stack| ==> path_state_included(concrete_stack[j], stack[j]))
            ==> (forall i :: 0 <= i < |backtrack_stack(stack, concrete_stack).1| ==> path_state_included(backtrack_stack(stack, concrete_stack).1[i], backtrack_stack(stack, concrete_stack).0[i]))
  {
    if |stack| == 0 || |concrete_stack| == 0 then
      ([], [])
    else if |stack[|stack| - 1].branch_pcs| > 0 then
      (stack, concrete_stack)
    else
      backtrack_stack(stack[..|stack| - 1], concrete_stack[..|concrete_stack| - 1])
  }

  predicate reg_included(c_v: u32, v: Val) {
    v.lo <= c_v as int <= v.hi
  }

  predicate state_included(env: E.State, abs: AbstractState) {
    forall r: Reg :: reg_included(env(r), abs.rs(r))
  }

  predicate path_state_included(path_state: PathState, abs_path_state: AbstractPathState) {
    (path_state.pc == abs_path_state.pc) &&
    (state_included(path_state.state, abs_path_state.state))
  }

  

  method explore_abstract_paths(prog: Program, fuel: int, init_conc_state: PathState, init_abstract_state: AbstractPathState)
    requires fuel >= 0
    requires |prog.stmts| > 0
    requires path_state_included(init_conc_state, init_abstract_state)
  {
    var stack : seq<AbstractPathState> := [init_abstract_state];
    var fuel := fuel;
    var concrete_stack : seq<PathState> := [init_conc_state];

    assert (path_state_included(concrete_stack[0], stack[0]));
    assert |concrete_stack| == |stack|;
    assert path_valid(prog, concrete_stack);

    while fuel > 0 && |stack| > 0
      invariant |concrete_stack| == |stack|
      // Proving that the actual execution is a subset of the static path wrt all taken branches
      invariant forall i :: 0 <= i < |stack| ==> path_state_included(concrete_stack[i], stack[i])
      //invariant path_valid(prog, concrete_stack);
    {
      // Pop topmost state from the abstract path stack
      var cur_state := stack[|stack| - 1];
      var cur_pc := cur_state.pc;
      stack := stack[..|stack| - 1];

      // Pop topmost state from the concrete path stack
      var cur_conc_state := concrete_stack[|concrete_stack| - 1];
      var cur_conc_pc := cur_conc_state.pc;
      concrete_stack := concrete_stack[..|concrete_stack| - 1];
      //assert path_valid(prog, concrete_stack);

      if cur_pc < 0 || cur_pc > |prog.stmts| {
        // We should never encounter this
        break;
      }

      if cur_pc == |prog.stmts| {
        // We hit the end of this concrete execution

        // Commenting out backtracking code
        // We hit the end of the subroutine
        // Backtrack till an abstract state with |branch_pcs| > 0 and
        // explore one of those paths
        /*var s := backtrack_stack(stack, concrete_stack);
        stack := s.0;
        concrete_stack := s.1;

        if |stack| > 0 {
          var last_state := stack[|stack| - 1].state;
          var last_pc := stack[|stack| - 1].pc;
          var last_branches := stack[|stack| - 1].branch_pcs;

          var new_pc := stack[|stack| - 1].branch_pcs[0];

          var new_branch_state := AbstractPathState(last_state, last_pc, last_branches[1..]);
          stack := stack[|stack| - 1 := new_branch_state];

          var new_expl_state := AbstractPathState(last_state, new_pc, []);
          stack := push_stack(stack, new_expl_state);

          var last_conc_state := concrete_stack[|concrete_stack| - 1].state;
          var last_conc_pc := concrete_stack[|concrete_stack| - 1].pc;
          concrete_stack := concrete_stack + [PathState(last_conc_state, new_pc)];

        }
        fuel := fuel - 1;
        continue;*/
        break;
      }

      // Continue exploring the path
      var cur_stmt := prog.stmts[cur_state.pc];
      var conc_step := stmt_step(cur_conc_state.state, cur_stmt);

      if conc_step.None? {
        // Invalid Execution Path
        break;
      }

      assert cur_conc_pc == cur_pc;

      match cur_stmt {
        case Assign(r, e) => {

          var v := AbstractEval.expr_eval(cur_state.state, e);
          var new_state := AbstractEval.update_state(cur_state.state, r, v);
          // We rewrite the branches array when this state is being popped off
          // Iff it is a branch instruction
          var new_abs_state := AbstractPathState(new_state, cur_pc + 1, []);
          stack := push_stack(stack, new_abs_state);

          assert conc_step.v.1 == 1;
          var new_conc_state := PathState(conc_step.v.0, cur_pc + conc_step.v.1);
          concrete_stack := concrete_stack + [new_conc_state];

          assert (path_state_included(new_conc_state, new_abs_state));
          assert path_state_included(concrete_stack[|concrete_stack| - 1], stack[|stack| - 1]);

          assert bridges(prog, [cur_conc_state], [new_conc_state]);
          assert bridges(prog, concrete_stack + [cur_conc_state], [new_conc_state]);
        }

        case JmpZero(r, offset) => {
          // Copied from AbstractEval.stmt_eval
          // imprecise analysis: we don't try to prove that this jump is or isn't taken
          var fall_through := AbstractPathState(cur_state.state, cur_pc + 1, []);
          var jmp_targ := AbstractPathState(cur_state.state, cur_pc + offset as int, []);
          var jmp_state := AbstractPathState(cur_state.state, cur_pc, []);

          var jmp_conc_state := PathState(cur_conc_state.state, cur_pc);
          var jmp_conc_targ := PathState(cur_conc_state.state, cur_pc + offset as int);
          var conc_fall_through := PathState(cur_conc_state.state, cur_pc + 1);

          assert (path_state_included(jmp_conc_targ, jmp_targ));
          assert (path_state_included(conc_fall_through, fall_through));

          // We are interested in only the actual branch that is taken
          if conc_step.v.1 == offset as int {
            // Explore the target branch
            stack := push_stack(push_stack(stack, jmp_state), jmp_targ);
            concrete_stack := concrete_stack + [jmp_conc_state] + [jmp_conc_targ];
            assert(cur_conc_state == jmp_conc_state);
            assert (path_valid(prog, [jmp_conc_state, jmp_conc_targ]));
          } else {
            stack := push_stack(push_stack(stack, jmp_state), fall_through);
            concrete_stack := concrete_stack + [jmp_conc_state] + [conc_fall_through];
            assert (path_valid(prog, [jmp_conc_state, conc_fall_through]));
          }
          assert path_state_included(concrete_stack[|concrete_stack| - 1], stack[|stack| - 1]);
        }
      }

      fuel := fuel - 1;
    }
  }

  predicate programWellFormed(prog: Program) {
    true
  }

  function pushAbstractPath(absPath: AbstractPath, state: AbstractPathState) : AbstractPath {
    AbstractPath(absPath.path + [state])
  }

  function exploreTillBranch(prog: Program, inst_idx: nat, abs_state: AbstractState, fuel: int) : AbstractPath 
    requires |prog.stmts| > 0
    requires fuel >= 0
    decreases fuel
  {
    var empty : AbstractPath := AbstractPath([]);

    if inst_idx >= |prog.stmts| then
      empty
    else

      var cur_inst := prog.stmts[inst_idx];

      if fuel > 0 then 
        match cur_inst {
          case JmpZero(_, _) => empty
          case Assign(r, e) => 
            var v := AbstractEval.expr_eval(abs_state, e);
            var new_state := AbstractEval.update_state(abs_state, r, v);
            var path_state := AbstractPathState(new_state, inst_idx, []);
            if inst_idx == |prog.stmts| - 1 then 
              AbstractPath([path_state])
            else
              var rest_of_path := exploreTillBranch(prog, inst_idx + 1, new_state, fuel - 1);
              AbstractPath([path_state] + rest_of_path.path)
        }
      else
        empty

    //ret
  }

  // TODO: Write a method for state space exploration and then reason about the datastructure that is used
  // Each sequence on the stack is a valid path --> need to abstract eval and real eval the path


  // The idea is to prove that the kernel's implementation of state space exploration and merging (or a lack thereof) is
  // semantically equivalent to a general abstract interpretation procedure over the same domains used by the kernel
  // The kernel explores each path in the program in a depth first manner never merging paths, but performs updates to
  // the abstract values in each register as dictated by the instruction semantics
  // The intuition is that the kernel algorithm potentially obtains more fine grained information since it does not merge
  // abstract values over paths

  // Analysis result returns a subset of explored paths as bounded by fuel
  // Each path may not even be complete as in it does not result in an exit instruction
  //    A
  //    |
  //    B
  //   / \
  //  C   D
  // Theorem to prove 1: For all concrete initial states c, path(c) should be contained
  // in the corresponding abstract path of the Analysis result
  // Theorem to prove 2: The Analysis result should be implied as per the correctness of
  // a general abstract interpretation procedure over the same interval domain

  // TODO: Need to find a datastructure for holding the program paths
  // TODO: The initial abstract state is completely unconstrained for now
  method verifierExplorePaths(prog: Program, fuel: int) returns (y : AnalysisResult)
    requires fuel > 0
    requires |prog.stmts| > 0
    requires programWellFormed(prog)
  {

    var ret := AnalysisResult([]);
    var init_abs_state:= initial_abstract_state(prog.stmts[0]);
    var explored_states: seq<seq<AbstractState>> := [];
    var cur_inst_idx: nat := 0;
    var stack: seq<VerifierStackElem> := [];

    var path := exploreTillBranch(prog, cur_inst_idx, init_abs_state.state, fuel);

    return ret;
  }

}