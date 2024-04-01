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
  datatype VerifierWorkElem = VerifierWorkElem(prev_inst_idx: nat, inst_idx: nat, verifier_state: AbstractPathState, path: AbstractPath)

  datatype InstructionType = BranchInstruction | FunctionExit

  datatype ConcretePath = ConcretePath(path: seq<PathState>)

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

  // Returns the path along with whether the last instructucion was a branch or an exit
  function exploreTillBranchOrExit(prog: Program, inst_idx: nat, abs_state: AbstractState) : (AbstractPath, InstructionType) 
    requires |prog.stmts| > 0
    // Make sure that we stay within bounds of the program
    ensures inst_idx < |prog.stmts| ==> inst_idx + |exploreTillBranchOrExit(prog, inst_idx, abs_state).0.path| <= |prog.stmts|
    ensures inst_idx < |prog.stmts| && prog.stmts[inst_idx].JmpZero? ==> |exploreTillBranchOrExit(prog, inst_idx, abs_state).0.path| == 0
    ensures (forall i :: 0 <= i < |exploreTillBranchOrExit(prog, inst_idx, abs_state).0.path| < |prog.stmts| ==> 0 <= exploreTillBranchOrExit(prog, inst_idx, abs_state).0.path[i].pc < |prog.stmts|)

    // Make sure that instruction following the path is a branch instruction and everything in between is not a branch
    ensures inst_idx + |exploreTillBranchOrExit(prog, inst_idx, abs_state).0.path| < |prog.stmts| ==> 
      prog.stmts[inst_idx + |exploreTillBranchOrExit(prog, inst_idx, abs_state).0.path|].JmpZero? && 
      exploreTillBranchOrExit(prog, inst_idx, abs_state).1.BranchInstruction? && 
      (forall i :: inst_idx <= i < inst_idx + |exploreTillBranchOrExit(prog, inst_idx, abs_state).0.path| ==> !prog.stmts[i].JmpZero?) &&
      (forall i :: 0 <= i < |exploreTillBranchOrExit(prog, inst_idx, abs_state).0.path| ==> !prog.stmts[exploreTillBranchOrExit(prog, inst_idx, abs_state).0.path[i].pc].JmpZero?)
    
    // Make sure that we return a FunctionExit on an actual function exit and everything in between is not a branch
    ensures inst_idx + |exploreTillBranchOrExit(prog, inst_idx, abs_state).0.path| == |prog.stmts| ==>
      exploreTillBranchOrExit(prog, inst_idx, abs_state).1.FunctionExit? && (forall i :: inst_idx <= i < |prog.stmts| ==> !prog.stmts[i].JmpZero?) &&
      (forall i :: 0 <= i < |exploreTillBranchOrExit(prog, inst_idx, abs_state).0.path| < |prog.stmts| ==> !prog.stmts[exploreTillBranchOrExit(prog, inst_idx, abs_state).0.path[i].pc].JmpZero?)

    decreases |prog.stmts| - inst_idx
  {
    var empty_path : AbstractPath := AbstractPath([]);

    if inst_idx >= |prog.stmts| then
      assert |empty_path.path| == 0; 
      (empty_path, FunctionExit)
    else

      var cur_inst := prog.stmts[inst_idx];

      match cur_inst {
          case JmpZero(_, _) => (empty_path, BranchInstruction)
          case Assign(r, e) => 
            var v := AbstractEval.expr_eval(abs_state, e);
            var new_state := AbstractEval.update_state(abs_state, r, v);

            assert inst_idx < |prog.stmts|;
            var path_state := AbstractPathState(new_state, inst_idx, []);

            var rest_of_path := exploreTillBranchOrExit(prog, inst_idx + 1, new_state);
            (AbstractPath([path_state] + rest_of_path.0.path), rest_of_path.1)
      }


    //ret
  }

  function concatPaths(path1: AbstractPath, path2: AbstractPath) : AbstractPath {
    AbstractPath(path1.path + path2.path)
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


  // Completeness: Makes sure that all the possible paths of a program are explored
  // Theorem 1.1: The element on the top of the worklist, represents an abstract path fragment (A) ending at a branching instruction or exit
  // Theorem 1.2: The element on the top of the worklist, represents an abstract path fragment (A) such that the pc values traced out by A respects
  // the possible pc values given by verifierExploreConcretePath for any concrete path defined by an initial concrete state C contained in the initial abstract state
  // Theorem 1.3: The loop body adds the abstract path to the AnalysisResult on a function exit
  // Theorem 1.3: The loop body enqueues both the possible branch outcomes on the worklist, 
  // Theorem 1.4: The loop body extends the abstract path on the top of the stack by a basic block defined by exploreTillBranchOrExit
  // Theorem 1.5: exploreTillBranchOrExit respects the program pc values in a basic block defined by verifierExploreConcretePath

  // Soundness: Make sure that we over-approximate each possible concrete path
  // Theorem 2: Given an initial abstract state a, all the concrete states c contained in the abstract state a
  // form concrete paths path(c) and these concrete paths are contained in the abstract path traced out by verifierExplorePaths
  // path(c) is defined wrt the concrete semantics defined in verifierExploreConcretePath
  // Corollary: An abstract state containing all the possible initial concrete states, should explore an abstract path that contains all
  // possible executions of the program
  method verifierExplorePaths(prog: Program, fuel: int) returns (y : AnalysisResult)
    requires fuel > 0
    requires |prog.stmts| > 0
    requires programWellFormed(prog)
    requires has_valid_jump_targets(prog.stmts, 0)
  {
    var ret := AnalysisResult([]);
    var fuel := fuel;
    var cur_state := initial_abstract_state(prog.stmts[0]);
    var explored_states: seq<seq<AbstractState>> := [];
    var cur_inst_idx: nat := 0;
    var prev_inst_idx: nat := 0;


    var worklist: seq<VerifierWorkElem> := [VerifierWorkElem(0, 0, cur_state, AbstractPath([]))];
    var cur_path := AbstractPath([]);

    assert cur_inst_idx < |prog.stmts|;
    assert |worklist| == 1;
    assert forall i :: 0 <= i < |worklist| ==> worklist[i].inst_idx < |prog.stmts|;

    while fuel > 0 
      invariant forall i :: 0 <= i < |worklist| ==> worklist[i].inst_idx <= |prog.stmts|
    {

      if |worklist| == 0 {
        break;
      }

      // pop work item from stack
      var worklist_top := worklist[|worklist| - 1];
      prev_inst_idx := worklist_top.prev_inst_idx;
      cur_inst_idx := worklist_top.inst_idx;
      cur_path := worklist_top.path;
      cur_state := worklist_top.verifier_state;
      worklist := worklist[..|worklist| - 1];

      assert cur_inst_idx <= |prog.stmts|;

      var path := exploreTillBranchOrExit(prog, cur_inst_idx, cur_state.state);
      var branch_or_exit_idx : nat := cur_inst_idx + |path.0.path|;
      assert cur_inst_idx < |prog.stmts| ==> branch_or_exit_idx <= |prog.stmts|;
      
      
      match path.1 {
        case BranchInstruction =>
          var cur_inst := prog.stmts[branch_or_exit_idx];
          assert branch_or_exit_idx < |prog.stmts|;
          assert cur_inst.JmpZero?;

          match cur_inst {
            case JmpZero(_ , offset) =>
              has_valid_jump_targets_ok(prog.stmts);
              assert 0 <= branch_or_exit_idx as int + offset as int <= |prog.stmts|;
          
              var not_taken_pc := branch_or_exit_idx + 1;
              var taken_pc := branch_or_exit_idx as int + offset as int;

              // Checking if we are at a branch that happens to be the last instruction
              var next_abs_state := if |path.0.path| == 0 then cur_state.state else path.0.path[|path.0.path| - 1].state;

              // The abstract state at the branch instruction is the same as that of the previous (non-branching) instruction
              var branch_abs_state := AbstractPathState(next_abs_state, branch_or_exit_idx, [not_taken_pc, taken_pc]);
              var path_so_far := concatPaths(cur_path, concatPaths(path.0, AbstractPath([branch_abs_state])));

              var taken_pc_work_elem := VerifierWorkElem(branch_or_exit_idx, taken_pc, branch_abs_state, path_so_far);
              var not_taken_pc_work_elem := VerifierWorkElem(branch_or_exit_idx, not_taken_pc, branch_abs_state, path_so_far);

              worklist := worklist + [taken_pc_work_elem, not_taken_pc_work_elem];

          }
        case FunctionExit =>
          ret := AnalysisResult(ret.paths + [concatPaths(cur_path, path.0)]);
      }

      // Reached an exit, pop from the worklist
      /*if branch_or_exit_idx >= |prog.stmts| || |path.0.path| == 0 {
        // Add path to analysis result
        ret := AnalysisResult(ret.paths + [concatPaths(cur_path, path.0)]);

        if |worklist| == 0 {
          // We are done with the exploration
          break;
        } else {
          // Pop from the worklist
          var worklist_top := worklist[|worklist| - 1];
          prev_inst_idx := worklist_top.prev_inst_idx;
          cur_inst_idx := worklist_top.inst_idx;
          cur_path := worklist_top.path;
          cur_state := worklist_top.verifier_state;
          worklist := worklist[..|worklist| - 1];
        }

      } else {
  predicate path_state_included(path_state: P
          // Should happen only if we ran out of fuel for exploration
          case Assign(_, _) => 
            ret := AnalysisResult(ret.paths + [concatPaths(cur_path, path.0)]);
          case JmpZero(_ , offset) =>
            // We ended at a branch, we should push the taken branch onto the stack and continue exploring the not taken branch
          has_valid_jump_targets_ok(prog.stmts);
          assert 0 <= branch_or_exit_idx as int + offset as int <= |prog.stmts|;
          
          
          var not_taken_pc := branch_or_exit_idx + 1;
          var taken_pc := branch_or_exit_idx as int + offset as int;

          // The abstract state at the branch instruction is the same as that of the previous (non-branching) instruction
          var branch_abs_state := AbstractPathState(path.0.path[|path.0.path| - 1].state, branch_or_exit_idx, [not_taken_pc, taken_pc]);
          var path_so_far := concatPaths(cur_path, concatPaths(path.0, AbstractPath([branch_abs_state])));

          var last_work_elem := VerifierWorkElem(branch_or_exit_idx, taken_pc, branch_abs_state, path_so_far);
          worklist := worklist + [last_work_elem];

          // Continue exploring the not taken branch
          cur_inst_idx := not_taken_pc;
          prev_inst_idx := branch_or_exit_idx;
          cur_path := path_so_far;

        }
        
      }*/
      
      // Decrement 1 to ensure termination
      fuel := fuel - |path.0.path| - 1;
    }

    return ret;
  }

  // Concrete path exploration
  // Return None if we run out of fuel
  function verifierExploreConcretePath(prog: Program, pc: nat, initial_conc_state: E.State, fuel: nat) : Option<ConcretePath>
    requires fuel >= 0
    requires |prog.stmts| > 0
    requires pc <= |prog.stmts|
    requires programWellFormed(prog)
    requires has_valid_jump_targets(prog.stmts, 0)
    decreases fuel
  { 
    var cur_pc := pc;
    var cur_state := initial_conc_state;
    var ret := ConcretePath([PathState(cur_state, cur_pc)]);
    var fuel := fuel;

    if cur_pc == |prog.stmts| then
        Some(ret)
    else if fuel == 0 then
        None
    else
      var cur_inst := prog.stmts[cur_pc];
      match cur_inst {
        case Assign(r, e) => 
          var e' := E.expr_eval(cur_state, e);
          match e' {
            case Some(v) =>
              var cur_state := E.update_state(cur_state, r, v);
              var cur_pc := cur_pc + 1;
              var rest_of_path := verifierExploreConcretePath(prog, cur_pc, cur_state, fuel - 1);
              match rest_of_path {
                case Some(conc_path) =>
                  var ret := ConcretePath(ret.path + conc_path.path);
                  Some(ret)
                case None =>
                  None
              }
            case None =>
              // Return a partial path even if there is an error state
              var ret := ConcretePath(ret.path + [PathState(cur_state, cur_pc)]);
              Some(ret)
          }
        case JmpZero(r, offset) =>
          var jmp := if cur_state(r) == 0 then offset else 1;
          has_valid_jump_targets_ok(prog.stmts);
          assert cur_pc + jmp as int <= |prog.stmts|;
          var cur_pc := cur_pc + jmp as int;
          var rest_of_path := verifierExploreConcretePath(prog, cur_pc, cur_state, fuel - 1);
          match rest_of_path {
            case Some(conc_path) =>
              var ret := ConcretePath(ret.path + conc_path.path);
              Some(ret)
            case None =>
              None
          }
      }

  }  

  //lemma concretePathContainedInAbstractPath(prog: Program, initial_conc_state: E.State, initial_abstract_state: AbstractState, fuel: nat)
  //  requires state_included(initial_conc_state, initial_abstract_state)
  //{
  //  assert |verifierExploreConcretePath(prog, 0, initial_conc_state, fuel).path| == |verifierExplorePaths(prog, initial_abstract_state, fuel).path|;
  //}

}