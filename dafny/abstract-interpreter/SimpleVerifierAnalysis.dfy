include "SimpleVerifier.dfy"
include "BoundedInts.dfy"
include "ConcreteExecution.dfy"
include "helpers.dfy"

module SimpleVerifierAnalysis {
  import opened Lang
  import opened E = ConcreteEval
  import opened AbstractEval
  import opened ConcreteExecution
  import opened Ints
  import opened BoundedInts
  import opened AbstractEvalProof
  import opened helpers

  datatype AbstractPathState = AbstractPathState(state: AbstractState, pc: nat, branch_pcs: seq<nat>)

  // Expected to satisfy stmt_step(path[i].state, path[i].pc) ~> (path[i + 1].state)
  datatype AbstractPath = AbstractPath(path: seq<AbstractPathState>)
  datatype AnalysisResult = AnalysisResult(paths: seq<AbstractPath>)

  datatype VerifierState = VerifierState(insn_idx: nat)
  datatype VerifierWorkElem = VerifierWorkElem(prev_inst_idx: nat, inst_idx: nat, verifier_state: AbstractPathState, path: AbstractPath)

  datatype InstructionType = BranchInstruction | FunctionExit

  function init_abs_reg_state(r: Reg): Val {
    //TODO: Maybe this should be (0, U64_MAX)
    //TODO: All registers are unconstrained
    Interval(0, U64_MAX as int)
  }

  function initial_abstract_state(stmt: Stmt): AbstractPathState {
    AbstractPathState(AbstractState(init_abs_reg_state), 0, [])
  }

  function push_stack(stack: seq<AbstractPathState>, new_state: AbstractPathState): seq<AbstractPathState> {
    stack + [new_state]
  }

  predicate reg_included(c_v: u32, v: Val) {
    v.lo <= c_v as int <= v.hi
  }

  predicate state_included(env: E.State, abs: AbstractState) {
    forall r: Reg :: reg_included(env(r), abs.rs(r))
  }

  predicate programWellFormed(prog: Program) {
    true
  }

  function pushAbstractPath(absPath: AbstractPath, state: AbstractPathState) : AbstractPath {
    AbstractPath(absPath.path + [state])
  }

  predicate program_path_branch_free(prog: Program, pc: nat, length: nat) {
    forall pc' :: pc <= pc' < pc + length ==> !is_branch_instruction(prog, pc')
  }

  predicate abstract_path_branch_free(prog: Program, path: AbstractPath) {
    forall idx :: 0 <= idx < |path.path| ==> !is_branch_instruction(prog, path.path[idx].pc)
  }

  lemma exploreTillBranchOrExit_pc_ok(prog: Program, pc: nat, abs_state: AbstractState)
    requires |prog.stmts| > 0
    requires pc <= |prog.stmts|
    requires programWellFormed(prog)
    requires has_valid_jump_targets(prog.stmts, 0)

    ensures forall p: ConcretePath :: is_basic_block_fragment(prog, p) && state_included(p.path[0].state, abs_state) ==> 
      |exploreTillBranchOrExit(prog, p.path[0].pc, abs_state).0.path| == |p.path|
  {
    assert forall p: ConcretePath :: is_basic_block_fragment(prog, p) && state_included(p.path[0].state, abs_state) ==> 
      |exploreTillBranchOrExit(prog, p.path[0].pc, abs_state).0.path| > 0;
    assert forall p: ConcretePath :: is_basic_block_fragment(prog, p) && state_included(p.path[0].state, abs_state) ==> 
      exploreTillBranchOrExit(prog, p.path[0].pc, abs_state).0.path[0].pc == p.path[0].pc;
  }

  // Returns the path along with whether the last instructucion was a branch or an exit
  function exploreTillBranchOrExit(prog: Program, pc: nat, abs_state: AbstractState) : (r : (AbstractPath, InstructionType))
    requires |prog.stmts| > 0
    requires pc <= |prog.stmts|
    requires programWellFormed(prog)
    requires has_valid_jump_targets(prog.stmts, 0)

    // Make sure that we stay within bounds of the program
    ensures pc_in_bounds(prog, pc) ==> pc_offset_in_bounds_or_at_end(prog, pc, |r.0.path|)
    ensures (forall idx :: in_bounds_path(idx, r.0.path) ==> r.0.path[idx].pc == pc + idx)

    // Make sure that instruction following the path is a branch instruction and everything in between is not a branch
    ensures pc_offset_in_bounds(prog, pc, |r.0.path|) ==>
              is_branch_instruction(prog, pc + |r.0.path|) &&
              r.1.BranchInstruction? &&
              program_path_branch_free(prog, pc, |r.0.path|) &&
              abstract_path_branch_free(prog, r.0)

    // Make sure that we return a FunctionExit on an actual function exit and everything in between is not a branch
    ensures pc_at_end(prog, pc + |r.0.path|) ==>
              r.1.FunctionExit? && 
              program_path_branch_free(prog, pc, |r.0.path|) &&
              abstract_path_branch_free(prog, r.0)

    decreases |prog.stmts| - pc
  {
    var empty_path : AbstractPath := AbstractPath([]);

    if pc == |prog.stmts| then
      (empty_path, FunctionExit)
    else

      var cur_inst := prog.stmts[pc];

      match cur_inst {
        case JmpZero(_, _) => (empty_path, BranchInstruction)
        case Assign(r, e) =>
  
          var new_state := AbstractEval.stmt_eval(abs_state, cur_inst);
          
          //assert forall conc_state: E.State :: state_included(conc_state, abs_state) ==> state_included(conc_state, new_state);

          assert pc < |prog.stmts|;
          assert new_state.1 == {1};

          var path_state := AbstractPathState(new_state.0, pc, []);

          var rest_of_path := exploreTillBranchOrExit(prog, pc + 1, new_state.0);
          (AbstractPath([path_state] + rest_of_path.0.path), rest_of_path.1)
      }


    //ret
  }

  function concatPaths(path1: AbstractPath, path2: AbstractPath) : AbstractPath {
    AbstractPath(path1.path + path2.path)
  }

  // Prove Theorem 1.5:
  predicate isBranchInstruction(stmt: Stmt) {
    stmt.JmpZero?
  }


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
  // Theorem 1.1: All the elements on the worklist, represent an abstract path fragment (A) ending at a branching instruction or exit
  // Theorem 1.2: All the elements on the worklist, represent an abstract path fragment (A) such that the pc values traced out by A respects
  // the possible pc values given by verifierExploreConcretePath for any concrete path defined by an initial concrete state C contained in the initial abstract state
  // Theorem 1.3: The loop body adds the abstract path to the AnalysisResult on a function exit
  // Theorem 1.3: The loop body enqueues both the possible branch outcomes on the worklist
  // Theorem 1.4: The loop body extends the abstract path on the top of the stack by a basic block defined by exploreTillBranchOrExit
  // Theorem 1.5: exploreTillBranchOrExit respects the program pc values in a basic block defined by verifierExploreConcretePath

  // Theorem 1.6: Each explored path is included in the AnalysisResult
  // Theorem 1.7: The worklist contains the prefixes of all unexplored paths in the program at any iteration
  // Thorem 1.8: The paths in the worklist and the unexplored paths in the worklist together consitute all the reachable paths in the program

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

      fuel := fuel - |path.0.path| - 1;
    }

    return ret;
  }

}
