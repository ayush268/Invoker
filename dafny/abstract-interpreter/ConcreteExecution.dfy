include "SimpleVerifier.dfy"
include "helpers.dfy"

module ConcreteExecution {
    import opened Lang
    import opened ConcreteEval
    import opened Ints
    import opened helpers

    datatype PathState = PathState(state: ConcreteEval.State, pc: nat)

    datatype ConcretePath = ConcretePath(path: seq<PathState>)

    function init_conc_reg_state(r: Reg): u32 {
        0
    }

    function initial_concrete_state(stmt: Stmt): PathState {
        PathState(init_conc_reg_state, 0)
    }

    predicate state_equal(s1: ConcreteEval.State, s2: ConcreteEval.State) {
        forall r : Reg :: s1(r) == s2(r)
    }

    predicate stmt_step_valid(prog: Program, initial_state: PathState, final_state: PathState)
    {
        var init_pc := initial_state.pc;
        var final_pc := final_state.pc;

        if pc_at_end(prog, init_pc) then
            // Check whether we stay at the same state
            pc_at_end(prog, final_pc) && 
                state_equal(initial_state.state, final_state.state)
        else if pc_in_bounds(prog, init_pc) then
            var stmt := prog.stmts[init_pc];
            match ConcreteEval.stmt_step(initial_state.state, stmt) {
                case Some((fin, offset)) =>
                    (init_pc + offset == final_pc) && 
                        state_equal(fin, final_state.state) &&
                        pc_in_bounds_or_at_end(prog, final_pc)
                case None => false
            }
        else
            // !pc_in_bounds(prog, init_pc) && !(pc_at_end(prog, pc))
            // pc points to space
            false
    }

    predicate is_valid_path(prog: Program, path: ConcretePath) {
        if |path.path| == 0 then
            true
        else if |path.path| == 1 then
            pc_in_bounds_or_at_end(prog, path.path[0].pc)
        else
            stmt_step_valid(prog, path.path[0], path.path[1]) && 
                is_valid_path(prog, ConcretePath(path.path[1..]))
    }

    predicate concrete_path_branch_free(prog: Program, path: ConcretePath) {
        forall idx :: 0 <= idx < |path.path| ==> !is_branch_instruction(prog, path.path[idx].pc)
    }

    predicate is_basic_block_fragment(prog: Program, path: ConcretePath) {
        |path.path| > 0 &&
        is_valid_path(prog, path) && 
        pc_in_bounds(prog, path.path[0].pc) &&
        !is_branch_instruction(prog, path.path[0].pc) &&
        concrete_path_branch_free(prog, path) &&
        (   pc_at_end(prog, path.path[|path.path| - 1].pc + 1)  ||
            (   pc_in_bounds(prog, path.path[|path.path| - 1].pc + 1) &&
                is_branch_instruction(prog, path.path[|path.path| - 1].pc + 1)  )
        )
    }
}