include "SimpleVerifier.dfy"

module SimpleVerifierAnalysis {
    import opened Lang
    import opened E = ConcreteEval
    import opened AbstractEval

    datatype PathState = PathState(state: E.State, pc: int)

    datatype AbstractPathState = AbstractPathState(state: AbstractState, pc: int, branch_pcs: seq<int>)

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
    predicate path_valid(prog: Program, path_states: seq<PathState>) {
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

    function init_abs_reg_state(r: Reg): Val {
        //TODO: Maybe this should be (0, U64_MAX)
        Interval(0, 0)
    }

    function initial_abstract_state(stmt: Stmt): AbstractPathState {
        AbstractPathState(AbstractState(init_abs_reg_state), 0, [])
    }

    function push_stack(stack: seq<AbstractPathState>, new_state: AbstractPathState): seq<AbstractPathState> {
        stack + [new_state]
    }

    function backtrack_stack(stack: seq<AbstractPathState>): seq<AbstractPathState> 
        ensures |backtrack_stack(stack)| > 0 ==> |backtrack_stack(stack)[|backtrack_stack(stack)| - 1].branch_pcs| > 0
    {
        if |stack| == 0 then
            []
        else if |stack[|stack| - 1].branch_pcs| > 0 then
            stack
        else
            backtrack_stack(stack[..|stack| - 1])
    }

    method explore_abstract_paths(prog: Program, fuel: int) 
        requires fuel >= 0
        requires |prog.stmts| > 0
    {
        var stack : seq<AbstractPathState> := [initial_abstract_state(prog.stmts[0])];
        var fuel := fuel;

        while fuel > 0 && |stack| > 0
        {
            // Pop topmost state from the stack
            var cur_state := stack[|stack| - 1];
            var cur_pc := cur_state.pc;
            stack := stack[..|stack| - 1];

            if cur_pc < 0 || cur_pc > |prog.stmts| {
                // We should never encounter this
                break;
            }

            if cur_pc == |prog.stmts| {
                // We hit the end of the subroutine
                // Backtrack till an abstract state with |branch_pcs| > 0 and 
                // explore one of those paths
                stack := backtrack_stack(stack);

                if |stack| > 0 {
                    var last_state := stack[|stack| - 1].state;
                    var last_pc := stack[|stack| - 1].pc;
                    var last_branches := stack[|stack| - 1].branch_pcs;

                    var new_pc := stack[|stack| - 1].branch_pcs[0];

                    var new_branch_state := AbstractPathState(last_state, last_pc, last_branches[1..]);
                    stack := stack[|stack| - 1 := new_branch_state];
                    
                    var new_expl_state := AbstractPathState(last_state, new_pc, []);
                    stack := push_stack(stack, new_expl_state);
                }
                fuel := fuel - 1;
                continue;
            }

            // Continue exploring the path
            var cur_stmt := prog.stmts[cur_state.pc];
            match cur_stmt {
                case Assign(r, e) => {
                    var v := AbstractEval.expr_eval(cur_state.state, e);
                    var new_state := AbstractEval.update_state(cur_state.state, r, v);
                    // We rewrite the branches array when this state is being popped off
                    // Iff it is a branch instruction
                    var new_abs_state := AbstractPathState(new_state, cur_pc + 1, []);
                    stack := push_stack(stack, new_abs_state);
                }

                case JmpZero(r, offset) => {
                    // Copied from AbstractEval.stmt_eval
                    // imprecise analysis: we don't try to prove that this jump is or isn't taken
                    var fall_through := AbstractPathState(cur_state.state, cur_pc + 1, []);
                    var jmp_state := AbstractPathState(cur_state.state, cur_pc, [cur_pc + offset as int]);

                    // Explore the fall_through case with the jmp offset pending in the branch_pcs seq
                    stack := push_stack(push_stack(stack, jmp_state), fall_through);
                }
            }

            fuel := fuel - 1;
        }
    }

    // TODO: Write a method for state space exploration and then reason about the datastructure that is used
    // Each sequence on the stack is a valid path --> need to abstract eval and real eval the path


}