include "SimpleVerifier.dfy"

module AbstractInterpretation {

    import opened AbstractEval
    import opened Lang

    datatype CFG<InstructionType> = CFG(nodes: seq<InstructionType>, edges: nat -> seq<nat>)

    opaque function join(state1: AbstractState, state2: AbstractState) : AbstractState 
    {
        var r0_state1 := state1.rs(R0);
        var r1_state1 := state1.rs(R1);
        var r2_state1 := state1.rs(R2);
        var r3_state1 := state1.rs(R3);

        var r0_state2 := state2.rs(R0);
        var r1_state2 := state2.rs(R1);
        var r2_state2 := state2.rs(R2);
        var r3_state2 := state2.rs(R3);

        state2 
    }

    opaque function extend(state: AbstractState, instruction: Stmt) : AbstractState {
        state
    }
}