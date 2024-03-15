module AbstractInterpretation {

    datatype CFG<InstructionType> = CFG(nodes: seq<InstructionType>, edges: nat -> seq<nat>)

    opaque function join<T>(state1: T, state2: T) : T 
    {
        state1
    }

    opaque function extend<T, U>(state: T, instruction: U) : T {
        state
    }
}