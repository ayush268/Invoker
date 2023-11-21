// Simplified verison of ebpf-setup/src/add_example.c

/*
0000000000000000 <ebpf_add_example>:
       0:	b7 00 00 00 01 00 00 00	r0 = 1
       1:	07 00 00 00 02 00 00 00	r0 += 0x2
       2:	95 00 00 00 00 00 00 00	exit
*/

module add_example {
    import opened parser

    function add_example(): BPFProgram {
        var statement00Op: Op := ArithmeticOperation(ArithmeticInstructionClass.BPF_ALU64, ArithmeticSource.BPF_K, ArithmeticOpCode.BPF_MOV);
        var statement00: Statement := Instruction(statement00Op, RegisterOrUnused.UNUSED, RegisterOrUnused.R0, 0x0, 0x01);

        var statement01Op: Op := ArithmeticOperation(ArithmeticInstructionClass.BPF_ALU64, ArithmeticSource.BPF_K, ArithmeticOpCode.BPF_ADD);
        var statement01: Statement := Instruction(statement01Op, RegisterOrUnused.UNUSED, RegisterOrUnused.R0, 0x0, 0x2);

        var statement02Op: Op := JumpOperation(JumpInstructionClass.BPF_JMP, JumpSource.BPF_K, JumpOpCode.BPF_EXIT);
        var statement02 : Statement := Instruction(statement02Op, RegisterOrUnused.UNUSED, RegisterOrUnused.UNUSED, 0x0, 0x0);

        var stmt_seq: seq<Statement> := [statement00, statement01, statement02];

        Statements(stmt_seq)
    }
}