// Dafny version of ebpf-setup/src/kern.c

/*
Disassembly of section tracepoint/syscalls/sys_enter_kill:

0000000000000000 <ebpf_kill_example>:
       0:	79 11 18 00 00 00 00 00	r1 = *(u64 *)(r1 + 0x18)
       1:	55 01 0c 00 09 00 00 00	if r1 != 0x9 goto +0xc <LBB0_2>
       2:	b7 01 00 00 30 0a 00 00	r1 = 0xa30
       3:	7b 1a f8 ff 00 00 00 00	*(u64 *)(r10 - 0x8) = r1
       4:	b7 01 00 00 01 00 00 00	r1 = 0x1
       5:	63 1a f4 ff 00 00 00 00	*(u32 *)(r10 - 0xc) = r1
       6:	bf a2 00 00 00 00 00 00	r2 = r10
       7:	07 02 00 00 f8 ff ff ff	r2 += -0x8
       8:	bf a3 00 00 00 00 00 00	r3 = r10
       9:	07 03 00 00 f4 ff ff ff	r3 += -0xc
      10:	18 01 00 00 00 00 00 00 00 00 00 00 00 00 00 00	r1 = 0x0 ll
      12:	b7 04 00 00 01 00 00 00	r4 = 0x1
      13:	85 00 00 00 02 00 00 00	call 0x2

0000000000000070 <LBB0_2>:
      14:	b7 00 00 00 00 00 00 00	r0 = 0x0
      15:	95 00 00 00 00 00 00 00	exit
*/
module kill_example {
  import opened parser

  function kill_example(): BPFProgram {

    var statement00Op: Op := LoadOperation(LoadInstructionClass.BPF_LDX, LoadSize.BPF_DW, LoadMode.BPF_MEM);
    var statement00 : Statement := Instruction(statement00Op, RegisterOrUnused.R1, RegisterOrUnused.R1, 0x18, 0x0);

    var statement01Op: Op := JumpOperation(JumpInstructionClass.BPF_JMP, JumpSource.BPF_K, JumpOpCode.BPF_JNE);
    var statement01: Statement := Instruction(statement01Op, RegisterOrUnused.UNUSED, RegisterOrUnused.R1, 0xc, 0x9);

    var statement02Op: Op := ArithmeticOperation(ArithmeticInstructionClass.BPF_ALU64, ArithmeticSource.BPF_K, ArithmeticOpCode.BPF_MOV);
    var statement02: Statement := Instruction(statement02Op, RegisterOrUnused.UNUSED, RegisterOrUnused.R1, 0x0, 0xa30);

    var statement03Op: Op := StoreOperation(StoreInstructionClass.BPF_STX, StoreSize.BPF_DW, StoreMode.BPF_MEM);
    var statement03 : Statement := Instruction(statement03Op, RegisterOrUnused.R1, RegisterOrUnused.R10, -0x8, 0x0);

    var statement04Op: Op := ArithmeticOperation(ArithmeticInstructionClass.BPF_ALU64, ArithmeticSource.BPF_K, ArithmeticOpCode.BPF_MOV);
    var statement04: Statement := Instruction(statement04Op, RegisterOrUnused.UNUSED, RegisterOrUnused.R1, 0x0, 0x1);

    var statement05Op: Op := StoreOperation(StoreInstructionClass.BPF_STX, StoreSize.BPF_W, StoreMode.BPF_MEM);
    var statement05 : Statement := Instruction(statement05Op, RegisterOrUnused.R1, RegisterOrUnused.R10, -0xc, 0x0);

    var statement06Op: Op := ArithmeticOperation(ArithmeticInstructionClass.BPF_ALU64, ArithmeticSource.BPF_X, ArithmeticOpCode.BPF_MOV);
    var statement06 : Statement := Instruction(statement06Op, RegisterOrUnused.R10, RegisterOrUnused.R2, 0x0, 0x0);

    var statement07Op: Op := ArithmeticOperation(ArithmeticInstructionClass.BPF_ALU64, ArithmeticSource.BPF_K, ArithmeticOpCode.BPF_ADD);
    var statement07: Statement := Instruction(statement07Op, RegisterOrUnused.UNUSED, RegisterOrUnused.R2, 0x0, -0x8);

    var statement08Op: Op := ArithmeticOperation(ArithmeticInstructionClass.BPF_ALU64, ArithmeticSource.BPF_X, ArithmeticOpCode.BPF_MOV);
    var statement08 : Statement := Instruction(statement08Op, RegisterOrUnused.R10, RegisterOrUnused.R3, 0x0, 0x0);

    var statement09Op: Op := ArithmeticOperation(ArithmeticInstructionClass.BPF_ALU64, ArithmeticSource.BPF_K, ArithmeticOpCode.BPF_ADD);
    var statement09: Statement := Instruction(statement09Op, RegisterOrUnused.UNUSED, RegisterOrUnused.R3, 0x0, -0xc);

    var statement10Op: Op := Immediate64Operation(Immediate64InstructionClass.BPF_LD, Immediate64Size.BPF_DW, Immediate64Mode.BPF_IMM, Immediate64Type.IMM64);
    var statement10: Statement := Instruction(statement10Op, RegisterOrUnused.R0, RegisterOrUnused.R1, 0x0, 0x0);

    var statement11: Statement := Immediate32(0x0);

    var statement12Op: Op := ArithmeticOperation(ArithmeticInstructionClass.BPF_ALU64, ArithmeticSource.BPF_K, ArithmeticOpCode.BPF_MOV);
    var statement12: Statement := Instruction(statement12Op, RegisterOrUnused.UNUSED, RegisterOrUnused.R4, 0x0, 0x1);

    var statement13Op: Op := JumpOperation(JumpInstructionClass.BPF_JMP, JumpSource.BPF_K, JumpOpCode.BPF_CALL);
    var statement13: Statement := Instruction(statement13Op, RegisterOrUnused.UNUSED, RegisterOrUnused.UNUSED, 0x0, 0x2);

    var statement14Op: Op := ArithmeticOperation(ArithmeticInstructionClass.BPF_ALU64, ArithmeticSource.BPF_K, ArithmeticOpCode.BPF_MOV);
    var statement14: Statement := Instruction(statement14Op, RegisterOrUnused.UNUSED, RegisterOrUnused.R0, 0x0, 0x0);

    var statement15Op: Op := JumpOperation(JumpInstructionClass.BPF_JMP, JumpSource.BPF_K, JumpOpCode.BPF_EXIT);
    var statement15 : Statement := Instruction(statement15Op, RegisterOrUnused.UNUSED, RegisterOrUnused.UNUSED, 0x0, 0x0);

    var stmt_seq: seq<Statement> := [statement00, statement01, statement02, statement03, statement04, statement05, statement05, statement06, statement07,
                                     statement08, statement09, statement10, statement11, statement12, statement13, statement14, statement15];
    var prog : BPFProgram := Statements(stmt_seq);
    prog
  }

}