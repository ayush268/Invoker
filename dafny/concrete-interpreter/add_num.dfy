// Simplified verison of ebpf-setup/src/add_example.c

/*
0000000000000000 <ebpf_add_example>:
       0:	b7 00 00 00 01 00 00 00	r0 = 1
       1:	07 00 00 00 02 00 00 00	r0 += 0x2
       2:	95 00 00 00 00 00 00 00	exit
*/

include "Types.dfy"
include "Execution.dfy"

module add_example {
  import opened Types
  import opened Execution

  // Interesting insight -> having the same name of the function as the module results in error
  // while compilation
  function add_example_program(): BPFProgram {
    var statement00Op: OpCode := ArithmeticOperation(ArithmeticOpCode.BPF_MOV, ArithmeticSource.BPF_K, ArithmeticInstructionClass.BPF_ALU64);
    var statement00: Statement := Instruction(statement00Op, None, Some(Register.R0), 0x0, 0x01);

    var statement01Op: OpCode := ArithmeticOperation(ArithmeticOpCode.BPF_ADD, ArithmeticSource.BPF_K, ArithmeticInstructionClass.BPF_ALU64);
    var statement01: Statement := Instruction(statement01Op, None, Some(Register.R0), 0x0, 0x2);

    var statement02Op: OpCode := JumpOperation(JumpOpCode.BPF_EXIT, JumpSource.BPF_K, JumpInstructionClass.BPF_JMP);
    var statement02 : Statement := Instruction(statement02Op, None, None, 0x0, 0x0);

    var stmt_seq: seq<Statement> := [statement00, statement01, statement02];

    Statements(stmt_seq)
  }

  /*function test_example(): bool {
    var program: BPFProgram := add_example_program();
    assert(|program.inst| == 3);
    true
  }*/

  method Main() {
    var example_prog: BPFProgram := add_example_program();
    print |example_prog.inst|, "\n";
    var res := executeProgram(example_prog);
    match res {
      case Ok(r) => print r;
      case NoFuel => print "Ran out of fuel";
      case Error(c, msg) => print "Error: ", msg;
    }
  }
}