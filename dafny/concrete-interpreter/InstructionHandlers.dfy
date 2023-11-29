include "BoundedInts.dfy"
include "Types.dfy"

module InstructionHandlers {
    import opened BoundedInts
    import opened Types

    function handleArithmeticInstructions(opcode: ArithmeticOpCode,
                                          source: ArithmeticSource,
                                          inst_class: ArithmeticInstructionClass,
                                          src_reg: Option<Register>,
                                          dest_reg: Option<Register>,
                                          offest: int16,
                                          imm: int32): ExecResult<>
}