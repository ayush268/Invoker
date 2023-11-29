include "BoundedInts.dfy"
include "Types.dfy"

// This module will be fully pure with zero side-effects
// The only changes would be to the returned state

// Have to ensure that for a certain input the output always remains
// the same i.e. the purity (or consistency) is upheld
module Execution {
    import opened BoundedInts
    import opened Types

    function executeProgram(prog: BPFProgram): ExecResult<Environment>
        // TODO: add any constraints as needed
    {
        match prog {
            case Statements(s) => executeStatement(s, (map[], map[]), 1)
            case _ => Some(map[], map[])
        }
    }

    // TODO: complete the function
    function executeStatement(prog: seq<Statement>, env: Environment, mem: Memory, pc: nat, fuel: nat): ExecResult<Environment>
        requires pc <= |prog|
        decreases fuel
    {
        if fuel == 0 then NoFuel
        else if pc == |prog| then Some(env)
        else {
            match prog[0] {
                case Instruction(op, src_reg, dest_reg, offset, imm) => {
                    match op {
                        case ArithmeticOperation(opcode, source, cls) => {
                            match opcode {
                                case BPF_ADD => {

                                }
                                case BPF_SUB => {

                                }
                                case BPF_MUL => {

                                }
                            }
                        }
                    }
                }
                case Instruction128(op, src_reg, dest_reg, offset, imm64) => {

                }
            }
        }
    }
}