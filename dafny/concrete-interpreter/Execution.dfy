include "BoundedInts.dfy"
include "Types.dfy"

// This module will be fully pure with zero side-effects
// The only changes would be to the returned state

// Have to ensure that for a certain input the output always remains
// the same i.e. the purity (or consistency) is upheld
module Execution {
    import opened BoundedInts
    import opened Types

    function executeProgram(prog: BPFProgram): Environment {
        match prog {
            case Statements(s) => executeStatement(s, (map[], map[]), 1)
            case _ => (map[], map[])
        }
    }

    function executeStatement(prog: seq<Statement>, env: Environment, mem: Memory): Environment {
        // TODO
        if |prog| == 0 then {   
            env
        } else {
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