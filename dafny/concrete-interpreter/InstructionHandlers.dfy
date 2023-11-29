include "BoundedInts.dfy"
include "Types.dfy"
include "Helpers.dfy"

module InstructionHandlers {
    import opened BoundedInts
    import opened Types
    import opened Helpers

    function handleArithmeticInstructions(opcode: ArithmeticOpCode,
                                          source: ArithmeticSource,
                                          cls: ArithmeticInstructionClass,
                                          src_reg: Option<Register>,
                                          dest_reg: Option<Register>,
                                          offest: int16,
                                          imm: int32,
                                          env: Environment): Option<Environment>
    {
        var source_operand: int64 :- match source {
            // TODO Can we do type casting here ?
            case BPF_K => Some(imm as int64)
            // TODO: Can I do a midway return here ???
            case BPF_X => match src_reg {
                case None => None // return error
                case Some(reg) => Some(getRegValue(reg, env.1))
            }
        };
        
        // operands tuple (dest, source)
        /*var operands: (int, int) := match cls {
            case BPF_ALU64 => (
                // TODO casting here
                (match dest_reg {
                    case None => 0
                    case Some(reg) => getRegValue(reg, env.1)
                },
                source_operand)
            )
            case BPF_ALU => (
                // TODO casting here to int32
                (match dest_reg {
                    case None => 0
                    case Some(reg) => getRegValue(reg, env.1)
                },
                source_operand)
            )
        };*/

        Some(env)
    }

    function handleByteSwapInstructions(opcode: ByteSwapOpCode,
                                        source: ByteSwapSource,
                                        cls: ByteSwapInstructionClass,
                                        dest_reg: Option<Register>,
                                        imm: int32,
                                        env: Environment): Option<Environment>
    {
        Some(env)
    }

    function handleJumpInstructions(opcode: JumpOpCode,
                                    source: JumpSource,
                                    cls: JumpInstructionClass,
                                    src_reg: Option<Register>,
                                    dest_reg: Option<Register>,
                                    offest: int16,
                                    imm: int32,
                                    env: Environment,
                                    mem: MemoryList): Option<(Environment, MemoryList, int)>
    {
        Some((env, mem, 1))
    }

    function handleLoadInstructions(mode: LoadMode,
                                    size: LoadSize,
                                    cls: LoadInstructionClass,
                                    src_reg: Option<Register>,
                                    dest_reg: Option<Register>,
                                    offest: int16,
                                    imm: int32,
                                    env: Environment): Option<Environment>
    {
        Some(env)
    }

    function handleStoreInstructions(mode: StoreMode,
                                     size: StoreSize,
                                     cls: StoreInstructionClass,
                                     src_reg: Option<Register>,
                                     dest_reg: Option<Register>,
                                     offest: int16,
                                     imm: int32,
                                     env: Environment,
                                     mem: MemoryList): Option<(Environment, MemoryList)>
    {
        Some((env, mem))
    }

    function handleSignedLoadInstructions(mode: SignedLoadMode,
                                          size: SignedLoadSize,
                                          cls: SignedLoadInstructionClass,
                                          src_reg: Option<Register>,
                                          dest_reg: Option<Register>,
                                          offest: int16,
                                          imm: int32,
                                          env: Environment): Option<Environment>
    {
        Some(env)
    }

    function handleAtomicInstructions(mode: AtomicMode,
                                      size: AtomicSize,
                                      cls: AtomicInstructionClass,
                                      src_reg: Option<Register>,
                                      dest_reg: Option<Register>,
                                      offest: int16,
                                      imm: int32,
                                      env: Environment,
                                      mem: MemoryList): Option<(Environment, MemoryList)>
    {
        Some((env, mem))
    }

    function handleImmediate64Instructions(mode: Immediate64Mode,
                                           size: Immediate64Size,
                                           cls: Immediate64InstructionClass,
                                           src_reg: Option<Register>,
                                           dest_reg: Option<Register>,
                                           offest: int16,
                                           imm: int32,
                                           next_imm: int32,
                                           env: Environment): Option<Environment>
    {
        Some(env)
    }

}