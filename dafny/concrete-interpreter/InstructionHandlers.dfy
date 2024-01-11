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
                                          offset: int16,
                                          imm: int32,
                                          env: Environment): Option<Environment>
    {
        var source_operand: int64 :- match source {
            // TODO ensure casting is correct here ?
            case BPF_K => Some(castInt32ToInt64(imm))
            // TODO: Can I do a midway return here ?
            case BPF_X => match src_reg {
                case None => None // return error
                case Some(reg) => Some(getRegValue(reg, env.1))
            }
        };
        
        // operands tuple (dest, source)
        var operands: (int, int) :- match cls {
            case BPF_ALU64 => (
                // TODO No need of casting here
                match dest_reg {
                    case None => None
                    case Some(reg) => Some((getRegValue(reg, env.1) as int,
                                            source_operand as int))
                }
            )
            case BPF_ALU => (
                // TODO casting here to int32 and
                // finally reading it into int
                match dest_reg {
                    case None => None
                    case Some(reg) => Some((castInt64ToInt32(getRegValue(reg, env.1)) as int,
                                            castInt64ToInt32(source_operand) as int))
                }
            )
        };

        match opcode {
            case BPF_ADD => (
                // TODO BPF_ADD
                match dest_reg {
                    case None => None
                    case Some(reg) => (
                        var updated_register_map: RegisterMap := match cls {
                            case BPF_ALU64 => (
                                updateRegValue(reg,
                                               castIntToInt64(operands.0 + operands.1),
                                               env.1)
                            )
                            case BPF_ALU => (
                                updateRegValue(reg,
                                               castInt32ToInt64(castIntToInt32(operands.0 + operands.1)),
                                               env.1)
                            )
                        };
                        Some((env.0, updated_register_map))
                    )
                }
            )
            case BPF_SUB => (
                // TODO BPF_SUB
                Some(env)
            )
            case BPF_MUL => (
                // TODO BPF_MUL
                Some(env)
            )
            case BPF_DIV => (
                // TODO BPF_DIV
                Some(env)
            )
            case BPF_SDIV => (
                // TODO BPF_SDIV
                Some(env)
            )
            case BPF_OR => (
                // TODO BPF_OR
                Some(env)
            )
            case BPF_AND => (
                // TODO BPF_AND
                Some(env)
            )
            case BPF_LSH => (
                // TODO BPF_LSH
                Some(env)
            )
            case BPF_RSH => (
                // TODO BPF_RSH
                Some(env)
            )
            case BPF_NEG => (
                // TODO BPF_NEG
                Some(env)
            )
            case BPF_MOD => (
                // TODO BPF_MOD
                Some(env)
            )
            case BPF_SMOD => (
                // TODO BPF_SMOD
                Some(env)
            )
            case BPF_XOR => (
                // TODO BPF_XOR
                Some(env)
            )
            case BPF_MOV => (
                // TODO BPF_MOV
                match dest_reg {
                    case None => None
                    case Some(reg) => (
                        var updated_register_map: RegisterMap := updateRegValue(reg,
                                                                                operands.1 as RegisterValue,
                                                                                env.1);
                        Some((env.0, updated_register_map))
                    )
                }
            )
            case BPF_MOVSX => (
                // TODO BPF_MOVSX
                Some(env)
            )
            case BPF_ARSH => (
                // TODO BPF_ARSH
                Some(env)
            )
        }
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
                                    offset: int16,
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
                                    offset: int16,
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
                                     offset: int16,
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
                                          offset: int16,
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
                                      offset: int16,
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
                                           offset: int16,
                                           imm: int32,
                                           next_imm: int32,
                                           env: Environment): Option<Environment>
    {
        Some(env)
    }

}