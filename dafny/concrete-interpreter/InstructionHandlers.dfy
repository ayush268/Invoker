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
        requires !dest_reg.IsFailure() && // the dest register can't be null
                 (source == ArithmeticSource.BPF_X && !src_reg.IsFailure()) // if source is BPF_X then source register can't be null
    {
        var source_operand: int64 :- match source {
            // TODO ensure casting is correct here ?
            case BPF_K => Some(castInt32ToInt64(imm))
            case BPF_X => Some(getRegValue(src_reg.Extract(), env.1))
        };

        // operands tuple (dest, source)
        var operands: (int, int) :- match cls {
            case BPF_ALU64 =>
                // TODO No need of casting here
                Some((getRegValue(dest_reg.Extract(), env.1) as int, source_operand as int))
            case BPF_ALU =>
                // TODO casting here to int32 and
                // finally reading it into int
                Some((castInt64ToInt32(getRegValue(dest_reg.Extract(), env.1)) as int,
                      castInt64ToInt32(source_operand) as int))
        };

        match opcode {
            case BPF_ADD => (
                var updated_register_map: RegisterMap := match cls {
                    case BPF_ALU64 => updateRegValue(dest_reg.Extract(),
                                                     castIntToInt64(operands.0 + operands.1),
                                                     env.1)
                    case BPF_ALU => updateRegValue(dest_reg.Extract(),
                                                   castInt32ToInt64(castIntToInt32(operands.0 + operands.1)),
                                                   env.1)
                };
                Some((env.0, updated_register_map))
            )
            case BPF_SUB => (
                // TODO BPF_SUB, check if underflows/overflows are handled correctly
                var updated_register_map: RegisterMap := match cls {
                    case BPF_ALU64 => updateRegValue(dest_reg.Extract(),
                                                     castIntToInt64(operands.0 - operands.1),
                                                     env.1)
                    case BPF_ALU => updateRegValue(dest_reg.Extract(),
                                                   castInt32ToInt64(castIntToInt32(operands.0 - operands.1)),
                                                   env.1)
                };
                Some((env.0, updated_register_map))
            )
            case BPF_MUL => (
                // TODO BPF_MUL, check if overflows are handled correctly
                var updated_register_map: RegisterMap := match cls {
                    case BPF_ALU64 => updateRegValue(dest_reg.Extract(),
                                                     castIntToInt64(operands.0 * operands.1),
                                                     env.1)
                    case BPF_ALU => updateRegValue(dest_reg.Extract(),
                                                   castInt32ToInt64(castIntToInt32(operands.0 * operands.1)),
                                                   env.1)
                };
                Some((env.0, updated_register_map))
            )
            case BPF_DIV => (
                // TODO BPF_DIV, check if underflows are handled correctly
                // if operands.1 (src == 0) then 0; case of division by zero
                var result: int := if operands.1 == 0 then 0
                                   else operands.0 / operands.1;
                var updated_register_map: RegisterMap := match cls {
                    case BPF_ALU64 => updateRegValue(dest_reg.Extract(),
                                                     castIntToInt64(result),
                                                     env.1)
                    case BPF_ALU => updateRegValue(dest_reg.Extract(),
                                                   castInt32ToInt64(castIntToInt32(result)),
                                                   env.1)
                };
                Some((env.0, updated_register_map))
            )
            case BPF_SDIV => (
                // TODO BPF_SDIV, is this operation present anymore?
                None
            )
            case BPF_OR => (
                // TODO BPF_OR, assuming this to be bitwise OR
                var updated_register_map: RegisterMap := match cls {
                    case BPF_ALU64 => updateRegValue(dest_reg.Extract(),
                                                     castIntToInt64(bitwiseOrOperation(operands.0, operands.1, 64)),
                                                     env.1)
                    case BPF_ALU => updateRegValue(dest_reg.Extract(),
                                                   castInt32ToInt64(castIntToInt32(bitwiseOrOperation(operands.0, operands.1, 32))),
                                                   env.1)
                };
                Some((env.0, updated_register_map))
            )
            case BPF_AND => (
                // TODO BPF_AND, assuming this to be bitwise AND
                var updated_register_map: RegisterMap := match cls {
                    case BPF_ALU64 => updateRegValue(dest_reg.Extract(),
                                                     castIntToInt64(bitwiseAndOperation(operands.0, operands.1, 64)),
                                                     env.1)
                    case BPF_ALU => updateRegValue(dest_reg.Extract(),
                                                   castInt32ToInt64(castIntToInt32(bitwiseAndOperation(operands.0, operands.1, 32))),
                                                   env.1)
                };
                Some((env.0, updated_register_map))
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
                // TODO BPF_NEG, assuming this to be bitwise NEG
                var updated_register_map: RegisterMap := match cls {
                    case BPF_ALU64 => updateRegValue(dest_reg.Extract(),
                                                     castIntToInt64(bitwiseNegOperation(operands.1, 64)),
                                                     env.1)
                    case BPF_ALU => updateRegValue(dest_reg.Extract(),
                                                   castInt32ToInt64(castIntToInt32(bitwiseNegOperation(operands.1, 32))),
                                                   env.1)
                };
                Some((env.0, updated_register_map))
            )
            case BPF_MOD => (
                // TODO BPF_MOD, check if underflows are handled correctly
                // if operands.1 (src == 0) then dest; case of division by zero
                var result: int := if operands.1 == 0 then operands.0
                                   else operands.0 % operands.1;
                var updated_register_map: RegisterMap := match cls {
                    case BPF_ALU64 => updateRegValue(dest_reg.Extract(),
                                                     castIntToInt64(result),
                                                     env.1)
                    case BPF_ALU => updateRegValue(dest_reg.Extract(),
                                                   castInt32ToInt64(castIntToInt32(result)),
                                                   env.1)
                };
                Some((env.0, updated_register_map))
            )
            case BPF_SMOD => (
                // TODO BPF_SMOD, is this operation present anymore ?
                Some(env)
            )
            case BPF_XOR => (
                // TODO BPF_XOR, assuming this to be bitwise XOR
                var updated_register_map: RegisterMap := match cls {
                    case BPF_ALU64 => updateRegValue(dest_reg.Extract(),
                                                     castIntToInt64(bitwiseXorOperation(operands.0, operands.1, 64)),
                                                     env.1)
                    case BPF_ALU => updateRegValue(dest_reg.Extract(),
                                                   castInt32ToInt64(castIntToInt32(bitwiseXorOperation(operands.0, operands.1, 32))),
                                                   env.1)
                };
                Some((env.0, updated_register_map))
            )
            case BPF_MOV => (
                var updated_register_map: RegisterMap := updateRegValue(dest_reg.Extract(),
                                                                        operands.1 as RegisterValue,
                                                                        env.1);
                Some((env.0, updated_register_map))
            )
            case BPF_MOVSX => (
                // TODO BPF_MOVSX, is this operation present anymore ?
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

    // Return values -> (Update Environment, Updated Memory, Update Program Counter)
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
        // TODO complete
        match opcode {
            case BPF_JA => (
                // TODO BPF_JA
                Some((env, mem, 1))   
            )
            case BPF_JEQ => (
                // TODO BPF_JEQ
                Some((env, mem, 1))
            )
            case BPF_JGT => (
                // TODO BPF_JGT
                Some((env, mem, 1))
            )
            case BPF_JGE => (
                // TODO BPF_JGE
                Some((env, mem, 1))
            )
            case BPF_JSET => (
                // TODO BPF_JSET
                Some((env, mem, 1))
            )
            case BPF_JNE => (
                // TODO BPF_JNE
                Some((env, mem, 1))
            )
            case BPF_JSGT => (
                // TODO BPF_JSGT
                Some((env, mem, 1))
            )
            case BPF_JSGE => (
                // TODO BPF_JSGE
                Some((env, mem, 1))
            )
            case BPF_CALL => (
                // TODO BPF_CALL
                Some((env, mem, 1))
            )
            case BPF_EXIT => (
                // TODO BPF_EXIT
                Some((env, mem, 1))
            )
            case BPF_JLT => (
                // TODO BPF_JLT
                Some((env, mem, 1))
            )
            case BPF_JLE => (
                // TODO BPF_JLE
                Some((env, mem, 1))
            )
            case BPF_JSLT => (
                // TODO BPF_JSLT
                Some((env, mem, 1))
            )
            case BPF_JSLE => (
                // TODO BPF_JSLE
                Some((env, mem, 1))
            )
        }
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