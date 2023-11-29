include "BoundedInts.dfy"
include "Types.dfy"

module InstructionHandlers {
    import opened BoundedInts
    import opened Types

    function handleArithmeticInstructions(opcode: ArithmeticOpCode,
                                          source: ArithmeticSource,
                                          cls: ArithmeticInstructionClass,
                                          src_reg: Option<Register>,
                                          dest_reg: Option<Register>,
                                          offest: int16,
                                          imm: int32,
                                          env: Environment): Option<Environment>
    {
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