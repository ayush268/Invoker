include "BoundedInts.dfy"
include "Types.dfy"
include "InstructionHandlers.dfy"

// This module will be fully pure with zero side-effects
// The only changes would be to the returned state

// Have to ensure that for a certain input the output always remains
// the same i.e. the purity (or consistency) is upheld
module Execution {
    import opened BoundedInts
    import opened Types
    import opened InstructionHandlers

    function executeProgram(prog: BPFProgram): ExecResult<Environment>
        // TODO: add any constraints as needed
    {
        match prog {
            case Statements(s) => executeStatement(s, (map[], map[]), [], 0, 1000)
        }
    }

    // TODO: complete the function
    function executeStatement(prog: seq<Statement>, env: Environment, mem: MemoryList, pc: nat, fuel: nat): ExecResult<Environment>
        requires pc <= |prog| && pc >= 0
        decreases fuel
    {
        if fuel == 0 then NoFuel
        else if pc == |prog| then Ok(env)
        else (
            match prog[pc] {
                case Instruction(op, src_reg, dest_reg, offset, imm) => (
                    match op {
                        case ArithmeticOperation(opcode, source, cls) => (
                            match handleArithmeticInstructions(opcode, source, cls, src_reg, dest_reg, offset, imm, env) {
                                case None => Error(pc, "Error in arithmetic operation!")
                                case Some(updated_env) => executeStatement(prog, updated_env, mem, pc+1, fuel-1)
                            }
                        )
                        case ByteSwapOperation(opcode, source, cls) => (
                            match handleByteSwapInstructions(opcode, source, cls, dest_reg, imm, env) {
                                case None => Error(pc, "Error in byte swap operation!")
                                case Some(updated_env) => executeStatement(prog, updated_env, mem, pc+1, fuel-1)
                            }
                        )
                        case JumpOperation(opcode, source, cls) => (
                            match handleJumpInstructions(opcode, source, cls, src_reg, dest_reg, offset, imm, env, mem) {
                                case None => Error(pc, "Error in jump operation!")
                                // Point to Note: The env and/or mem can only be updated in case of BPF_CALL
                                case Some((updated_env, updated_mem, pc_offset)) => executeStatement(prog, updated_env, updated_mem, pc+pc_offset, fuel-1)
                            }
                        )
                        case LoadOperation(mode, size, cls) => (
                            match handleLoadInstructions(mode, size, cls, src_reg, dest_reg, offset, imm, env) {
                                case None => Error(pc, "Error in load operation!")
                                case Some(updated_env) => executeStatement(prog, updated_env, mem, pc+1, fuel-1)
                            }
                        )
                        case StoreOperation(mode, size, cls) => (
                            match handleStoreInstructions(mode, size, cls, src_reg, dest_reg, offset, imm, env, mem) {
                                case None => Error(pc, "Error in store operation!")
                                case Some((updated_env, updated_mem)) => executeStatement(prog, updated_env, updated_mem, pc+1, fuel-1)
                            }
                        )
                        case SignedLoadOperation(mode, size, cls) => (
                            match handleSignedLoadInstructions(mode, size, cls, src_reg, dest_reg, offset, imm, env) {
                                case None => Error(pc, "Error in signed load operation")
                                case Some(updated_env) => executeStatement(prog, updated_env, mem, pc+1, fuel-1)
                            }
                        )
                        case AtomicOperation(mode, size, cls) => (
                            match handleAtomicInstructions(mode, size, cls, src_reg, dest_reg, offset, imm, env, mem) {
                                case None => Error(pc, "Error in atomic operation")
                                case Some((updated_env, updated_mem)) => executeStatement(prog, updated_env, updated_mem, pc+1, fuel-1)
                            }
                        )
                        case _ => (
                            Error(pc, "Invalid instruction encountered!")
                        )
                    }
                )
                case Instruction128(op, src_reg, dest_reg, offset, imm, next_imm) => (
                    match op {
                        case Immediate64Operation(mode, size, cls) => (
                            match handleImmediate64Instructions(mode, size, cls, src_reg, dest_reg, offset, imm, next_imm, env) {
                                case None => Error(pc, "Error in immediate64 operation")
                                case Some(updated_env) => executeStatement(prog, updated_env, mem, pc+1, fuel-1)
                            }
                        )
                        case _ => (
                            Error(pc, "Invalid instruction encountered!")
                        )
                    }
                )
            }
        )
    }

    /*method Main() {
        var i1: int64 := S64_MIN;
        var i2: int64 := S64_MAX;
        var i3: int64 := -0x7FFF_FFFF_FFFF_FFFF;
        var i4: int64 := 0x7FFF_FFFF_FFFF_FFFF;
        var i5: int64 := -5;

        print "**********************************************", "\n";
        print S32_MIN, "\n";
        print S32_MAX, "\n";

        print "**********************************************", "\n";
        print i1, "\n";
        print (i1 as int) % 0x8000_0000, "\n";
        print ((i1 as int) % 0x8000_0000) - 0x8000_0000, "\n";
        print "**********************************************", "\n";

        print i2, "\n";
        print (i2 as int) % 0x8000_0000, "\n";
        print "**********************************************", "\n";

        print i3, "\n";
        print (i3 as int) % 0x8000_0000, "\n";
        print ((i3 as int) % 0x8000_0000) - 0x8000_0000, "\n";
        print "**********************************************", "\n";

        print i4, "\n";
        print (i4 as int) % 0x8000_0000, "\n";
        print "**********************************************", "\n";

        print i5, "\n";
        print (i5 as int) % 0x8000_0000, "\n";
        print ((i5 as int) % 0x8000_0000) - 0x8000_0000, "\n";
        print "**********************************************", "\n";
    }*/
}