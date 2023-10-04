module parser {

    datatype BPFProgram = Statements(s: StatementList)
    datatype StatementList = Cons(stmt: Statement, next: StatementList) | EmptyList

    //TODO: Think about whether int is the right datatype for offset (u16) and immediate(u32)
    //TODO: Do we really need Immediate32?
    datatype Statement = Instruction(op: Op, srcReg: Register, destReg: Register, offset: int, immediate: int) | Immediate32(immediate: int)
    //TODO: Add Legacy BPF Instructions
    datatype Op = ArithmeticOperation(arithmeticInstructionClass: ArithmeticInstructionClass, arithmeticSource: ArithmeticSource, arithmeticOpcode: ArithmeticOpCode) | // BPF_ALU, BPF_ALU64
                  JumpOperation(jumpInstructionClass: JumpInstructionClass, jumpSource: JumpSource, jumpOpcode: JumpOpCode) | // BPF_JMP and BPF_JMP32
                  ByteSwapOperation(byteSwapInstructionClass: ByteSwapInstructionClass, byteSwapSource: ByteSwapSource, byteSwapOpcode: ByteSwapOpCode) | // BPF_ALU
                  LoadOperation(loadInstructionClass: LoadInstructionClass, loadSize: LoadSize, loadMode: LoadMode) | // BPF_LD | BPF_LDX
                  StoreOperation(storeInstructionClass: StoreInstructionClass, storeSize: StoreSize, storeMode: StoreMode) | // BPF_ST | BPF_STX
                  AtomicOperation(atomicInstructionClass: AtomicInstructionClass, atomicSize: AtomicSize, atomicMode: AtomicMode, shouldFetch: bool) |
                  //TODO: Do we really need this separation here?
                  Immediate64Operation(immediate64InstructionClass: Immediate64InstructionClass, immediate64Size: Immediate64Size, immediate64Mode: Immediate64Mode, subtype: Immediate64Type)

    datatype ArithmeticSource = BPF_K | BPF_X
    datatype ArithmeticOpCode = BPF_ADD | BPF_SUB | BPF_MUL | BPF_DIV | BPF_OR | BPF_AND | BPF_LSH | BPF_RSH | BPF_NEG | BPF_MOD | BPF_XOR | BPF_MOV | BPF_ARSH

    datatype JumpSource = BPF_K | BPF_X
    datatype JumpOpCode = BPF_JA | BPF_JMP | BPF_JEQ | BPF_JGT | BPF_JGE | BPF_JSET | BPF_JNE | BPF_JSGT | BPF_JSGE | BPF_CALL | BPF_EXIT | BPF_JLT | BPF_JLE | BPF_JSLT | BPF_JSLE

    datatype ByteSwapSource = BPF_TO_LE | BPF_TO_BE
    datatype ByteSwapOpCode = BPF_END

    datatype LoadSize = BPF_W | BPF_H | BPF_B | BPF_DW
    datatype LoadMode = BPF_ABS | BPF_IND | BPF_MEM

    datatype StoreSize = BPF_W | BPF_H | BPF_B | BPF_DW
    datatype StoreMode = BPF_ABS | BPF_IND | BPF_MEM

    datatype Immediate64Size = BPF_DW
    datatype Immediate64Mode = BPF_IMM
    datatype Immediate64Type = IMM64 | MAP_BY_FD | MVA_MAP_BY_FD | VARIABLE_ADDR | CODE_ADDR | MAP_BY_IDX | MVA_MAP_BY_IDX

    datatype AtomicSize = BPF_W | BPF_DW
    datatype AtomicMode = BPF_ATOMIC

    datatype ArithmeticInstructionClass = BPF_ALU | BPF_ALU64
    datatype JumpInstructionClass = BPF_JMP | BPF_JMP32
    datatype ByteSwapInstructionClass = BPF_ALU
    datatype LoadInstructionClass = BPF_LD | BPF_LDX
    datatype StoreInstructionClass = BPF_ST | BPF_STX
    datatype AtomicInstructionClass = BPF_STX
    datatype Immediate64InstructionClass = BPF_LD

    datatype InstructionClass = BPF_LD | BPF_LDX | BPF_ST | BPF_STX | BPF_ALU | BPF_JMP | BPF_JMP32 | BPF_ALU64
    datatype InstructionClassType = ArithmeticInstructionClass(arithInstructionClass: ArithmeticInstructionClass) | JumpInstructionClass(jumpInstructionClass: JumpInstructionClass) | 
                                    ByteSwapInstructionClass(byteSwapInstructionClass: ByteSwapInstructionClass) | LoadInstructionClass(loadInstructionClass: LoadInstructionClass) | StoreInstructionClass(storeInstructionClass: StoreInstructionClass) | AtomicInstructionClass(atomicInstructionClass: AtomicInstructionClass)
    datatype SourceType = ArithmeticSource(arithSource: ArithmeticSource) | ByteSwapSource(byteSwapSource: ByteSwapSource) | JumpSource(jmpSource: JumpSource)
    datatype SizeType = LoadSize(loadsz: LoadSize) | StoreSize(stpresz: StoreSize) | AtomicSize(atomicsz: AtomicSize) | Immediate64Size(imm64sz: Immediate64Size)
    datatype OpCodeType = ArithmeticOpCode(arithopcode: ArithmeticOpCode) | JumpOpCode(jmpopcode: JumpOpCode) | ByteSwapOpCode(byteswapopcode: ByteSwapOpCode)
    datatype ModeType = LoadMode(loadmode: LoadMode) | StoreMode(storemode: StoreMode) | AtomicMode(atomicmode: AtomicMode) | Immediate64Mode(imm64mode: Immediate64Mode)

    datatype Register = R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7 | R8 | R9 | R10

    method print_statements(prog: StatementList) {
        match prog {
            case Cons(s, n) => { print s; print_statements(n); }
            case EmptyList => {}
        }
    }

    method parse_prog(prog: BPFProgram) returns (y: int) {
        match prog {
            case Statements(s) => {
                print_statements(s);
            }
        }

        y := 0;
    }

    method Main() {
        var t := EmptyList;
        var prog : BPFProgram := Statements(t);
        print_statements(prog.s);
    }

}