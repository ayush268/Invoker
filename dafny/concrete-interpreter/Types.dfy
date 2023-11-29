include "BoundedInts.dfy"

module Types {

    import opened BoundedInts

    // Basic datatypes used throughout the code.
    datatype Option<T> = Some(elem: T) | None
    {
        predicate IsFailure() {
            this.None?
        }
        function PropagateFailure<U>(): Option<U>
            requires IsFailure()
        {
            None
        }
        function Extract(): T
            requires !IsFailure()
        {
            this.elem
        }
    }

    // A BPF Program will be a list of sequential instructions
    datatype BPFProgram = Statements(inst: seq<Statement>)

    // An instruction can be 64 bit or 128 bits
    // This is essentially constituting the BPF bytecode
    datatype Statement = Instruction(op: OpCode, src_reg: Option<Register>, dest_reg: Option<Register>, offset: int16, imm: int32) |
                         Instruction128(op: OpCode, src_reg: Option<Register>, dest_reg: Option<Register>, offset: int16, imm: int32, next_imm: int32)
    
    // OpCode field is of 8 bits out of which 3 LSB is instruction class
    // We'll divide each instruction class into its own instruction type here itself
    datatype OpCode = ArithmeticOperation(ar_opcode: ArithmeticOpCode, ar_source: ArithmeticSource, ar_class: ArithmeticInstructionClass) |
                      ByteSwapOperation(byte_opcode: ByteSwapOpCode, byte_source: ByteSwapSource, byte_class: ByteSwapInstructionClass) |
                      JumpOperation(jump_opcode: JumpOpCode, jump_source: JumpSource, jump_class: JumpInstructionClass) |
                      LoadOperation(load_opcode: LoadMode, load_size: LoadSize, load_class: LoadInstructionClass) |
                      StoreOperation(store_opcode: StoreMode, store_size: StoreSize, store_class: StoreInstructionClass) |
                      SignedLoadOperation(signed_load_opcode: SignedLoadMode, signed_load_size: SignedLoadSize, signed_load_class: SignedLoadInstructionClass) |

                      // Special case of atomic operation where immediate field is encoded with a certain atomic operation
                      // This will be handled in the code logic itself instead of here since its not the part of the 
                      // opcode field.
                      AtomicOperation(atomic_opcode: AtomicMode, atomic_size: AtomicSize, atomic_class: AtomicInstructionClass) |

                      // Special case of immediate64operations where src field is encoded with a opcode subtype,
                      // will be handled in the code logic itself instead of here since its not the part of the
                      // opcode field.
                      Immediate64Operation(imm64_opcode: Immediate64Mode, imm64_size: Immediate64Size, imm64_class: Immediate64InstructionClass)
    
    // Arithmetic instructions
    datatype ArithmeticOpCode = BPF_ADD | BPF_SUB | BPF_MUL | BPF_DIV | BPF_SDIV | BPF_OR | BPF_AND | BPF_LSH |
                                BPF_RSH | BPF_NEG | BPF_MOD | BPF_SMOD | BPF_XOR | BPF_MOV | BPF_MOVSX | BPF_ARSH
    datatype ArithmeticSource = BPF_K | BPF_X
    datatype ArithmeticInstructionClass = BPF_ALU | BPF_ALU64


    // ByteSwap instructions
    datatype ByteSwapOpCode = BPF_END
    datatype ByteSwapSource = BPF_TO_LE | BPF_TO_BE | RESERVED
    datatype ByteSwapInstructionClass = BPF_ALU | BPF_ALU64


    // Jump instructions
    datatype JumpOpCode = BPF_JA | BPF_JEQ | BPF_JGT | BPF_JGE | BPF_JSET | BPF_JNE | BPF_JSGT |
                          BPF_JSGE | BPF_CALL | BPF_EXIT | BPF_JLT | BPF_JLE | BPF_JSLT | BPF_JSLE
    datatype JumpSource = BPF_K | BPF_X
    datatype JumpInstructionClass = BPF_JMP | BPF_JMP32


    // Load instructions
    datatype LoadMode = BPF_ABS | BPF_IND | BPF_MEM
    datatype LoadSize = BPF_W | BPF_H | BPF_B | BPF_DW
    datatype LoadInstructionClass = BPF_LD | BPF_LDX
    

    // Store instructions
    datatype StoreMode = BPF_ABS | BPF_IND | BPF_MEM
    datatype StoreSize = BPF_W | BPF_H | BPF_B | BPF_DW
    datatype StoreInstructionClass = BPF_ST | BPF_STX


    // Signed Load instructions
    datatype SignedLoadMode = BPF_MEMSX
    datatype SignedLoadSize = BPF_W | BPF_H | BPF_B
    datatype SignedLoadInstructionClass = BPF_LDX


    // Atomic instructions
    datatype AtomicMode = BPF_ATOMIC
    datatype AtomicSize = BPF_W | BPF_DW
    datatype AtomicInstructionClass = BPF_STX

    // to be used for later in code logic
    datatype AtomicOp = BPF_ADD | BPF_OR | BPF_AND | BPF_XOR | BPF_FETCH | BPF_XCHG | BPF_CMPXCHG


    // Immediate64 type instructions
    datatype Immediate64Mode = BPF_IMM
    datatype Immediate64Size = BPF_DW
    datatype Immediate64InstructionClass = BPF_LD

    // to be used for later in code logic
    datatype Immediate64Type = IMM64 | MAP_BY_FD | MV_MAP_BY_FD | VAR_ADDR | CODE_ADDR | MAP_BY_IDX | MV_MAP_BY_IDX


    // TODO: General types, define as needed

    // Possible register values
    datatype Register = R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7 | R8 | R9 | R10
    type RegisterValue = int64

    // TODO: Add eBPF Map functionality for required instructions
    // datatype eBPFMap<T, eBPFValue> =
    // datatype eBPFValue = Hash(size: int, data: u32)

    // Memory Management for execution
    // Defining our own custom memory map
    type Memory = int
    // For maintaining a list of memory available
    type MemoryList = seq<Memory>

    // Types of values which can be stored
    type Literal = int
    // TODO: Expand this value type as needed
    datatype Value = Lit(val: Literal)

    // TODO: Currently using direct memory to value map
    // Do we need equivalence classes and a unification algo here ?
    type MemoryToValueMap = map<Memory, Value>

    // TODO: Environment Variables to keep track of
    // Memory, register values, eBPF Maps

    // TODO: Update this to one with eq class if we are using that
    type AssignmentStore = MemoryToValueMap
    type RegisterMap = map<Register, RegisterValue>

    // TODO: Update Environment to include eBPF Maps later
    type Environment = (AssignmentStore, RegisterMap)

    // Execution can also result in an error which needs to be handled
    // TODO: Update errors or add more result types as needed
    datatype ExecResult<T> = Ok(result: T) | NoFuel | Error(code: int, message: string)

    method print_statements(prog: seq<Statement>) {
        var i: int := 0;
        while i < |prog| {
            print prog[i];
            i := i + 1;
        }
    }

    method parse_program(prog: BPFProgram) returns (err: int) {
        match prog {
            case Statements(s) => {
                print_statements(s);
            }
        }

        err := 0;
    }
}