include "BoundedInts.dfy"
include "types.dfy"
include "ebpf.dfy"

module eBPFInterpreter {
    import opened BoundedInts
	import opened parser
	import opened types
    
	// Modelling struct bpf_verifier_state
	class BpfVerifierState {
		/* call stack tracking */
		var bpf_func_state: array<BpfFuncState>
		var parent: BpfVerifierState

		var branches_count : uint32
		
	}

	// Modelling struct bpf_func_state
	class BpfFuncState {

	}

    // Modelling struct bpf_reg_state
    class AbstractRegisterState {

        var typ: RegisterType

        // Range Analysis
        var smin_value: int64 /* minimum possible (s64)value */
	    var smax_value: int64 /* maximum possible (s64)value */
	    var umin_value: uint64 /* minimum possible (u64)value */
	    var umax_value: uint64 /* maximum possible (u64)value */
	    var s32_min_value: int32 /* minimum possible (s32)value */
	    var s32_max_value: int32 /* maximum possible (s32)value */
	    var u32_min_value: uint32 /* minimum possible (u32)value */
	    var u32_max_value: uint32 /* maximum possible (u32)value */

		constructor() { 
			typ := NOT_INIT;
		}

        //TODO: Add More stuff
    }

    class ConcreteRegisterState {
        var value: uint64

		constructor() {
			value := 0;
		}
    }

    class Registers {
        var abs_regs: array<AbstractRegisterState>
        var concrete_regs: array<ConcreteRegisterState>

        constructor (num_regs: uint64) 
        {
			var abs := new AbstractRegisterState();
            abs_regs := new AbstractRegisterState[num_regs](_ => abs);

			var conc := new ConcreteRegisterState();
            concrete_regs := new ConcreteRegisterState[num_regs](_ => conc);
        }
    }

    class Map {
		//TODO: Convert these to enums?
        var key_typ: uint64
		var val_typ: uint64

		//TODO: Model Key value pairs

    }

	method RegisterToInt(reg: Register) returns (y: uint8) {
		match reg {
			case R0 => { y := 0; }
			case R1 => { y := 1; }
			case R2 => { y := 2; }
			case R3 => { y := 3; }
			case R4 => { y := 4; }
			case R5 => { y := 5; }
			case R6 => { y := 6; }
			case R7 => { y := 7; }
			case R8 => { y := 8; }
			case R9 => { y := 9; }
			case R10 => { y := 10; }
		}
	}

    class ExecutionContext {
        var regs: Registers
        var maps: array<Map>
		var pc: uint64

		constructor(n: uint64) {
			regs := new Registers(n);
			pc := 0;
		}
    

		method runInstruction(op: Op, srcReg: Register, destReg: Register, offset: int16, immediate: int32) returns (result: ExecutionContext) {
			match op {
				case ArithmeticOperation(arithmeticInstructionClass, arithmeticSource, arithmeticOpcode) => {
					var source_immediate: bool := arithmeticSource == ArithmeticSource.BPF_K;
					var width_64: bool := arithmeticInstructionClass == ArithmeticInstructionClass.BPF_ALU64;

					match arithmeticOpcode {
						case BPF_ADD => {
							var src_reg: uint8 := RegisterToInt(srcReg);
							var dst_reg: uint8 := RegisterToInt(destReg);
							// TODO: How to do signed addition here?
							// regs.concrete_regs[dst_reg] := regs.concrete_regs[dst_reg] + if source_immediate then immediate else regs.concrete_regs[src_reg];

						}

						case default => { } 
					}
				}

				case default => { print ("unimplemented"); } 
			}		
		}

		method executeStatement(stmt: Statement) {
			match stmt {
				case Instruction(op, srcReg, destReg, offset, immediate) => { 
					var result := runInstruction(op, srcReg, destReg, offset, immediate);
				}
				case Immediate32(immediate) => { }
			}
		}

		method executeStatementList(s: StatementList) {
			match s {
				case Cons(s, n) => {
					executeStatementList(n);
				}
				case EmptyList => { }
			}
		}

	}

	method executeProgram(prog: BPFProgram) {
		var ctx: ExecutionContext := new ExecutionContext(11);

		match prog {
			case Statements(s) => {
				ctx.executeStatementList(s);
			}
		}
	}

	method runVerifier(prog: BPFProg) returns (valid: bool) {
		//TODO: separate programs into subprograms (functions)
		//TODO: Check whether all the jumps in a function land inside the function
		//TODO: Run check_cfg() on the program
		
		var env : BPFVerifierEnv := BPFVerifierEnv();

	}
}