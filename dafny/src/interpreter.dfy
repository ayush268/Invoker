module BoundedInts {
  newtype int8  = x: int  | -0x80 <= x < 0x80
  newtype int16 = x: int  | -0x8000 <= x < 0x8000
  newtype int32 = x: int  | -0x8000_0000 <= x < 0x8000_0000
  newtype int64 = x: int  | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000

  newtype uint8 = x:int | 0 <= x < 0x100
  newtype uint16 = x:int | 0 <= x < 0x1_0000
  newtype uint32 = x:int | 0 <= x < 0x1_0000_0000
  newtype uint64 = x:int | 0 <= x <= 0xFFFF_FFFF_FFFF_FFFF


  type byte = uint8
  type bytes = seq<byte>
}

module eBPFInterpreter {
    import opened BoundedInts
	import opened parser

    datatype RegisterType = NOT_INIT /* nothing was written into register */ |
	                        SCALAR_VALUE /* reg doesn't contain a valid pointer */ |
	                        PTR_TO_CTX /* reg points to bpf_context */ |
	                        CONST_PTR_TO_MAP /* reg points to struct bpf_map */ |
	                        PTR_TO_MAP_VALUE /* reg points to map element value */ |
	                        PTR_TO_MAP_KEY /* reg points to a map element key */ | 
	                        PTR_TO_STACK /* reg == frame_pointer + offset */ |
	                        PTR_TO_PACKET_META /* skb->data - meta_len */ |
	                        PTR_TO_PACKET /* reg points to skb->data */ |
	                        PTR_TO_PACKET_END /* skb->data + headlen */ |
	                        PTR_TO_FLOW_KEYS /* reg points to bpf_flow_keys */ |
	                        PTR_TO_SOCKET /* reg points to struct bpf_sock */ |
	                        PTR_TO_SOCK_COMMON /* reg points to sock_common */ |
	                        PTR_TO_TCP_SOCK /* reg points to struct tcp_sock */ |
	                        PTR_TO_TP_BUFFER /* reg points to a writable raw tp's buffer */ |
	                        PTR_TO_XDP_SOCK /* reg points to struct xdp_sock */ |
	                        /* PTR_TO_BTF_ID points to a kernel struct that does not need
	                        * to be null checked by the BPF program. This does not imply the
	                        * pointer is _not_ null and in practice this can easily be a null
	                        * pointer when reading pointer chains. The assumption is program
	                        * context will handle null pointer dereference typically via fault
	                        * handling. The verifier must keep this in mind and can make no
	                        * assumptions about null or non-null when doing branch analysis.
	                        * Further, when passed into helpers the helpers can not, without
	                        * additional context, assume the value is non-null.
	                        */
	                        PTR_TO_BTF_ID |
	                        /* PTR_TO_BTF_ID_OR_NULL points to a kernel struct that has not
	                        * been checked for null. Used primarily to inform the verifier
	                        * an explicit null check is required for this struct.
	                        */
	                        PTR_TO_MEM		 /* reg points to valid memory region */ | 
	                        PTR_TO_BUF		 /* reg points to a read/write buffer */ | 
	                        PTR_TO_FUNC		 /* reg points to a bpf program function */ |
	                        CONST_PTR_TO_DYNPTR	 /* reg points to a const struct bpf_dynptr */ |
                            PTR_TO_MAP_VALUE_OR_NULL | PTR_TO_SOCKET_OR_NULL | PTR_TO_SOCK_COMMON_OR_NULL | PTR_TO_TCP_SOCK_OR_NULL | PTR_TO_BTF_ID_OR_NULL

    datatype PTR_TO_MAP_VALUE_OR_NULL = PTR_MAYBE_NULL | PTR_TO_MAP_VALUE
    datatype PTR_TO_SOCKET_OR_NULL = PTR_MAYBE_NULL | PTR_TO_SOCKET
    datatype PTR_TO_SOCK_COMMON_OR_NULL = PTR_MAYBE_NULL | PTR_TO_SOCK_COMMON
    datatype PTR_TO_TCP_SOCK_OR_NULL = PTR_MAYBE_NULL | PTR_TO_TCP_SOCK
    datatype PTR_TO_BTF_ID_OR_NULL = PTR_MAYBE_NULL | PTR_TO_BTF_ID

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
    

		method runInstruction(op: Op, srcReg: Register, destReg: Register, offset: int16, immediate: int32) {
			match op {
				case ArithmeticOperation(arithmeticInstructionClass, arithmeticSource, arithmeticOpcode) => {
					var source_immediate: bool := arithmeticSource == ArithmeticSource.BPF_K;
					var width_64: bool := arithmeticInstructionClass == ArithmeticInstructionClass.BPF_ALU64;

					match arithmeticOpcode {
						case BPF_ADD => {
							var src_reg: uint8 := RegisterToInt(srcReg);
							var dst_reg: uint8 := RegisterToInt(destReg);
							// TODO: How to do signed addition here?
							regs.concrete_regs[dst_reg] := regs.concrete_regs[dst_reg] + if source_immediate then immediate else regs.concrete_regs[src_reg];
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
					runInstruction(op, srcReg, destReg, offset, immediate);
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
}