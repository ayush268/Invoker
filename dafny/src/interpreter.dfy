module eBPFInterpreter {
    import opened BoundedInts

    datatype Re

    // Modelling struct bpf_reg_state
    class RegisterState {

        var type: RegisterType;

        // Range Analysis
        var smin_value: int64; /* minimum possible (s64)value */
	    var smax_value: int64; /* maximum possible (s64)value */
	    var umin_value: uint64; /* minimum possible (u64)value */
	    var umax_value: uint64; /* maximum possible (u64)value */
	    var s32_min_value: int32; /* minimum possible (s32)value */
	    var s32_max_value: int32; /* maximum possible (s32)value */
	    var u32_min_value: uint32; /* minimum possible (u32)value */
	    var u32_max_value: uint32; /* maximum possible (u32)value */

        //TODO: Add More stuff
    }

    class Registers {
        var regs: array<RegisterState>;
    }

    class ExecutionContext {
        var regs: Registers;

    }
}