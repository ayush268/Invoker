module eBPFInterpreter {
    import opened BoundedInts

    // Modelling struct bpf_reg_state
    datatype Register {
        var type: RegisterType;
        //TODO: Add more things
        var smin_value: int /* minimum possible (s64)value */
	s64 smax_value; /* maximum possible (s64)value */
	u64 umin_value; /* minimum possible (u64)value */
	u64 umax_value; /* maximum possible (u64)value */
	s32 s32_min_value; /* minimum possible (s32)value */
	s32 s32_max_value; /* maximum possible (s32)value */
	u32 u32_min_value; /* minimum possible (u32)value */
	u32 u32_max_value; /* maximum possible (u32)value */
    }

    class Registers {
        var regs: array<Register>;
    }

    class ExecutionContext {
        var regs: Registers;

    }
}