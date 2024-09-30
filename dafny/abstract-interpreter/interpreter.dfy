include "BoundedInts.dfy"
include "types.dfy"
include "ebpf.dfy"
include "helpers.dfy"

module eBPFInterpreter {
  import opened BoundedInts
  import opened parser
  import opened types
  import opened helpers

  const BPF_MAX_REG := 11

  function RegisterToInt(reg: RegisterOrUnused): uint8
  {
    match reg {
      case R0 => 0
      case R1 => 1
      case R2 => 2
      case R3 => 3
      case R4 => 4
      case R5 => 5
      case R6 => 6
      case R7 => 7
      case R8 => 8
      case R9 => 9
      case R10 => 10
      case UNUSED => 0
    }
  }


  function unInitRegisterState(): BPFRegState
    //ensures unInitRegisterState().BPFRegState?
  {
    var ret: BPFRegState := BPFRegState(NOT_INIT, 0, TristateNum(0, 0),
                                        0, 0,
                                        0, 0,
                                        0, 0,
                                        0, 0,
                                        0, None, 0, REG_LIVE_NONE);
    ret
  }

  //TODO: Currently sets regs to the initial state assuming one function per program
  function createNewFuncState(): BPFFuncState
    //ensures |createNewFuncState().regs| == 11
  {
    var regs: seq<BPFRegState> := [unInitRegisterState(), unInitRegisterState(), unInitRegisterState(), unInitRegisterState(),
                                   unInitRegisterState(), unInitRegisterState(), unInitRegisterState(), unInitRegisterState(),
                                   unInitRegisterState(), unInitRegisterState(), unInitRegisterState()];

    var ret: BPFFuncState := BPFFuncState(regs);
    ret
  }

  function markRegWithType(regs: seq<BPFRegState>, regno: int, typ: RegisterType): seq<BPFRegState>
    requires 0 <= regno < |regs|
    requires forall idx :: 0 <= idx < |regs| ==> regs[idx].BPFRegState?
  {
    regs[regno := regs[regno].(typ := typ)]
  }

  //TODO: Assume a single frame for now
  function createNewBPFVerifierState(): BPFVerifierState {
    var ret: BPFVerifierState := BPFVerifierState([createNewFuncState()], None, 1, 0, 0, 0, 0, []);
    ret
  }

  //TODO: Instruction idx initialized to 0 assuming a single function program
  function createNewBPFVerifierEnv(prog: BPFProg): BPFVerifierEnv
    //ensures createNewBPFVerifierEnv(prog).insn_idx as int <= |prog.prog.s|
  {
    var ret: BPFVerifierEnv := BPFVerifierEnv(0, 0, prog, [], createNewBPFVerifierState(), [[]], []);
    ret
  }

  //TODO: Fill in all the cases
  function isReg64(env: BPFVerifierEnv, instruction: Statement, register: RegisterOrUnused, regstate: BPFRegState, argType: RegisterArgType): bool
    requires instruction.Instruction?
    requires !register.UNUSED?
  {
    match instruction.op {
      case JumpOperation(jumpInstructionClass, jumpSource, jumpOpcode) =>
        if jumpOpcode == BPF_EXIT then
          true
        else if jumpOpcode == BPF_CALL then
          // BPF Pseudo Call
          if RegisterToInt(instruction.srcReg) == 0x1 then
            false
          else if argType == SRC_OP then
            true
          else
            false
        else
          true


      case ArithmeticOperation(arithmeticInstructionClass, arithSource, arithOpcode) =>
        if arithmeticInstructionClass == ArithmeticInstructionClass.BPF_ALU64 then
          true
        else
          false

      case default => false
    }
  }

  function checkRegArg(env: BPFVerifierEnv, instruction: Statement, reg: RegisterOrUnused, argType: RegisterArgType): bool
    requires instruction.Instruction?
    requires !reg.UNUSED?
    requires env.cur_state.curframe as int < |env.cur_state.frame|
    requires |curRegs(env)| == BPF_MAX_REG
  {
    //TODO: Mark register scratched, maybe not very important
    var regState := curRegs(env)[RegisterToInt(reg)];
    var is64 := isReg64(env, instruction, reg, regState, argType);
    if argType == SRC_OP then
      //TODO: Fill in this case
      true
    else
    // Frame Pointer is read only
    if reg == RegisterOrUnused.R10 then
      //TODO: Add an error code here
      false
    else
      //TODO: The
      true

  }

  predicate check_mem_access(env: BPFVerifierEnv, insn_idx: uint32, register: RegisterOrUnused,
                             offset: int16, size: LoadSize, t: BPFAccessType, value_register: RegisterOrUnused, strict_alignment_once: bool) {
    true
  }

  function curRegs(env: BPFVerifierEnv): seq<BPFRegState>
    requires env.cur_state.BPFVerifierState?
    requires env.cur_state.curframe as int < |env.cur_state.frame|
  {
    env.cur_state.frame[env.cur_state.curframe].regs
  }

  function frameRegs(env: BPFVerifierEnv, frameno: uint32): seq<BPFRegState>
    requires env.cur_state.BPFVerifierState?
    requires frameno as int < |env.cur_state.frame|
  {
    env.cur_state.frame[frameno].regs
  }

  function update_regs(env: BPFVerifierEnv, regstate: BPFRegState, regno: uint8, frameno: uint32): BPFVerifierEnv
    requires frameno as int < |env.cur_state.frame|
    requires env.cur_state.curframe as int < |env.cur_state.frame|
    requires |frameRegs(env, frameno)| == BPF_MAX_REG
    requires 0 <= regno < BPF_MAX_REG as uint8
  {
    var frame_regs:= env.cur_state.frame[frameno].regs;
    // Updating the target reg
    var new_regs := frame_regs[regno := regstate];
    var new_func_state := env.cur_state.frame[frameno].(regs := new_regs);
    var new_frames := env.cur_state.(frame := env.cur_state.frame[frameno := new_func_state]);
    env.(cur_state := new_frames)
  }

  function markRegUnbounded(reg: BPFRegState): BPFRegState {
    reg.(smin_value := S64_MIN, smax_value := S64_MAX, umin_value := U64_MIN, umax_value := U64_MAX,
    s32_min_value := S32_MIN, s32_max_value := S32_MAX, u32_min_value := U32_MIN, u32_max_value := U32_MAX)
  }

  function markRegUnknown(env: BPFVerifierEnv, regs: seq<BPFRegState>, reg: RegisterOrUnused): BPFVerifierEnv
    requires |regs| == BPF_MAX_REG
    requires env.cur_state.curframe as int < |env.cur_state.frame|
    requires |curRegs(env)| == BPF_MAX_REG
  {
    var regno := RegisterToInt(reg);
    //TODO: Model and clear the union data in the kernel regstate
    //TODO: Model the ref_obj_id and precise fields
    var regstate := regs[regno].(typ := SCALAR_VALUE, offset := 0, id := 0, var_off := TristateNum(0, U64_MAX as uint64), frameno := 0);
    var regstate := markRegUnbounded(regstate);
    //TODO: Mark all fields appropriately

    update_regs(env, regstate, regno, env.cur_state.curframe)
  }

  function markRegKnown___(reg: BPFRegState, imm: int32): BPFRegState {
    reg.(smin_value := imm as int64, smax_value := imm as int64, umin_value := signed32_to_unsigned64(imm), umax_value := signed32_to_unsigned64(imm),
    s32_min_value := imm, s32_max_value := imm, u32_min_value := signed32_to_unsigned32(imm), u32_max_value := signed32_to_unsigned32(imm))
  }

  function markRegKnown__(env: BPFVerifierEnv, regs: seq<BPFRegState>, reg: RegisterOrUnused, imm: int32): BPFVerifierEnv
    requires env.cur_state.curframe as int < |env.cur_state.frame|
    requires |regs| == BPF_MAX_REG
    requires |curRegs(env)| == BPF_MAX_REG
  {
    var regno := RegisterToInt(reg);
    //TODO: Model the union in struct bpf_reg_state
    //TODO: Model the ref_obj_id
    var regstate := regs[regno].(offset := 0, id := 0);
    var regstate := markRegKnown___(regstate, imm);

    update_regs(env, regstate, regno, env.cur_state.curframe)
  }

  function adjustRegMinMaxVals(env: BPFVerifierEnv, instruction: Statement): (BPFVerifierEnv, Error) {
    //TODO: Implement this
    (env, Success)
  }


  function handleALUOp(instruction: Statement, env: BPFVerifierEnv): (BPFVerifierEnv, Error)
    requires instruction.Instruction?
    requires instruction.op.ArithmeticOperation?
    requires env.cur_state.curframe as int < |env.cur_state.frame|
    requires |curRegs(env)| == BPF_MAX_REG
    requires instruction.op.arithmeticOpcode == BPF_MOV ==> !instruction.destReg.UNUSED?
    requires instruction.op.arithmeticOpcode == ArithmeticOpCode.BPF_ADD ==> !instruction.destReg.UNUSED?
  {
    var srcReg: RegisterOrUnused := instruction.srcReg;
    var destReg: RegisterOrUnused := instruction.destReg;

    var op := instruction.op.arithmeticOpcode;

    var t := match instruction.op.arithmeticOpcode {
      case BPF_MOV =>
        //TODO: do checks for reserved fields
        var err := checkRegArg(env, instruction, instruction.destReg, DST_OP_NO_MARK);
        //TODO: Do early return on error here
        match instruction.op.arithmeticSource {
          // R = dest
          case BPF_X => (env, Success)
          // R = imm
          case BPF_K =>
            var temp_env := markRegUnknown(env, curRegs(env), instruction.destReg);
            var dest_reg_state := curRegs(temp_env)[RegisterToInt(instruction.destReg)];
            // Question: How does multiple declarations work here?
            var temp_env := update_regs(temp_env, dest_reg_state.(typ := SCALAR_VALUE), RegisterToInt(instruction.destReg), temp_env.cur_state.curframe);
            //TODO: Mark reg as known with the immediate
            var temp_env := markRegKnown__(env, curRegs(env), instruction.destReg, instruction.immediate);
            (temp_env, Success)
        }

      case BPF_ADD =>
        //TODO: do checks for reserved fields
        var err := checkRegArg(env, instruction, instruction.destReg, SRC_OP);
        //TODO: Do early return on error here
        //TODO: do more checks
        var err := checkRegArg(env, instruction, instruction.destReg, DST_OP_NO_MARK);
        //TODO: Do early return on error here
        adjustRegMinMaxVals(env, instruction)


      case default => (env, Success)
    };

    t

    //(env, Success)
  }

  // Assumes that the program has just a single global function
  // Assumes that there are no Immediate32 in the instruction stream
  method runVerifier(program: BPFProg) returns (valid: bool)
    requires |program.prog.s| > 0
    requires forall idx :: 0 <= idx < |program.prog.s| ==> program.prog.s[idx].Instruction?
  {
    //TODO: separate programs into subprograms (functions)
    //TODO: Check whether all the jumps in a function land inside the function
    //TODO: Run check_cfg() on the program

    // Question: How to model function pointers?
    var env : BPFVerifierEnv := createNewBPFVerifierEnv(program);
    //TODO: Finish initializing function args (PTR_CTX) for the main function
    //TODO: Analyze the first instruction of the kill_example, how is the pointer manipulated

    // Updating R1 to PTR_TO_CTX
    var func_frame : BPFFuncState := env.cur_state.frame[0].(regs := markRegWithType(env.cur_state.frame[0].regs, 1, RegisterType.PTR_TO_CTX));
    env := env.(cur_state := env.cur_state.(frame := [func_frame]));

    // TODO: Mark Register as known immediate(0)
    // But already init to zero

    //TODO: Check BTF for function argument correctness
    var prev_insn_idx: int := -1;

    while true {
      //TODO: Implement is_state_visited

      // Question: can we get counter example?
      var instruction := program.prog.s[env.insn_idx];
      var err := false;
      // Question why can destructors be used only with values constructed using the constructor?
      match instruction.op {
        case LoadOperation(cls, loadSize, loadMode) => {
          // r1 = PTR_TO_CTX
          // r1 = *(u64 *)(r1 + 0x18)
          if cls == LoadInstructionClass.BPF_LDX {

            var srcRegNo := RegisterToInt(instruction.srcReg);

            // Logically this is an error, UNUSED is treated as R0
            // If this condition is true then it indicates an error in the assembly parser
            if instruction.srcReg.UNUSED? {
              return false;
            }

            // Question: How to update nested structs in a better way?
            err := checkRegArg(env, instruction, instruction.srcReg, SRC_OP) || checkRegArg(env, instruction, instruction.destReg, DST_OP_NO_MARK) ||
                   check_mem_access(env, env.insn_idx, instruction.srcReg,
                                    instruction.offset, loadSize, BPF_READ, instruction.destReg, false); // Checks memory access and updates the abstract state of the register

            //TODO: Implement AUX ptr type
            //err := err || saveAuxPtrType(env, cur_regs(env)[srcRegNo], false);
          }
        }

        case ArithmeticOperation(arithInstructionClass, arithSrc, arithOp) => {
          if arithInstructionClass == ArithmeticInstructionClass.BPF_ALU64 ||
             arithInstructionClass == ArithmeticInstructionClass.BPF_ALU {
            if !instruction.destReg.UNUSED? {
              // Question: How to handle multiple returns?
              var r := handleALUOp(instruction, env);
            } else {
              print "BPF_MOV has dest reg UNUSED";
            }

          }

        }

        case default => {}
      }

      break;
    }




    valid := true;

  }
}