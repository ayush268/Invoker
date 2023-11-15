include "BoundedInts.dfy"
include "types.dfy"
include "ebpf.dfy"

module eBPFInterpreter {
  import opened BoundedInts
  import opened parser
  import opened types

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

  function checkRegArg(env: BPFVerifierEnv, reg: RegisterOrUnused, argType: RegisterArgType): bool {
    false
  }

  predicate check_mem_access(env: BPFVerifierEnv, insn_idx: uint32, register: RegisterOrUnused,
                             offset: int16, size: LoadSize, t: BPFAccessType, value_register: RegisterOrUnused, strict_alignment_once: bool) {
    true
  }

  function cur_regs(env: BPFVerifierEnv): seq<BPFRegState>
    requires env.cur_state.BPFVerifierState?
    requires env.cur_state.curframe as int < |env.cur_state.frame|
  {
    env.cur_state.frame[env.cur_state.curframe].regs
  }

  // Assumes that the program has just a single global function
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

            // Question: How to update nested structs in a better way?
            err := checkRegArg(env, instruction.srcReg, SRC_OP) || checkRegArg(env, instruction.destReg, DST_OP_NO_MARK) ||
                   check_mem_access(env, env.insn_idx, instruction.srcReg,
                                    instruction.offset, loadSize, BPF_READ, instruction.destReg, false); // Checks memory access and updates the abstract state of the register

            //TODO: Implement AUX ptr type
            //err := err || saveAuxPtrType(env, cur_regs(env)[srcRegNo], false);
          }
        }

        case default => {}
      }

      break;
    }




    valid := true;

  }
}