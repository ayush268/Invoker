include "BoundedInts.dfy"
include "ebpf.dfy"

module types {

  import opened BoundedInts
  import opened parser

  datatype Option<T> = Some(elem: T) | None

  datatype Error = ALUInstructionError | Success

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
                          PTR_TO_MEM   /* reg points to valid memory region */ |
                          PTR_TO_BUF   /* reg points to a read/write buffer */ |
                          PTR_TO_FUNC   /* reg points to a bpf program function */ |
                          CONST_PTR_TO_DYNPTR  /* reg points to a const struct bpf_dynptr */ |
                          PTR_TO_MAP_VALUE_OR_NULL | PTR_TO_SOCKET_OR_NULL | PTR_TO_SOCK_COMMON_OR_NULL | PTR_TO_TCP_SOCK_OR_NULL | PTR_TO_BTF_ID_OR_NULL

  datatype PTR_TO_MAP_VALUE_OR_NULL = PTR_MAYBE_NULL | PTR_TO_MAP_VALUE
  datatype PTR_TO_SOCKET_OR_NULL = PTR_MAYBE_NULL | PTR_TO_SOCKET
  datatype PTR_TO_SOCK_COMMON_OR_NULL = PTR_MAYBE_NULL | PTR_TO_SOCK_COMMON
  datatype PTR_TO_TCP_SOCK_OR_NULL = PTR_MAYBE_NULL | PTR_TO_TCP_SOCK
  datatype PTR_TO_BTF_ID_OR_NULL = PTR_MAYBE_NULL | PTR_TO_BTF_ID

  //TODO: struct bpf_prog

  datatype BPFProg = BPFProg(prog: BPFProgram)

  datatype TristateNum = TristateNum(value: uint64, mask: uint64)

  datatype RegisterArgType = SRC_OP | DST_OP | DST_OP_NO_MARK

  datatype BPFAccessType = BPF_READ | BPF_WRITE

  /* Liveness marks, used for registers and spilled-regs (in stack slots).
   * Read marks propagate upwards until they find a write mark; they record that
   * "one of this state's descendants read this reg" (and therefore the reg is
   * relevant for states_equal() checks).
   * Write marks collect downwards and do not propagate; they record that "the
   * straight-line code that reached this state (from its parent) wrote this reg"
   * (and therefore that reads propagated from this state or its descendants
   * should not propagate to its parent).
   * A state with a write mark can receive read marks; it just won't propagate
   * them to its parent, since the write mark is a property, not of the state,
   * but of the link between it and its parent.  See mark_reg_read() and
   * mark_stack_slot_read() in kernel/bpf/verifier.c.
 
  enum bpf_reg_liveness {
   REG_LIVE_NONE = 0, /* reg hasn't been read or written this branch */
   REG_LIVE_READ32 = 0x1, /* reg was read, so we're sensitive to initial value */
   REG_LIVE_READ64 = 0x2, /* likewise, but full 64-bit content matters */
   REG_LIVE_READ = REG_LIVE_READ32 | REG_LIVE_READ64,
   REG_LIVE_WRITTEN = 0x4, /* reg was written first, screening off later reads */
   REG_LIVE_DONE = 0x8, /* liveness won't be updating this register anymore */
  };*/
  datatype BPFRegLiveness = REG_LIVE_NONE | REG_LIVE_READ32 | REG_LIVE_READ64 | REG_LIVE_READ | REG_LIVE_WRITTEN | REG_LIVE_DONE

  //TODO: Add more fields
  datatype BPFRegState = BPFRegState(typ: RegisterType, offset: int32, var_off: TristateNum,
                                     smin_value: int64, smax_value: int64,
                                     umin_value: uint64,  umax_value: uint64,
                                     s32_min_value: int32, s32_max_value: int32,
                                     u32_min_value: uint32, u32_max_value: uint32,
                                     id: uint32, parent: Option<BPFRegState>, frameno: uint32, live: BPFRegLiveness)

  datatype BPFFuncState = BPFFuncState(regs: seq<BPFRegState>)

  //TODO: struct bpf_verifier_state st;
  datatype BPFVerifierState = BPFVerifierState(frame: seq<BPFFuncState>, parent: Option<BPFVerifierState>, branches: uint32,
                                               insn_idx: uint32, curframe: uint32, first_insn_idx: uint32, last_insn_idx: uint32, jmp_history: seq<(uint32, uint32)>)

  datatype BPFVerifierStateList = BPFVerifierStateList(state: BPFVerifierState, next: BPFVerifierStateList, miss_cnt: int, hit_cnt: int) | EmptyList

    /*

    /* verifier_state + insn_idx are pushed to stack when branch is encountered */
        struct bpf_verifier_stack_elem {
     /* verifer state is 'st'
         * before processing instruction 'insn_idx'
         * and after processing instruction 'prev_insn_idx'
     */
     struct bpf_verifier_state st;
     int insn_idx;
     int prev_insn_idx;
     struct bpf_verifier_stack_elem *next;
     /* length of verifier log at the time this state was pushed on stack */
     u32 log_pos;
    };

    */
  datatype BPFVerifierStackElem = BPFVerifierStackElem(
    st: BPFVerifierState,
    insn_idx: int64,
    prev_insn_idx: int64,
    next: Option<BPFVerifierStackElem>,
    log_pos: uint32
  )

  /* Linux 6.5.3
   struct bpf_verifier_env {
    u32 insn_idx;
    u32 prev_insn_idx;
    struct bpf_prog *prog;		/* eBPF program being verified */
    const struct bpf_verifier_ops *ops;
    struct bpf_verifier_stack_elem *head; /* stack of verifier states to be processed */
    int stack_size;			/* number of states to be processed */
    bool strict_alignment;		/* perform strict pointer alignment checks */
    bool test_state_freq;		/* test verifier with different pruning frequency */
    struct bpf_verifier_state *cur_state; /* current verifier state */
    struct bpf_verifier_state_list **explored_states; /* search pruning optimization */
    struct bpf_verifier_state_list *free_list;
    struct bpf_map *used_maps[MAX_USED_MAPS]; /* array of map's used by eBPF program */
    struct btf_mod_pair used_btfs[MAX_USED_BTFS]; /* array of BTF's used by BPF program */
    u32 used_map_cnt;		/* number of used maps */
    u32 used_btf_cnt;		/* number of used BTF objects */
    u32 id_gen;			/* used to generate unique reg IDs */
    bool explore_alu_limits;
    bool allow_ptr_leaks;
    bool allow_uninit_stack;
    bool bpf_capable;
    bool bypass_spec_v1;
    bool bypass_spec_v4;
    bool seen_direct_write;
    struct bpf_insn_aux_data *insn_aux_data; /* array of per-insn state */
    const struct bpf_line_info *prev_linfo;
    struct bpf_verifier_log log;
    struct bpf_subprog_info subprog_info[BPF_MAX_SUBPROGS + 1];
    union {
     struct bpf_idmap idmap_scratch;
     struct bpf_idset idset_scratch;
    };
    struct {
     int *insn_state;
     int *insn_stack;
     int cur_stack;
    } cfg;
    struct backtrack_state bt;
    u32 pass_cnt; /* number of times do_check() was called */
    u32 subprog_cnt;
    /* number of instructions analyzed by the verifier */
    u32 prev_insn_processed, insn_processed;
    /* number of jmps, calls, exits analyzed so far */
    u32 prev_jmps_processed, jmps_processed;
    /* total verification time */
    u64 verification_time;
    /* maximum number of verifier states kept in 'branching' instructions */
    u32 max_states_per_insn;
    /* total number of allocated verifier states */
    u32 total_states;
    /* some states are freed during program analysis.
      * this is peak number of states. this number dominates kernel
      * memory consumption during verification
     */
    u32 peak_states;
    /* longest register parentage chain walked for liveness marking */
    u32 longest_mark_read_walk;
    bpfptr_t fd_array;
 
    /* bit mask to keep track of whether a register has been accessed
      * since the last time the function state was printed
     */
    u32 scratched_regs;
    /* Same as scratched_regs but for stack slots */
    u64 scratched_stack_slots;
    u64 prev_log_pos, prev_insn_print_pos;
    /* buffer used to generate temporary string representations,
      * e.g., in reg_type_str() to generate reg_type string
     */
    char tmp_str_buf[TMP_STR_BUF_LEN];
   };
  */
  datatype BPFVerifierEnv = BPFVerifierEnv(
    insn_idx: uint32,
    prev_insn_idx: uint32,
    prog: BPFProg,
    //TODO: const struct bpf_verifier_ops *ops;
    head: seq<BPFVerifierStackElem>,
    //TODO: Do we need stack_stize?
    cur_state: BPFVerifierState,
    explored_states: seq<seq<BPFVerifierState>>,
    free_list: seq<BPFVerifierState>
    //TODO: used_maps
    //TODO: used_btfs
    //used_map_cnt: uint32,
    //used_btf_cnt: uint32,
    //id_gen: uint32,
    //explore_alu_limits: bool,
    //allow_ptr_leaks : bool,
    //allow_uninit_stack : bool,
    //bpf_capable : bool,
    //bypass_spec_v1 : bool,
    //bypass_spec_v4 : bool,
    //seen_direct_write : bool
    // TODO: Add more fields
  )
}