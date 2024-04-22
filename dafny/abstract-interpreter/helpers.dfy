include "BoundedInts.dfy"
include "SimpleVerifier.dfy"

module helpers {

  import opened BoundedInts
  import opened Lang

  function signed_add64(a: uint64, b: uint64): uint64 {
    (((a as int) + (b as int)) % 0x1_00000000_00000000) as uint64
  }

  function unsigned_to_signed64(a: uint64): int64 {
    if a >= 0x8000_0000_0000_0000 then
      -(TWO_TO_THE_64 - (a as int)) as int64
    else
      a as int64
  }

  function signed32_to_unsigned64(a: int32): uint64 {
    if a < 0 then
      (TWO_TO_THE_32 + (a as int)) as uint64
    else
      a as uint64
  }

  function signed32_to_unsigned32(a: int32): uint32 {
    if a < 0 then
      (TWO_TO_THE_32 + (a as int)) as uint32
    else
      a as uint32
  }

  predicate pc_in_bounds(prog: Program, pc: int) {
    0 <= pc < |prog.stmts|
  }

  predicate pc_at_end(prog: Program, pc: int) {
    pc == |prog.stmts|
  }

  predicate pc_in_bounds_or_at_end(prog: Program, pc: int) {
    pc_in_bounds(prog, pc) || pc_at_end(prog, pc)
  }

  predicate pc_offset_in_bounds_or_at_end(prog: Program, pc: nat, offset: nat) {
    pc_in_bounds_or_at_end(prog, pc + offset)
  }

  predicate pc_offset_in_bounds(prog: Program, pc: nat, offset: nat) {
    pc_in_bounds(prog, pc + offset)
  }

  predicate in_bounds_path<T>(i: int, path: seq<T>) {
    0 <= i < |path|
  }

  predicate is_branch_instruction(prog: Program, pc: nat) {
    prog.stmts[pc].JmpZero?
  }

  // pc in [start, end)
  predicate pc_in_range(pc: nat, start: nat, end: nat) {
    start <= pc < end
  }

}