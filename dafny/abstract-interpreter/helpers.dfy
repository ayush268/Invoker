include "BoundedInts.dfy"

module helpers {

  import opened BoundedInts

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


}