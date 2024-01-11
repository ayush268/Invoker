include "BoundedInts.dfy"
include "Types.dfy"

module Helpers {
    import opened BoundedInts
    import opened Types

    // Assumption: Giving the default value as zero if not present in the map
    // TODO: Confirm the assumption
    function getRegValue(reg: Register, values: RegisterMap): RegisterValue
    {
        if reg in values then values[reg]
        else 0
    }

    function updateRegValue(reg: Register, val: RegisterValue, values: RegisterMap): RegisterMap
    {
        values[reg := val]
    }

    // Currently doing signed conversion, i.e.
    // U64_MIN -> S32_MIN (the signed will be carried forward)
    // rest of the bits (other than signed) will be picked up directly
    // as their value is.
    // TODO: Confirm the assumption
    function castIntToInt32(source: int): int32
    {
        var int_val: int := source % 0x8000_0000;
        if source >= 0 then (int_val as int32)
        else (int_val - 0x8000_0000) as int32
    }

    function castIntToInt64(source: int): int64
    {
        var int_val: int := source % 0x8000_0000_0000_0000;
        if source >= 0 then (int_val as int64)
        else (int_val - 0x8000_0000_0000_0000) as int64
    }

    function castInt64ToInt32(source: int64): int32
    {
        castIntToInt32(source as int)
    }

    function castInt32ToInt64(source: int32): int64
    {
        (source as int) as int64
    }
}