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
}