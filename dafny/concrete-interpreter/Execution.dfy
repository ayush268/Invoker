include "BoundedInts.dfy"
include "Types.dfy"

// This module will be fully pure with zero side-effects
// The only changes would be to the returned state

// Have to ensure that for a certain input the output always remains
// the same i.e. the purity (or consistency) is upheld
module Execution {
    import opened BoundedInts
    import opened Types

    function executeProgram(prog: BPFProgram): EnvironmentMap {
        // TODO
        []
    }

    function executeStatement(prog: seq<Statement>, env: EnvironmentMap): EnvironmentMap {
        // TODO
        []
    }
}