include "SimpleVerifier.dfy"

module SimpleVerifierAnalysis {
    import opened Lang
    import opened ConcreteEval
    import opened AbstractEval

    datatype Visited = EXPLORED | EXPLORING | NOT_EXPLORED

    function num_unexplored(visited: seq<Visited>): int 
        decreases |visited|
    {
        if |visited| == 0 then
            0
        else 
            if visited[0] == NOT_EXPLORED then
                1 + num_unexplored(visited[1..])
            else
                num_unexplored(visited[1..])
    }

    // Recursive DFS
    function check_cfg_acyclic(prog: Program, idx: int, visited: seq<Visited>): Option<(seq<Visited>, bool)> 
        requires |visited| == |prog.stmts|
        decreases num_unexplored(visited)
    {
        if |prog.stmts| == 0 then
            Some((visited, true))
        else
            if idx >= |prog.stmts| || idx < 0 then
                None
            else
                if visited[idx] == EXPLORING then
                    Some((visited, false))
                else
                //TODO: Write some conditionals here
                    if visited[idx] == NOT_EXPLORED then
                      //var visited_status := if visited[idx] == NOT_EXPLORED then EXPLORING else EXPLORED;
                        assert visited[idx] != EXPLORING && visited[idx] != EXPLORED; 
                        var visited_updated := visited[idx := EXPLORING];
                        assert |visited_updated| == |visited|;
                        //assert visited_updated[idx] != NOT_EXPLORED;
                        assert forall i :: (0 <= i < |visited| && i != idx) ==> (visited[i] == visited_updated[i]);

                        assert num_unexplored(visited_updated) <= num_unexplored(visited); 
                
                        match prog.stmts[idx] {
                            case JmpZero(reg, offset) => 
                                match check_cfg_acyclic(prog, idx + offset as int, visited_updated) {
                                    case Some((visited', acyclic)) => 
                                        if acyclic then
                                            check_cfg_acyclic(prog, idx + 1, visited')
                                        else
                                            Some((visited', false))
                                    case None => Some((visited_updated, true))

                                }
                            case default => check_cfg_acyclic(prog, idx + 1, visited_updated)
                        }
                    else
                        Some((visited, true))
    }


    method dummy(visited: seq<Visited>, idx: int) returns (y: bool) 
        requires |visited| > 0
    {
        if idx >= |visited| || idx < 0 {
            y := false;
        }
        else {
            if visited[idx] == NOT_EXPLORED {
                //var visited_status := if visited[idx] == NOT_EXPLORED then EXPLORING else EXPLORED;
                assert visited[idx] != EXPLORING && visited[idx] != EXPLORED; 
                var visited_updated := visited[idx := EXPLORING];
                assert |visited_updated| == |visited|;
                //assert visited_updated[idx] != NOT_EXPLORED;
                assert forall i :: (0 <= i < |visited| && i != idx) ==> (visited[i] == visited_updated[i]);

                assert num_unexplored(visited_updated) <= num_unexplored(visited);
            
               y :=  true;
            }
            else {
                y := true;
            }
        }
    }


    //function explore_states()
}