"""Emit small independently replayable research examples."""
from pathlib import Path
import json
from cographic import Graph, maximum_batch, side_histogram, finite_routing_forest
from causal import amplification, path_bounds, PersistentCounters
from verify import verify_batch, verify_routing, verify_trace, verify_reuse
from reuse import plan_reuse
ROOT=Path(__file__).resolve().parents[1]

def main():
    caps=(1,1,1); parents=((),(0,),(1,)); scores=amplification(caps,parents)
    graph=Graph(3,((0,1),(1,2),(0,2)),scores)
    packet=maximum_batch(graph)
    assert verify_batch(packet)
    before=sum(path_bounds(caps,parents))
    after=sum(path_bounds(caps,parents,(0,1,1)))
    result={'explanation':'Fixed-DAG upper-bound optimization, not actual knot timing.',
            'caps':caps,'parents':parents,'saved_progress':[1,1,1],
            'amplification':scores,'side_census':side_histogram(graph),'batch':packet,
            'total_bound_without_reuse':before,'total_bound_after_optimal_reuse':after}
    route=finite_routing_forest(6,[(0,1),(2,3),(4,5)],[(1,2),(3,4),(0,5)],scores)
    assert verify_routing(route)
    model=PersistentCounters((1,)*5,((),(0,),(1,),(2,),(3,))).finish()
    assert verify_trace(model.caps,model.parents,model.events)
    trace={'caps':model.caps,'parents':model.parents,'events':model.events,
           'versions':model.versions,'bounds':path_bounds(model.caps,model.parents)}
    composite=plan_reuse(3,graph.edges,caps,parents,(1,1,1))
    assert verify_reuse(composite)
    for name, data in [('causal_reuse_certificate.json',composite),('causal_reuse.json',result),('finite_routing.json',route),('sharp_chain.json',trace)]:
        (ROOT/'examples'/name).write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
