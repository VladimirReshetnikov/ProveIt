"""Reproducible finite mathematical audit (no native topology claims)."""
import itertools, json, random, sys, time, platform
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from ordered_kernel import *
from scripts.oracles import sparse, optimal_subsets, maximum_positive_pivots
from reference.positive_predecessor.cancellation.deferred import deferred_plan, transport_exact_counts


def run():
    start=time.perf_counter(); counts={}; checksum=0; maxima={}
    for m,n,alphabet in [(0,0,1),(1,4,3),(2,3,3),(3,2,3),(3,3,2),(3,3,3)]:
        label=f'{m}x{n}_alphabet{alphabet}'; count=0; work=0; peak=0
        for flat in itertools.product(range(alphabet),repeat=m*n):
            a=sparse([flat[i*n:(i+1)*n] for i in range(m)])
            p=ordered_plan(a)
            if p['status']!='OPTIMAL_MATRIX_PLAN': raise AssertionError((a,p))
            expected,_=optimal_subsets(a)
            assert (p['cost'],len(p['deferred_rows']))==expected,(a,p,expected)
            assert verify_plan(a,p)
            if m<=2 or n<=2:
                assert m-p['cost']==maximum_positive_pivots([flat[i*n:(i+1)*n] for i in range(m)])
            checksum+=p['cost']; count+=1
            work=max(work,p['stats']['work']); peak=max(peak,p['stats']['peak_states'])
        counts[label]=count; maxima[label]={'max_work':work,'max_peak_states':peak}
        print(label,count,flush=True)
    rng=random.Random(20261012)
    weighted=0; orders=0; source_comparisons=0; transfer=0; wide_alternates=0
    for k in range(350):
        m=rng.randrange(1,8); n=rng.randrange(1,8)
        a={r:{c:rng.choice((1,1,2,3)) for c in range(n) if rng.random()<0.4} for r in range(m)}
        w={r:rng.randrange(10) for r in a}
        p=ordered_plan(a,w); expected,_=optimal_subsets(a,w)
        assert (p['cost'],len(p['deferred_rows']))==expected,(a,w,p,expected)
        assert verify_plan(a,p,w)
        automatic=optimize_counts(a,w)
        assert automatic['status']=='OPTIMAL_MATRIX_PLAN'
        assert (automatic['cost'],len(automatic['deferred_rows']))==expected
        assert verify_plan(a,automatic,w)
        weighted+=1
        if k<120:
            labels,adj,_=Matrix.parse(a).graph()
            order=list(range(len(adj))); rng.shuffle(order)
            td=elimination_decomposition(adj,order)
            if td.width <= 5:
                q=ordered_plan(a,w,td,limits=Limits(max_width=5,max_states=1000000))
                assert q['status']=='OPTIMAL_MATRIX_PLAN',(k,q)
                assert (q['cost'],len(q['deferred_rows']))==expected
                orders+=1
            else:
                # Alternative random orders can be intentionally very poor.
                # Test truthful refusal rather than allocating factorial tables.
                q=ordered_plan(a,w,td,limits=Limits(max_width=5))
                assert q['status']=='RESOURCE_LIMIT'
                wide_alternates+=1
        if k<200:
            q=ordered_plan(a); old=deferred_plan(a,m)
            assert q['cost']==old['minimum_deferrals']; source_comparisons+=1
            assert transport_counts(a,q)==transport_exact_counts(a,q['deferred_rows'],q['cancellations'])
            transfer+=1
    scc=0; closure=0
    from ordered_kernel.two_incidence import reachability_graph, reachable
    from scripts.oracles import peel_literal
    for k in range(800):
        m=rng.randrange(1,9); n=rng.randrange(1,10)
        a={r:{} for r in range(m)}
        for c in range(n):
            for r in rng.sample(range(m),rng.randrange(min(2,m)+1)):
                a[r][c]=rng.choice((1,1,2,3))
        w={r:rng.randrange(12) for r in a}
        p=two_incidence_plan(a,w); expected,_=optimal_subsets(a,w)
        assert (p['cost'],len(p['deferred_rows']))==expected
        assert verify_two_incidence_optimality(a,p,w); scc+=1
        graph,roots=reachability_graph(Matrix.parse(a,w))
        d={r for r in a if rng.random()<0.3}
        reached=reachable(graph,roots|d)
        _,remaining=peel_literal(a,d)
        assert set(a)-remaining==reached
        closure+=1
    result={'status':'PASS','environment':{'python':sys.version,'platform':platform.platform()},
            'exhaustive':counts,'total_exhaustive':sum(counts.values()),'exhaustive_maxima':maxima,
            'weighted_random_optima':weighted,'automatic_core_optima':weighted,'alternate_decompositions':orders,'wide_alternate_refusals':wide_alternates,
            'actual_predecessor_optimum_comparisons':source_comparisons,
            'actual_predecessor_transfer_comparisons':transfer,
            'two_incidence_weighted_optima':scc,'reachability_closure_checks':closure,
            'sum_exhaustive_optima':checksum,'seconds':time.perf_counter()-start,
            'scope':'finite matrices, not native knot benchmarks'}
    (ROOT/'results'/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':run()
