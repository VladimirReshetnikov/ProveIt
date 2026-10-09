"""Deterministic independent finite audits; writes a new JSON evidence file."""
from __future__ import annotations
import json, platform, random, sys, time
from pathlib import Path
from disk_kernel import Candidate, partitions, root_row, reduce_family, minimum_completion
from certificate_check import graph_completion, reference_row, verify_certificate
from signed_kernel import signed_states, signed_row, signed_graph_completion
from surface_model import glue_two, assemble_patches
from assembly import Layer, solve, replay_surface


def rank(rows):
    pivots={}
    for row in rows:
        while row:
            k=row.bit_length()-1
            if k not in pivots:
                pivots[k]=row;break
            row^=pivots[k]
    return len(pivots)


def run():
    start=time.perf_counter();rng=random.Random(20261009)
    result={"seed":20261009,"python":sys.version,"platform":platform.platform(),
            "scope":"finite partition and abstract triangulated-surface audit; no knot corpus"}
    ranks=[];pairs=0
    for r in range(1,8):
        ps=list(partitions(r));matrix=[]
        for p in ps:
            row=0
            for j,q in enumerate(ps):
                row|=int(graph_completion(p,q))<<j;pairs+=1
            matrix.append(row)
        got=rank(matrix);assert got==1<<(r-1)
        ranks.append({"r":r,"partitions":len(ps),"direct_matrix_rank":got})
    result['direct_matrix_pairs']=pairs;result['ranks']=ranks
    cases=1000;weighted_queries=0
    for _ in range(cases):
        r=rng.randrange(1,8);ps=list(partitions(r))
        items=[Candidate(rng.choice(ps),rng.randrange(-1000,1001)) for _ in range(rng.randrange(1,101))]
        red=reduce_family(items)
        assert verify_certificate([x.partition for x in items],[x.cost for x in items],red.certificate)
        for q in (ps if r<=4 else rng.choices(ps,k=25)):
            a,b=minimum_completion(items,q),minimum_completion(red.retained,q)
            assert (None if a is None else a.cost)==(None if b is None else b.cost)
            weighted_queries+=1
    result['weighted_families']=cases;result['weighted_completion_queries']=weighted_queries
    surface_cases=1000
    for _ in range(surface_cases):
        r=rng.randrange(1,9);ps=list(partitions(r));p,q=rng.choice(ps),rng.choice(ps)
        twists=tuple(rng.randrange(2) for i in range(r))
        s=glue_two(p,q,twists)
        assert s['is_disk']==graph_completion(p,q)
        assert s['chi']==max(p)+max(q)+2-r
        assert (s['component_count']==1 and s['components'][0]['orientable'])==signed_graph_completion(p,(0,)*r,q,twists)
    result['literal_surface_cases']=surface_cases
    # A positive-defect annulus glued to another disk remains positive-defect.
    s=assemble_patches([(0,0,0),(0,0),(0,)],
                       [((0,0),(1,0)),((0,1),(1,1)),((0,2),(2,0))])
    assert s['chi']==0 and not s['is_disk'];result['persistent_defect_control']=s
    grammar_cases=200
    for _ in range(grammar_cases):
        r=rng.randrange(1,6);ps=list(partitions(r))
        initial=[Candidate(p,rng.randrange(-10,20)) for p in rng.choices(ps,k=12)]
        layers=[]
        for j in range(3):
            s=rng.randrange(1,6)
            options=[]
            for k in range(10):
                # Random disk components, including births, merges and dead ends.
                from disk_kernel import canonical
                p=canonical(rng.randrange(max(1,(r+s)//2)) for i in range(r+s))
                options.append(Candidate(p,rng.randrange(-5,10)))
            layers.append(Layer(r,s,tuple(options)));r=s
        caps=[Candidate(p,rng.randrange(10)) for p in list(partitions(r))]
        a=solve(initial,layers,caps,compressed=False)
        b=solve(initial,layers,caps,collect_certificates=True)
        assert (a['status'],a['cost'])==(b['status'],b['cost'])
        for e in b['certificates']:
            assert verify_certificate(e['partitions'],e['costs'],e['certificate'])
        if b['witness'] is not None:
            replay=replay_surface(initial,layers,caps,b['witness'])
            assert replay['is_disk'] and replay['cost']==b['cost']
    result['complete_grammar_comparisons']=grammar_cases
    result['seconds']=time.perf_counter()-start;result['status']='PASS'
    return result

if __name__=='__main__':
    out=Path(sys.argv[1]) if len(sys.argv)>1 else Path('results/audit.json')
    result=run();out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
