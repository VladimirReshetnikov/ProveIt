"""Exhaustive, randomized, and exact-small-field audits."""
from __future__ import annotations
from collections import Counter
from itertools import combinations, product
import hashlib, json, platform, random, sys, time
from pathlib import Path
from activation_forest import Instance, solve, verify_positive, verify_obstruction
from activation_forest.closure import Activation
from activation_forest.matroid import representatives
from activation_forest.algebra import sample_representation, vector_rank
from activation_forest.solve import search_projected
from .fixtures import random_instance, repository_loop, choice_arms
from .oracles import brute_solve, brute_representatives, brute_projected, deleted_closure, independent
ROOT=Path(__file__).resolve().parents[1]

def audit_answer(x,counters,seed):
    truth,witness,_=brute_solve(x)
    answer=solve(x,rounds=8,seed=seed,try_incumbent=False,max_b=None,max_transitions=None)
    counters['cases']+=1
    counters['positive_inputs' if truth else 'negative_inputs']+=1
    counters[answer['status']]+=1
    counters['route:'+answer.get('route','sample-miss-or-local-negative')]+=1
    if answer['status']=='SUCCESS': assert truth and verify_positive(x,answer['certificate'])
    elif answer['status']=='BLOCKED_EXACT': assert not truth and verify_obstruction(x,answer['obstruction'])
    elif truth: counters['positive_unknown']+=1
    return answer

def main():
    start=time.perf_counter()
    report={'python':sys.version,'platform':platform.platform(),'seed':20261012,
            'scope':'Matrix/dual-graph and finite-field audits; not native topology execution.'}
    exhaustive=Counter(); edges=((0,1),(1,2),(0,2),(0,1))
    for index,values in enumerate(product(range(3),repeat=8)):
        x=Instance(3,edges,tuple(tuple(values[2*r:2*r+2]) for r in range(4)),2)
        audit_answer(x,exhaustive,index+413)
    report['exhaustive_4_by_2']=dict(exhaustive); print('exhaustive',dict(exhaustive),flush=True)
    rng=random.Random(20261012); finite=Counter()
    for i in range(1500): audit_answer(random_instance(rng),finite,i+91317)
    report['random_matrix_graph']=dict(finite); print('random',dict(finite),flush=True)
    planted=Counter()
    for b in range(3,8):
        for q in range(1,7):
            m=b+q
            x=Instance(m,tuple((i,(i+1)%m) for i in range(m)),
                       tuple((1,) if i<b else (0,) for i in range(m)),1)
            for trial in range(10):
                a=solve(x,seed=30000+100*b+10*q+trial,rounds=8,try_incumbent=False,max_b=None,max_transitions=None)
                planted['cases']+=1; planted[a['status']]+=1; planted['rounds']+=len(a['stats']['rounds'])
                if a['status']=='SUCCESS': assert verify_positive(x,a['certificate'])
    report['planted_generic_positive']=dict(planted); print('planted',dict(planted),flush=True)
    mi=Counter(); x=Instance(4,((0,1),(0,2),(0,3),(1,2),(1,3),(2,3)),((),)*6,0)
    subsets=[s for k in range(3) for s in combinations(range(6),k) if independent(x,s)]
    for colors in product((-1,0,1),repeat=6):
        groups=[{e for e,c in enumerate(colors) if c==i} for i in range(2)]
        for fixed in subsets:
            expected=brute_representatives(x,groups,fixed); actual=representatives(x,groups,fixed)
            assert actual['complete']==(expected is not None)
            mi['queries']+=1
    report['forced_matroid_intersection']=dict(mi); print('intersection',dict(mi),flush=True)
    closure_count=projected=nofalse=0
    for case in range(450):
        x=random_instance(rng,max_m=7); a=Activation(x); union=set().union(set(),*a.mandatory)
        for k in range(min(3,x.m)+1):
            for seeds in combinations(sorted(set(range(x.m))-union),k):
                actual=representatives(x,a.mandatory,fixed=seeds) if independent(x,seeds) else None
                if actual and actual['complete']:
                    literal=deleted_closure(x,(*seeds,*actual['edges']))
                    mask=sum(1<<j for j,e in enumerate(a.boundary) if e in literal)
                    assert a.seed_closure(seeds)==mask
                    closure_count+=1
        p=rng.choice((2,3,5,101)); v=sample_representation(x,a.mandatory,a.b,p,rng)
        if v is None: continue
        rank=len(v[0]) if v else 0
        for k in range(min(rank,3)+1):
            for seeds in combinations(range(x.m),k):
                if vector_rank([v[e] for e in seeds],p)==k:
                    assert brute_representatives(x,a.mandatory,seeds) is not None
                    nofalse+=1
        expected=brute_projected(a,v,p,rank); found,_=search_projected(a,v,p)
        assert (expected is None)==(found is None)
        projected+=1
    report['horn_closure_vs_literal_queries']=closure_count
    report['sampled_independence_soundness_queries']=nofalse
    report['representative_dp_vs_literal']=projected
    print('closure / sampled / DP',closure_count,nofalse,projected,flush=True)
    x=Instance(3,((0,1),(0,2),(1,2)),((),)*3,0); fields=[]
    for p in (2,3,5,7):
        failures=0
        for z0,z1,projection in product(range(p),repeat=3):
            class Fixed:
                def __init__(self): self.values=iter((z0,z1,projection))
                def randrange(self,bound): return next(self.values)
            v=sample_representation(x,[{0,1}],1,p,Fixed())
            failures+=v is None or not any(v[2])
        assert failures==2*p*p-p
        fields.append(dict(prime=p,samples=p**3,misses=failures,exact_miss_numerator=2*p-1,
                           exact_miss_denominator=p*p,theorem_bound_numerator=2,theorem_bound_denominator=p))
    report['exact_small_field_spaces']=fields
    from .fixtures import parallel_obstruction,generic_positive,generic_negative
    for name,x in [('repository_loop',repository_loop()),('parallel_negative_6',parallel_obstruction(6)),
                   ('generic_positive',generic_positive()),('generic_negative',generic_negative()),('choice_arms_3',choice_arms(3))]:
        (ROOT/'examples'/f'{name}.json').write_text(json.dumps(x.to_dict(),indent=2)+'\n')
        answer=solve(x,seed=1210,try_incumbent=False,max_transitions=None)
        (ROOT/'results'/f'{name}_answer.json').write_text(json.dumps(answer,indent=2)+'\n')
    report['elapsed_seconds']=time.perf_counter()-start
    report['script_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    (ROOT/'results'/'validation.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2),flush=True)

if __name__=='__main__': main()
