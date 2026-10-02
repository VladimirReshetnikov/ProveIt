#!/usr/bin/env python3
"""Deterministic, reproducible finite tests; not a substitute for the proof."""
from __future__ import annotations
from itertools import product, combinations
from pathlib import Path
import json, random, time
from quadratic_compiler import Network, Rule, Compiled, HornCompiled, simulate, save_example

ROOT=Path(__file__).resolve().parents[1]
COUNTS={}

def equilibrium(net, ds, labels, times, M):
    """Literal simultaneous semantics; independent of polynomial implementation."""
    seeds=dict(net.seeds)
    for v,a in seeds.items():
        if labels[v]!=a or times[v]!=0: return False
    for v in range(net.sites):
        if v in seeds: continue
        candidates=[(M,0)]
        for a in range(1,net.labels+1):
            offers=[]
            for r,d in zip(net.rules,ds):
                if r.head!=(v,a): continue
                effective=[times[u] if labels[u]==b else M for u,b in r.tail]
                offers.append(d+max(effective,default=0))
            candidates.append((min([M]+offers),a))
        t,a=min(candidates)
        if labels[v]!=a or times[v]!=t: return False
    return True

def all_equilibria(net, ds, M):
    free=[v for v in range(net.sites) if v not in dict(net.seeds)]
    states=[(0,M)]+[(a,t) for a in range(1,net.labels+1) for t in range(M)]
    result=[]; examined=0
    for state in product(states,repeat=len(free)):
        labels=[0]*net.sites; times=[M]*net.sites
        for v,a in net.seeds: labels[v]=a; times[v]=0
        for v,(a,t) in zip(free,state): labels[v]=a; times[v]=t
        examined+=1
        if equilibrium(net,ds,labels,times,M): result.append((labels,times))
    COUNTS['semantic_assignments_examined']=COUNTS.get('semantic_assignments_examined',0)+examined
    return result

def check_instance(net,ds,timed=True,brute=False,mutate=False,expanded=False):
    c=Compiled(net,timed=timed); w,labels,times=c.witness(ds); M=c.M.value(w)
    assert equilibrium(net,ds,labels,[M if t is None else t for t in times],M)
    if brute:
        roots=all_equilibria(net,ds,M)
        assert roots==[(labels,[M if t is None else t for t in times])], (net,ds,roots)
        COUNTS['brute_semantic_instances']=COUNTS.get('brute_semantic_instances',0)+1
    if mutate:
        for v in c.c.variables:
            bad=dict(w); bad[v]+=1
            assert c.c.evaluate(bad)>0, (v,net,ds)
            COUNTS['single_coordinate_mutations']=COUNTS.get('single_coordinate_mutations',0)+1
    if expanded:
        p=c.c.expanded(); assert all(len(k)<=2 for k in p)
        rng=random.Random(773)
        for j in range(6):
            x=w if j==0 else {v:rng.randrange(6) for v in c.c.parameters+c.c.variables}
            a=sum(coef*__import__('math').prod(x[v] for v in mon) for mon,coef in p.items())
            assert a==c.c.evaluate(x) and a>=0
            COUNTS['expanded_polynomial_evaluations']=COUNTS.get('expanded_polynomial_evaluations',0)+1
    COUNTS['compiled_instances']=COUNTS.get('compiled_instances',0)+1

def test_gates():
    checked=0
    for kind in ['min','max']:
        for x,y in product(range(6),repeat=2):
            zeros=[]
            for z,a,b in product(range(6),repeat=3):
                p=((x-z-a)**2+(y-z-b)**2+a*b if kind=='min' else
                   (z-x-a)**2+(z-y-b)**2+a*b)
                assert p>=0; checked+=1
                if p==0: zeros.append((z,a,b))
            target=min(x,y) if kind=='min' else max(x,y)
            assert len(zeros)==1 and zeros[0][0]==target
    COUNTS['gate_tuples_examined']=checked
    # The symbolic-cap mux, including the absent-label alternative.
    checked=0
    for M in range(1,5):
        for t in range(M+1):
            for label in range(3):
                for b in [1,2]:
                    roots=[]
                    for f,a,h in product(range(M+1),repeat=3):
                        p=(f-t-a)**2+(M-f-h)**2+(label==b)*a+(label!=b)*h
                        checked+=1
                        if p==0: roots.append((f,a,h))
                    F=t if label==b else M
                    assert roots==[(F,F-t,M-F)]
    COUNTS['mux_tuples_examined']=checked

def test_catalogues():
    # Every subset of the eight positive Horn rules on two unseeded sites.
    tails=[(),((0,1),),((1,1),),((0,1),(1,1))]
    universe=[Rule((v,1),tail) for v in range(2) for tail in tails]
    for mask in range(1<<len(universe)):
        rules=tuple(r for j,r in enumerate(universe) if mask>>j&1)
        net=Network(2,1,(),rules)
        check_instance(net,[1]*len(rules),timed=False,brute=True)
    # All unordered catalogues of <=2 distinct rules, 2 sites, 2 competing labels;
    # empty or singleton bodies; every delay assignment in {1,2}.
    literals=[(v,a) for v in range(2) for a in [1,2]]
    universe=[Rule(h,t) for h in literals for t in [()]+[(p,) for p in literals]]
    for nr in range(3):
        for rules in combinations(universe,nr):
            net=Network(2,2,(),rules)
            for ds in product([1,2],repeat=nr):
                check_instance(net,ds,timed=True,brute=True)

def test_random():
    rng=random.Random(20261002)
    for i in range(300):
        n=rng.randrange(1,9); q=rng.randrange(1,5)
        seeds=tuple((v,rng.randrange(1,q+1)) for v in range(n) if rng.random()<0.22)
        free=[v for v in range(n) if v not in dict(seeds)]
        lits=[(v,a) for v in range(n) for a in range(1,q+1)]
        rules=[]
        if free:
            for j in range(rng.randrange(0,18)):
                tail=tuple(sorted(rng.sample(lits,rng.randrange(min(len(lits),4)+1))))
                rules.append(Rule((rng.choice(free),rng.randrange(1,q+1)),tail))
        net=Network(n,q,seeds,tuple(rules))
        ds=[rng.randrange(1,8) for _ in rules]
        check_instance(net,ds,mutate=True,expanded=(i<30))
        check_instance(net,[1]*len(rules),timed=False,mutate=(i<30))
    COUNTS['random_networks']=300

def test_limits_and_examples():
    # Directed self-assembly locking counterexample, S -> A -> C -> B-at-A's-site.
    ghost=Network(3,2,((0,1),),(Rule((1,1),((0,1),)),Rule((2,1),((1,1),)),Rule((1,2),((2,1),))))
    check_instance(ghost,[1,1,1],timed=False,brute=True,mutate=True,expanded=True)
    known={(0,1)}
    while True:
        nxt=known|{r.head for r in ghost.rules if set(r.tail)<=known}
        if nxt==known: break
        known=nxt
    assert (1,2) in known and simulate(ghost,[1]*3)[0][1]==1
    data=save_example(ROOT/'results/locking_counterexample.json',ghost,[1]*3,timed=False)
    examples={'locking_counterexample':data['counts']}
    # A blocked typed cycle, a simultaneous tie, an unreachable empty-rule label.
    race=Network(6,2,((0,1),),(
        Rule((1,1),((0,1),)), Rule((1,2),()),
        Rule((2,1),((1,1),)), Rule((2,2),((1,2),)),
        Rule((3,1),((4,1),)), Rule((4,1),((3,1),)),
        Rule((5,2),((2,1),)), Rule((5,1),((2,2),))))
    ds=[2,2,3,1,1,1,4,1]
    check_instance(race,ds,mutate=True,expanded=True)
    data=save_example(ROOT/'results/timed_race.json',race,ds)
    examples['timed_race']=data['counts']
    huge=Network(5,1,((0,1),),tuple(Rule((v,1),((v-1,1),)) for v in range(1,5)))
    ds=[10**30+1,10**30+3,10**30+7,10**30+9]
    check_instance(huge,ds,mutate=True,expanded=True)
    data=save_example(ROOT/'results/huge_delay_chain.json',huge,ds)
    examples['huge_delay_chain']=data['counts']
    # Zero-delay self-support: deliberately bypass the positive-delay interface.
    zero=Network(1,1,(),(Rule((0,1),((0,1),)),))
    assert len(all_equilibria(zero,[0],1))==2
    # Empty network and an entirely seeded network.
    check_instance(Network(0,1,(),()),[],expanded=True)
    check_instance(Network(2,2,((0,1),(1,2)),()),[],expanded=True)
    # Exponential independent timing phases: all 2^8 labelled outputs.
    n=8; independent=Network(n,2,(),tuple(Rule((v,a),()) for v in range(n) for a in [1,2]))
    outputs=set()
    for bits in product([0,1],repeat=n):
        ds=[d for bit in bits for d in ((1,2) if bit==0 else (2,1))]
        c=Compiled(independent); w,labels,times=c.witness(ds); outputs.add(tuple(labels))
    assert len(outputs)==2**n; COUNTS['timing_phase_outputs']=len(outputs)
    for bad in [Network(2,1,((0,1),(0,1)),()),
                Network(1,1,(),(Rule((0,2),()),)),
                Network(1,1,((0,1),),(Rule((0,1),()),)),
                Network(1,1,(),(Rule((0,1),((0,1),(0,1))),))]:
        try: Compiled(bad)
        except ValueError: pass
        else: raise AssertionError('Invalid catalogue accepted')
    for ds in [[0],[-1],[1,2]]:
        try: simulate(zero,ds)
        except ValueError: pass
        else: raise AssertionError('Invalid delays accepted')
    COUNTS['invalid_inputs_rejected']=7
    return examples


def test_tiles_and_horn():
    # Literal three-site restriction of the four-tile aTAM counterexample.
    # Types: S=1, A=2, C=3, B=4. Glues g,h each have strength 2.
    ns={1:('g',None),2:('h','g'),3:(None,'h'),4:('h',None)}
    rules=[]
    for v in [1,2]:
        for a in range(1,5):
            for u in [v-1,v+1]:
                if not 0<=u<3: continue
                for b in ([1] if u==0 else range(1,5)):
                    ga=ns[a][1 if u<v else 0]; gb=ns[b][0 if u<v else 1]
                    if ga is not None and ga==gb: rules.append(Rule((v,a),((u,b),)))
    net=Network(3,4,((0,1),),tuple(rules))
    c=Compiled(net,timed=False); w,labels,times=c.witness()
    assert labels==[1,2,3] and times==[0,1,2]
    check_instance(net,[1]*len(rules),timed=False,brute=True,mutate=True,expanded=True)
    data=save_example(ROOT/'results/literal_four_tile_example.json',net,[1]*len(rules),timed=False)
    # Check the four-neighbor antichain incidence bound for many actual weights.
    maximum=0; policies=0
    for weights in product(range(4),repeat=4):
        for tau in range(1,13):
            minimal=[]
            for mask in range(16):
                total=sum(weights[i] for i in range(4) if mask>>i&1)
                if total>=tau and all(total-weights[i]<tau for i in range(4) if mask>>i&1):
                    minimal.append(mask)
            inc=sum(mask.bit_count() for mask in minimal)
            maximum=max(maximum,inc); assert inc<=12; policies+=1
    assert maximum==12
    COUNTS['four_neighbor_weight_threshold_policies']=policies
    # Independent comparison of optimized Horn allocation with general compiler.
    rng=random.Random(194761)
    for i in range(160):
        n=rng.randrange(1,8); seeds=tuple((v,1) for v in range(n) if rng.random()<0.2)
        free=[v for v in range(n) if v not in dict(seeds)]; rules=[]
        if free:
            for _ in range(rng.randrange(12)):
                tail=tuple((u,1) for u in sorted(rng.sample(range(n),rng.randrange(min(n,4)+1))))
                rules.append(Rule((rng.choice(free),1),tail))
        net=Network(n,1,seeds,tuple(rules))
        for timed in [False,True]:
            ds=[rng.randrange(1,12) if timed else 1 for _ in rules]
            hc=HornCompiled(net,timed); hw,hl,ht=hc.witness(ds)
            gc=Compiled(net,timed); gw,gl,gt=gc.witness(ds)
            assert (hl,ht)==(gl,gt)
            for v in hc.free: assert hw[f't_{v}']==gw[f't_{v}']
    COUNTS['optimized_horn_comparisons']=320
    return data['counts']

if __name__=='__main__':
    start=time.perf_counter(); (ROOT/'results').mkdir(exist_ok=True)
    test_gates(); test_catalogues(); test_random(); examples=test_limits_and_examples()
    examples['literal_four_tile_example']=test_tiles_and_horn()
    result={'status':'PASS','random_seed':20261002,'counts':COUNTS,'examples':examples,
        'scope':'Finite tests and symbolic sparse expansion checks. Universal correctness and uniqueness are proved in the article, not established by exhaustive testing.',
        'runtime_seconds':round(time.perf_counter()-start,3)}
    (ROOT/'results/test_receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
