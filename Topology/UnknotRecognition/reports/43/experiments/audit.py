#!/usr/bin/env python3
"""Deterministic exhaustive and seeded differential validation. No dependencies."""
import sys,json,random,copy,time,platform
from pathlib import Path
from itertools import product
from collections import Counter
ROOT=Path(__file__).resolve().parents[1]
sys.path[:0]=[str(ROOT/'src'),str(ROOT/'tests')]
from whitehead_exposure.algebra import *
from whitehead_exposure.selector import *
from whitehead_exposure.flow import *
from whitehead_exposure.slp import *
from whitehead_exposure.engine import *
from whitehead_exposure.braid import *
from helpers import all_moves,literal_oracle,random_word,barrier

def main():
    start=time.perf_counter(); report={'python':sys.version,'platform':platform.platform(),'seed':20261008}
    words=checks=existence=0
    for n in range(1,7):
        for w in product((-2,-1,1,2),repeat=n):
            if cyclic_reduce(w)!=w:continue
            words+=1;graph=word_graph(w); found=False
            for a,S in all_moves([1,2]):
                z=cyclic_reduce(y for x in w for y in whitehead_image(x,a,S))
                c=cut_capacity(graph,S)
                assert sum(abs(x)==abs(a) for x in z)==c
                assert Counter(abs(x) for x in z if abs(x)!=abs(a))==Counter(abs(x) for x in w if abs(x)!=abs(a))
                assert len(z)-len(w)==c-sum(abs(x)==abs(a) for x in w)
                found |= c==1; checks+=1
            assert found==bool(unit_bridges(graph,(-2,-1,1,2)))
            existence+=1
    report['cyclic_words']=words;report['occurrence_move_checks']=checks;report['bridge_existence_checks']=existence
    rng=random.Random(20261008); comparisons=0; verified=0; flow_calls=0
    for rank,iterations in ((2,100),(3,160),(4,60)):
        for _ in range(iterations):
            alive=list(range(1,rank+1))
            W=[random_word(rng,rank,rng.randint(0,20)) for _ in range(rng.randint(1,4))]
            for objective in ('allocation','length'):
                stats={};p=find_exposure(W,alive,objective=objective,stats=stats)
                expected=literal_oracle(W,alive,objective)
                got=None if p is None else ((p['allocation_bound'],p['length_change']) if objective=='allocation' else (p['length_change'],p['allocation_bound']))
                assert expected==got
                comparisons+=1;flow_calls+=stats['flows']
                if p is not None:
                    assert verify_exposure_graphs([word_graph(w) for w in W],tuple(alive),p);verified+=1
    report['selector_objective_comparisons']=comparisons;report['exposure_witnesses_verified']=verified;report['selector_flow_calls']=flow_calls
    flow_tests=0; tamper_tests=0
    for _ in range(500):
        n=rng.randint(2,8);V=tuple(range(n))
        G={(i,j):rng.randint(1,10**5) for i in V for j in V if i<j and rng.random()<.6}
        p=minimum_pinned_cut(G,V,{0},{n-1},Budget())
        expected=min(cut_capacity(G,{0}|{v for v in V[1:-1] if mask>>(v-1)&1}) for mask in range(1<<(n-2)))
        assert p['capacity']==expected and verify_pinned_cut(G,V,{0},{n-1},p);flow_tests+=1
        q=copy.deepcopy(p);q['capacity']+=1
        assert not verify_pinned_cut(G,V,{0},{n-1},q);tamper_tests+=1
    report['independent_flow_comparisons']=flow_tests;report['tampered_flow_rejections']=tamper_tests
    barriers=[]
    for m in range(1,33):
        W=barrier(m);p=find_exposure(W,[1,2]); assert p['allocation_bound']==34*m and p['length_change']==2*m-2
        strict=search_presentation(W,[1,2],mode='strict');expose=search_presentation(W,[1,2])
        assert strict['status']=='INCONCLUSIVE' and expose['status']=='FREE_RANK_ONE'
        assert len(expose['moves'])==2 and verify_presentation_trace(expose)
        if m in (1,2,16,32):barriers.append({'m':m,'before':20*m+5,'whitehead_after':22*m+3,'raw_bound':34*m,'final':0})
    report['barrier_presentations_checked']=32;report['barrier_examples']=barriers
    u,v=barrier(1);slopes=[]
    for a,S in all_moves([1,2]):
        changes=[len(cyclic_reduce(y for x in w for y in whitehead_image(x,a,S)))-len(w) for w in (u,v)]
        slopes.append({'multiplier':a,'subset':sorted(S),'changes':changes})
    report['rank_two_move_table']=slopes;report['seconds']=time.perf_counter()-start
    (ROOT/'data'/'audit.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('rank_two_move_table','python','platform')},indent=2))
if __name__=='__main__':main()
