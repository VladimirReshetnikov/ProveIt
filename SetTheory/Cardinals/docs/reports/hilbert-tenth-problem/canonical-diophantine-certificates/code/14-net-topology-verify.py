#!/usr/bin/env python3
"""Reproduce finite checks and the exported quartics. No third-party packages.

Usage: python code/verify.py [--output data]
"""
from __future__ import annotations
import argparse
from collections import Counter
from itertools import product
import hashlib
import json
from pathlib import Path
import random
from certificates import *
from nets import *

def abstract_glue(M,J):
    # Independent connected-component oracle on 4 internal + external vertices.
    adj={i:[] for i in range(4)}
    for i in range(4):
        if not any(i in e for e in M):
            adj[i].append(4+i); adj[4+i]=[i]
    for a,b in list(M)+list(J): adj[a].append(b); adj[b].append(a)
    seen=set(); loops=0; pairs=set()
    for p in adj:
        if p in seen: continue
        todo=[p]; comp=set()
        while todo:
            x=todo.pop()
            if x in comp: continue
            comp.add(x); todo.extend(adj[x])
        seen.update(comp); ends=sorted(x-4 for x in comp if x>=4)
        if ends: assert len(ends)==2; pairs.add(tuple(ends))
        else: loops+=1
    return pairs,loops

def run(out: Path):
    out.mkdir(parents=True,exist_ok=True)
    report={"seed":20261002,"scope":"finite tests; not a formal proof or a full trace-polynomial emitter"}
    Jstats=[]
    for J,name in ((JDELTA,'delta'),(JGAMMA,'gamma')):
        S=loop_system(J); count=0; histogram=Counter(); rejected=0
        for bits in product((0,1),repeat=6):
            M={e for e,b in zip(EDGES,bits) if b}
            partial=all(sum(i in e for e in M)<=1 for i in range(4))
            if not partial:
                rejected+=1; continue
            W=loop_witness(M,J); assert S.accepts(W)
            P,c=abstract_glue(M,J)
            actual={e for e in EDGES if W['g'+ename(*e)]}
            assert (P,c)==(actual,W['cycles'])
            histogram[c]+=1; count+=1
        assert count==10 and rejected==54
        stats=S.export(out/f'{name}_loop_quartic.json',loop_witness(set(J),J),
                       {"kernel":name,"boundary_order":["u1","u2","v1","v2"]})
        Jstats.append(dict(name=name,valid_boolean_patterns=count,
                           impossible_boolean_patterns=rejected,loop_histogram=dict(histogram),**stats))
    report['loop_kernels']=Jstats
    nlogs=nvalid=mutations=0
    for L in (1,2,3):
        S=memory_system(L,2,2)
        choices=list(product(range(2),range(2),range(2)))
        for log in product(choices,repeat=L):
            W=memory_witness(log,2,2); valid=valid_memory_log(log)
            assert S.accepts(W)==valid
            nlogs+=1; nvalid+=valid
            if valid:
                for var in S.aux:
                    W[var]+=1; assert not S.accepts(W); W[var]-=1; mutations+=1
    report['memory']={"exhaustive_source_logs":nlogs,"valid_logs":nvalid,
                       "one_coordinate_mutations_rejected":mutations}
    log=[(1,1,7),(2,0,0),(1,0,7),(1,1,3)]
    S=memory_system(4,4,10); W=memory_witness(log,4,10)
    report['memory']['export']=S.export(out/'memory_example_quartic.json',W,
                                             {"L":4,"A":4,"V":10,"log":log})
    two_inputs=two_steps=0
    for ts in product(TYPES,repeat=2):
        ports=tuple((c,p) for c,t in enumerate(ts) for p in range(ARITY[t]+1))
        for wiring in matchings(ports):
            N=make_net(list(ts),wiring,2); two_inputs+=1
            for u,v in N.active():
                assert rewrite_components(N,u,v).signature()==rewrite_local(N,u,v).signature();two_steps+=1
    report['two_cell_closed']={"inputs":two_inputs,"enabled_rewrites":two_steps}
    four_inputs=four_steps=0; normal_forms=Counter(); digest=hashlib.sha256()
    ports=tuple((c,p) for c in range(4) for p in range(3))
    def terminals(N):
        ap=N.active()
        if not ap: return {N.signature()}
        answer=set()
        for u,v in ap: answer.update(terminals(rewrite_local(N,u,v)))
        return answer
    for wiring in matchings(ports):
        N=make_net(['d']*4,wiring); four_inputs+=1
        for u,v in N.active():
            assert rewrite_components(N,u,v).signature()==rewrite_local(N,u,v).signature(); four_steps+=1
        forms=terminals(N); assert len(forms)==1
        result=next(iter(forms)); normal_forms[(len(result[0]),result[2])]+=1
        digest.update(repr((N.signature(),result)).encode())
    report['four_delta_cells']={"inputs":four_inputs,"enabled_rewrites":four_steps,
                               "distinct_normal_forms_per_input":1,"sha256":digest.hexdigest(),
                               "normal_form_histogram":[{"agents":a,"loops":c,"count":v}
                                  for (a,c),v in sorted(normal_forms.items())]}
    rng=random.Random(20261002); random_steps=0; rules=Counter(); growth_max=0
    for trial in range(1000):
        C=rng.randrange(2,7); ts=[rng.choice(TYPES) for _ in range(C)]
        ps=[(c,p) for c,t in enumerate(ts) for p in range(ARITY[t]+1)]
        free=rng.randrange(5); free+=(len(ps)+free)%2
        ps += [(-j-1,0) for j in range(free)]
        # Force an initial active pair, then pair remaining ports uniformly.
        ps.remove((0,0));ps.remove((1,0));rng.shuffle(ps)
        wiring=[((0,0),(1,0))]+list(zip(ps[::2],ps[1::2]))
        N=make_net(ts,wiring,rng.randrange(4))
        for step in range(8):
            ap=N.active()
            if not ap: break
            u,v=rng.choice(ap); rules[''.join(sorted((N.cells[u],N.cells[v])))]+=1
            C1=rewrite_components(N,u,v); C2=rewrite_local(N,u,v)
            assert C1.signature()==C2.signature(); N=C1
            random_steps+=1; growth_max=max(growth_max,len(N.cells))
    report['random_full_system']={"initial_nets":1000,"maximum_steps_per_net":8,
                                 "compared_steps":random_steps,"rule_coverage":dict(sorted(rules.items())),
                                 "maximum_live_cells_seen":growth_max}
    A,B=obstruction_examples(); A1=rewrite_local(A,0,1); B1=rewrite_local(B,0,1)
    A2=rewrite_local(A1,2,3)
    assert A2.agent_free() and A2.loops==2 and not B1.active() and len(B1.cells)==2
    report['obstruction']={"A_after_two_steps_agents":len(A2.cells),"A_loops":A2.loops,
                           "B_after_one_step_agents":len(B1.cells),"B_loops":B1.loops,"B_normal":not B1.active()}
    report['source_hashes']={p.name:hashlib.sha256(p.read_bytes()).hexdigest()
                             for p in sorted(Path(__file__).parent.glob('*.py'))}
    report['status']='PASS'
    (out/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'data')
    run(parser.parse_args().output)
