#!/usr/bin/env python3
"""Exact read-only episode search resolving inconsistent graph cycles.

This executor retains the symbols already read. It can therefore follow
cycles in the control graph whose tape-symbol conditions are inconsistent.
Only the genuine scanning loops are treated as macro boundaries.
"""
import importlib.util,sys,json
from pathlib import Path
from functools import lru_cache
HERE=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('pure_bdd_no_cuts',HERE/'decoder_bdd.py')
bd=importlib.util.module_from_spec(sp);sp.loader.exec_module(bd)
T=bd.T;states=bd.Tq;pure=bd.pure
cuts={q for q in pure if any(T[q,b][2]==q for b in (0,1))}
calls=0;maximum=0;loops=0
@lru_cache(None)
def execute(q,h,cube):
    global calls,maximum,loops
    calls+=1;maximum=max(maximum,len(cube))
    if q not in pure or q in cuts:return bd.leaf(q,h)
    assert abs(h)<60 and len(cube)<60,(q,h,len(cube),'possible drifting cycle')
    key=(q,h)
    if key in active:
        loops+=1
        return bd.leaf(-999,0)
    active.add(key)
    known=dict(cube)
    branches=[]
    for b in (0,1):
        if h in known and known[h]!=b:
            branches.append(None);continue
        child=tuple(sorted(cube+((h,b),))) if h not in known else cube
        w,d,t=T[q,b];assert w==b
        branches.append(execute(t,h+d,child))
    active.remove(key)
    if branches[0] is None:return branches[1]
    if branches[1] is None:return branches[0]
    return bd.choose(h,*branches)
summaries={}
for q in sorted(states):
    active=set()
    summaries[q]=execute(q,0,())
groups={}
for q,i in summaries.items():groups.setdefault(i,[]).append(q)
hits=[g for g in groups.values() if len(g)>1]
print(json.dumps(dict(cuts=sorted(cuts),calls=calls,maximum_facts=maximum,
    looping_branches=loops,bdd_nodes=len(bd.nodes),hits=hits),indent=2))
(HERE/'decoder_symbolic_results.json').write_text(json.dumps(dict(cuts=sorted(cuts),
    calls=calls,maximum_facts=maximum,looping_branches=loops,bdd_nodes=len(bd.nodes),hits=hits),indent=2)+'\n')
