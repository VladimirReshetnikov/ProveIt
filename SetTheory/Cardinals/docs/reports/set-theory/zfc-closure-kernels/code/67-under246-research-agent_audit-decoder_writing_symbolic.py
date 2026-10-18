#!/usr/bin/env python3
"""Writing episode semantics with exact known-symbol cycle elimination."""
import importlib.util,json
from pathlib import Path
from functools import lru_cache
HERE=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('symbolic_writer_base',HERE/'decoder_transducer.py')
wr=importlib.util.module_from_spec(sp);sp.loader.exec_module(wr)
T=wr.T;states=wr.states;bd=wr.bd
cuts=wr.protected|{q for q in states if any(T[q,b][2]==q for b in (0,1))}
calls=0;maximum=0;loops=0
@lru_cache(None)
def execute(q,h,cube,flips):
    global calls,maximum,loops
    calls+=1;maximum=max(maximum,len(cube))
    known=dict(cube)
    if q not in states or q in cuts:
        return bd.leaf(q,h),tuple((i,wr.bit(1-known[i])) for i in flips)
    assert abs(h)<60 and len(cube)<60,(q,h,len(cube),'possible drift')
    key=(q,h,flips)
    if key in active:
        loops+=1
        return bd.leaf(-999,0),()
    active.add(key)
    cases=[]
    for initial in (0,1):
        if h in known and known[h]!=initial:
            cases.append(None);continue
        child=tuple(sorted(cube+((h,initial),))) if h not in known else cube
        b=initial^(h in flips)
        w,d,t=T[q,b]
        newflips=set(flips)
        if w==initial:newflips.discard(h)
        else:newflips.add(h)
        cases.append(execute(t,h+d,child,tuple(sorted(newflips))))
    active.remove(key)
    if cases[0] is None:return cases[1]
    if cases[1] is None:return cases[0]
    lo,hi=cases
    end=bd.choose(h,lo[0],hi[0]);a=dict(lo[1]);b=dict(hi[1]);out={}
    for i in a.keys()|b.keys():
        f=bd.choose(h,a.get(i,wr.variable(i)),b.get(i,wr.variable(i)))
        if f!=wr.variable(i):out[i]=f
    return end,tuple(sorted(out.items()))

summaries={}
for q in sorted(states):
    active=set();summaries[q]=execute(q,0,(),())
groups={}
for q,k in summaries.items():groups.setdefault(k,[]).append(q)
hits=[g for g in groups.values() if len(g)>1]
print(json.dumps(dict(cuts=sorted(cuts),calls=calls,maximum_facts=maximum,
    looping_branches=loops,bdd_nodes=len(bd.nodes),hits=hits),indent=2))
(HERE/'decoder_writing_symbolic_results.json').write_text(json.dumps(dict(cuts=sorted(cuts),
    calls=calls,maximum_facts=maximum,looping_branches=loops,bdd_nodes=len(bd.nodes),hits=hits),indent=2)+'\n')

def summary(q):return summaries[q]
variable=wr.variable
@lru_cache(None)
def depends(q,r):
    seen=set();todo=[q]
    while todo:
        q=todo.pop()
        if q==r:return True
        if q in seen or q not in states or q in cuts:continue
        seen.add(q);todo.extend(T[q,b][2] for b in (0,1))
    return False
@lru_cache(None)
def restrict_summary(q,cube):
    end,output=summary(q)
    end=bd.cube(end,cube)
    output=tuple((i,v) for i,f in output if (v:=bd.cube(f,cube))!=bd.cube(variable(i),cube))
    return end,output
