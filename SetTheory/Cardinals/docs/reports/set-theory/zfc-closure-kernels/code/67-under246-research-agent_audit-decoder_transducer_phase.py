#!/usr/bin/env python3
"""Search writing-enabled finite decoder episodes on symbolic phase domains."""
import importlib.util,sys,json
from pathlib import Path
from types import SimpleNamespace
from functools import lru_cache
HERE=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('transducer_search',HERE/'decoder_transducer.py')
wr=importlib.util.module_from_spec(sp);sp.loader.exec_module(wr)
collector=(HERE/'decoder_phase.py').read_text().split('protected={',1)[0]
collector=collector.replace("dec=load('episode_bdd',HERE/'decoder_bdd.py')",'dec=transducer_adapter')
collector=collector.replace('abs(offset)>42','abs(offset)>28').replace('min(c,43)','min(c,29)').replace('abs(offset)<=42','abs(offset)<=28')
env={'__file__':str(HERE/'decoder_phase.py'),'transducer_adapter':SimpleNamespace(
    pure=wr.states,cuts=wr.cuts,Tq=wr.states)}
exec(compile(collector,'affine_symbolic_context_collection','exec'),env)
contexts=env['contexts']
@lru_cache(None)
def bdd_support(i):
    a=wr.bd.nodes[i]
    if a[0]=='leaf':return frozenset()
    return {a[1]}|bdd_support(a[2])|bdd_support(a[3])
supports={}
for q in wr.states:
    end,out=wr.summary(q)
    supports[q]=bdd_support(end)|set(i for i,v in out)
    for i,v in out:supports[q]|=bdd_support(v)

def restricted(q,c):
    return wr.restrict_summary(q,tuple((i,b) for i,b in c if i in supports[q]))
hits=[]
for q in sorted(wr.states-wr.cuts):
    cubes=tuple(contexts[q])
    if not cubes:print('unused',q,flush=True);continue
    for r in sorted(wr.states-{q}):
        if wr.depends(r,q):continue
        if all(restricted(q,c)==restricted(r,c) for c in cubes):
            hit=dict(remove=q,replace=r,contexts=len(cubes));hits.append(hit)
            print('HIT',hit,flush=True)
print(json.dumps(dict(cases=env['checked'],observations=env['observations'],hits=hits),indent=2))
(HERE/'decoder_transducer_phase_results.json').write_text(json.dumps(dict(cases=env['checked'],
    observations=env['observations'],context_counts={q:len(cs) for q,cs in contexts.items()},
    cuts=sorted(wr.cuts),hits=hits),indent=2)+'\n')
