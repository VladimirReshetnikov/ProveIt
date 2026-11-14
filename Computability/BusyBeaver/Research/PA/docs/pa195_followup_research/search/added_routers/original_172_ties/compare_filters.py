#!/usr/bin/env python3
"""Reproduce the six C++/Python complete router-set comparisons."""
import itertools,json,os,sys,time
from pathlib import Path
D=Path(__file__).resolve().parent
if len(sys.argv)!=2:raise SystemExit('Usage: compare_filters.py /path/to/pa195_conpa/pa195')
os.environ['PA195_REFERENCE']=sys.argv[1]
import router_fast_snapshot as r
old1,old2=r.one_router_candidates,r.two_router_candidates
from cpp_router_filter import install
install(r)
symbols=json.loads((D/'input/symbols.json').read_text());symbols=[tuple(x)if isinstance(x,list)else x for x in symbols]
seeds=json.loads((D/'input/seeds.json').read_text())['checks'];receipt=[]
for index in (0,20,22):
    seed=seeds[index];doc=json.loads((D/'input'/seed['source']).read_text().splitlines()[seed['line']]);trees=[]
    def at(i):return symbols[-1-i]if i<0 else trees[i]
    for a,b in doc['rules']:trees.append((at(a),at(b)))
    raw,_,_=r.c.build(trees[doc['root']]);shape={q:None for q,_ in raw if q!=74}
    for helpers,old,new in [(1,old1,r.one_router_candidates),(2,old2,r.two_router_candidates)]:
        tick=time.time();a=old(raw,shape);old_time=time.time()-tick
        tick=time.time();b=new(raw,shape);new_time=time.time()-tick
        def keys(x):
            if helpers==1:return {tuple(h)for h,upper in x['hits']}
            return {tuple(sorted((tuple(ha),tuple(hb))))for aa,bb,upper in x['hits']for ha,hb in itertools.product(aa,bb)}
        if keys(a)!=keys(b):raise ValueError((index,helpers,'different concrete router sets'))
        for key in ('best_optimistic','router_signatures','target_folds'):
            if a[key]!=b[key]:raise ValueError((index,helpers,key,a[key],b[key]))
        row={'grammar':index,'helpers':helpers,'original_seconds':old_time,'cpp_seconds':new_time,'complete_concrete_router_sets_equal':True,'concrete_hits':len(keys(a)),'best_optimistic':a['best_optimistic']}
        receipt.append(row);print(json.dumps(row),flush=True)
(D/'cpp_filter_comparison.json').write_text(json.dumps(receipt,indent=2)+'\n')
