#!/usr/bin/env python3
"""Allow inactive fixed readers to become paid helpers for simultaneous folds."""
from pathlib import Path
import json,collections,functools
import optimize_closed as O

def best_weighted(full,active,options):
    pair_opts=collections.defaultdict(list)
    for q,r,ds in options:pair_opts[q,r].append((q,r,ds))
    pairs=sorted(pair_opts);best=[];bestscore=len(active)//2;tested=0;base=bestscore
    def dfs(i,used,sel):
        nonlocal best,bestscore,tested
        if base-len(sel)-(len(pairs)-i)>=bestscore:return
        if i==len(pairs):
            tested+=1
            mm,mu=O.F.fold(full,sel);sc=len(O.prune(mm))//2
            if sc<bestscore and O.F.check_local(full,sel)[0]:bestscore=sc;best=sel.copy()
            return
        q,r=pairs[i]
        if q not in used and r not in used:
            for item in pair_opts[q,r]:dfs(i+1,used|{q,r},sel+[item])
        dfs(i+1,used,sel)
    dfs(0,set(),[])
    return bestscore,best,tested

@functools.lru_cache(maxsize=10000)
def evaluate(t):
    if O.zero_shape(t)[1]>6:return 1000,0,0,()
    try:full,new,entry=O.make(t,False)
    except ValueError:return 1000,0,0,()
    active=O.prune(full)
    protected={q for q,b in O.S.ENGINE_ROWS}|{full[k][2] for k in O.S.ENGINE_ROWS if k in full}|{0,O.S.ROOT}
    endpoints={q for q,b in active if q not in protected}
    opts=O.F.candidates(full,endpoints,tags_from=active)
    score,selected,tested=best_weighted(full,active,opts)
    return score,len(active)//2,len(selected),tuple(selected)
O.evaluate=evaluate
old_output=O.output
def output(t,path):
    old_output(t,path.with_name(path.stem+'_weighted'+path.suffix))
O.output=output

def validate(t,path):
    full,new,entry=O.make(t,False);score,n,c,sel=evaluate(t)
    mm,mu=O.F.fold(full,sel);mm=O.prune(mm)
    newtree=O.C.replace(O.ROOT,O.RAW['x67'],O.raw(t))
    result=O.C.check(mm,newtree,True)
    path=path.with_name(path.stem+'_weighted'+path.suffix)
    path.with_suffix('.tm').write_text(''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n' for (q,b),(w,d,z) in sorted(mm.items())))
    path.with_suffix('.check.json').write_text(json.dumps(result,indent=2))
    return result
O.validate=validate
if __name__=='__main__':O.main()
