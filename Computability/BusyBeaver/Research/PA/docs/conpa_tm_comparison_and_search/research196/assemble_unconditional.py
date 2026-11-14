#!/usr/bin/env python3
from pathlib import Path
exec(Path(__file__).with_name('wrapper_search.py').read_text().split('OUT=Path')[0])
from functools import lru_cache
OUT=Path(__file__).resolve().parent/'fused_unconditional';OUT.mkdir(exist_ok=True)
def decode(d):
    if 'terminal' in d:return tuple(d['terminal']) if isinstance(d['terminal'],list) else d['terminal']
    rs=d['rules']
    def rec(x):
        if isinstance(x,list):return tuple(x)
        if x in rs:return tuple(rec(y) for y in rs[x])
        return x
    return rec(d['root'])
random.seed(13713);start=time.time();best=999
candidates=json.loads((OUT/'candidates.json').read_text());candidates.sort(key=lambda c:c['cost'])
for idx,c in enumerate(candidates[:52]):
    parts=list(map(decode,c['parts']));aa=list(map(attrs,parts));n=len(parts)
    @lru_cache(None)
    def splits(i,j,b):
        if i+1==j:return(-1,) if aa[i][1]<=b and aa[i][2]<=6 else ()
        if b<=0:return()
        return tuple(k for k in range(i+1,j) if splits(i,k,b-1) and splits(k,j,6))
    if not splits(0,n,6):continue
    def sample(i,j,b):
        if i+1==j:return parts[i]
        k=random.choice(splits(i,j,b));return(sample(i,k,b-1),sample(k,j,6))
    print('CAND',idx,c['cost'],c['meta'],'parts',n,flush=True)
    localbest=999
    for it in range(20000 if c['cost']<=69 else 5000):
        t=sample(0,n,6);cc=cost(t)
        if cc[0]<localbest:
            localbest=cc[0];print('LOCAL',idx,cc[:3],it,'seconds',time.time()-start,flush=True)
            dd=encode(t);dd['meta']=c['meta'];dd['cost']=cc[:3]
            (OUT/f'assembled_{idx}.json').write_text(json.dumps(dd))
        if cc[0]<best:
            best=cc[0]
            if best<62:check(t,'fused_unconditional')
    print('DONE CAND',idx,localbest,'global',best,'seconds',time.time()-start,flush=True)
