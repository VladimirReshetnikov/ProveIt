#!/usr/bin/env python3
"""AX reassociation reducing six-zero paths without changing macro word."""
import sys,time,random,math,json,functools
from pathlib import Path
from rotate_search import *

def rawpaths(t,p=''):
    if isinstance(t,str):yield from rawpaths(DEFS[t],p);return
    if isinstance(t[0],str) and t[0].startswith('.'):
        yield p;return
    yield from rawpaths(t[0],p+'0');yield from rawpaths(t[1],p+'1')

RP={v:tuple(rawpaths(k)) for k,v in TOKENS.items()}
RP['i']=('',);RP['B']=('',)

@functools.lru_cache(maxsize=300000)
def summary(t,z=0):
    if isinstance(t,str):
        return sum('000000' in '0'*z+p for p in RP[t])
    a,b=t
    if z>=6:return sum(len(RP[x]) for x in expand(t))
    return summary(a,z+1)+summary(b,0)

@functools.lru_cache(maxsize=100000)
def maxheight(t):
    if isinstance(t,str):return max(map(len,RP[t]))
    return 1+max(map(maxheight,t))

if __name__=='__main__':
    rng=random.Random(742982);base=tree('x67')
    def netcost(t):
        ns=nodes(t)
        return len(ns)-int(('i','i') in ns)-int((('i','i'),('i','i')) in ns)
    if len(sys.argv)>2:
        d=json.loads(Path(sys.argv[2]).read_text());rr=d['rules']
        def get(q):
            if q not in rr:return q
            return tuple(map(get,rr[q]))
        base=get(d['root'])
    best=(netcost(base),summary(base));besttree=base
    budget=int(sys.argv[1]) if len(sys.argv)>1 else 1000000
    t=base;n,b=best;score=n+.1*b;start=time.time()
    print('baseline',n,b,'height',maxheight(base),flush=True)
    pareto={}
    for it in range(budget):
        if it%20000==0:
            t=besttree;n,b=best;score=n+.1*b
        ps=paths(t);p,q=rng.choice(ps);a,b=q
        if rng.randrange(2):
            if not isinstance(a,tuple):continue
            u,v=a;new=(u,(v,b))
        else:
            if not isinstance(b,tuple):continue
            u,v=b;new=((a,u),v)
        cand=replace(t,q,new) if rng.random()<.6 else replace_one(t,p,new)
        n=netcost(cand);bad=summary(cand);h=maxheight(cand)
        candscore=n+.1*bad+max(0,h-30)
        temp=.35*(1-(it%20000)/20000)+.02
        if candscore<=score or rng.random()<math.exp((score-candscore)/temp):t=cand;score=candscore
        if n<=68 and bad<best[1] and h<=30:
            best=n,bad;besttree=cand;assert expand(cand)==WORD
            output(cand,Path(__file__).with_name('net_safe_best.json'))
            print('best',n,bad,'iter',it,'secs',round(time.time()-start,3),'height',h,flush=True)
            if bad==0:break
        if n<=70 and bad<pareto.get(n,10000) and h<=30:
            pareto[n]=bad
            output(cand,Path(__file__).with_name(f'net_safe_{n}_best.json'))
    print('done',best,'pareto',pareto,'secs',round(time.time()-start,3),flush=True)
