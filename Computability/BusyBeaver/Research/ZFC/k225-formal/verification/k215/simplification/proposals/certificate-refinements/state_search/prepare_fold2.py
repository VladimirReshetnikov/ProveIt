#!/usr/bin/env python3
"""Prepare graph-history contexts and row-independent two-row merge screen."""
import argparse, itertools, json, hashlib
from collections import defaultdict
from functools import lru_cache
from pathlib import Path

def read(path):
    T={};start=None
    for l in path.read_text().splitlines():
        if l.startswith('#! start '):start=int(l.split()[-1])
        if not l or l.startswith('#'):continue
        q,b,w,d,z=l.split();T[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(z))
    Q=sorted({q for q,b in T})
    assert len(T)==2*len(Q) and all((q,b) in T for q in Q for b in (0,1))
    assert start in Q
    return T,Q,start

def contexts(T,Q,depth,start):
    inc=defaultdict(list)
    for (q,b),(w,d,z) in T.items():inc[z].append((q,b,w,d))
    @lru_cache(None)
    def pre(q,n):
        if n==0 or q==start:return ((),)
        out=set()
        for p,b,w,d in inc[q]:
            for c in pre(p,n-1):
                c=dict(c)
                if 0 in c and c[0]!=b:continue
                c[0]=w
                out.add(tuple(sorted((h-d,v) for h,v in c.items())))
        return tuple(sorted(out))
    return {q:pre(q,depth)for q in Q}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('table',type=Path);ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--depth',type=int,default=4);ap.add_argument('--steps',type=int,default=45);ap.add_argument('--nodes',type=int,default=200)
    a=ap.parse_args();T,Q,start=read(a.table);C=contexts(T,Q,a.depth,start)
    assert all(-59<=h<=59 for cs in C.values() for c in cs for h,v in c)
    def overlap(c,d):
        c,d=dict(c),dict(d)
        return all(h not in d or d[h]==v for h,v in c.items())
    pairs=[];counts=defaultdict(int)
    for q,r in itertools.combinations(Q,2):
        if start in (q,r):continue
        diff=0
        for b in (0,1):
            def renamed(x):return x[:2]+(q if x[2]==r else x[2],)
            if renamed(T[q,b])==renamed(T[r,b]):continue
            diff+=1
            cq=[c for c in C[q] if dict(c).get(0,b)==b];cr=[c for c in C[r] if dict(c).get(0,b)==b]
            if not cq or not cr or any(overlap(c,d) for c in cq for d in cr):break
        else:pairs.append((q,r));counts[diff]+=1
    a.out.parent.mkdir(parents=True,exist_ok=True)
    with a.out.open('w')as f:
        print(len(Q),a.steps,a.nodes,file=f)
        for q in Q:print(q,*T[q,0],*T[q,1],file=f)
        print(len(Q),file=f)
        for q in Q:
            print(q,len(C[q]),file=f)
            for c in C[q]:print(len(c),*(x for t in c for x in t),file=f)
        print(len(pairs),file=f)
        for p in pairs:print(*p,file=f)
    meta={'table':str(a.table),'sha256':hashlib.sha256(a.table.read_bytes()).hexdigest(),'states':len(Q),'start':start,'context_depth':a.depth,'max_steps':a.steps,'max_nodes':a.nodes,'eligible_pairs_by_differing_rows':dict(counts),'scope':'Each changed row block avoids the other changed row; distinct effects require disjoint history contexts. This is a restricted synthesis search, not a lower bound.'}
    a.out.with_suffix('.json').write_text(json.dumps(meta,indent=2)+'\n');print(json.dumps(meta))
if __name__=='__main__':main()
