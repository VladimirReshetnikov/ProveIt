#!/usr/bin/env python3
"""Explore exact source subtrees via bounded arithmetic signatures.

Matches are conjecture proposals only; no equivalence is inferred from bounds.
"""
import collections,itertools,json
from functools import cache
from pathlib import Path
BASE=Path(__file__).resolve().parent
SITES=json.loads((BASE/'sites_logical.json').read_text())
LEAVES={p:(k,a) for p,k,a in SITES}
NODES={}
def tree(p):
    if p in LEAVES:return LEAVES[p]
    t=(tree(p+'0'),tree(p+'1'));NODES[p]=t;return t
ROOT=tree('')
def isleaf(t):return isinstance(t[0],str)
@cache
def info(t):
    if isleaf(t):
        op,a=t
        return (1,(1,0) if op=='CD' else (a,0) if op=='CB' else (0,a) if op=='CC' else (0,0),frozenset([a]) if op in ('CI','CD') else frozenset())
    na,(ba,ca),va=info(t[0]);nb,(bb,cb),vb=info(t[1])
    return na+nb,(max(ba-1,bb,0),max(ca,cb-1,0)),va|vb
def leaves(t,p=''):
    if isleaf(t):return [(p,*t)]
    return leaves(t[0],p+'0')+leaves(t[1],p+'1')
def inc(p):
    i=p.rfind('0')
    return p[:i]+'1' if i>=0 else None
def strip(p,b,n):
    while n and p:
        n-=p[-1]==b;p=p[:-1]
    return p
@cache
def cfg(t):
    ss=leaves(t);lookup={p:i for i,(p,*_) in enumerate(ss)}
    def find(p):
        if p is None:return -1
        for j in range(64):
            if p in lookup:return lookup[p]
            p+='0'
        raise ValueError(p)
    rows=[]
    for p,op,a in ss:
        if op=='CI':rows.append((op,a,find(inc(p)),None))
        elif op=='CD':rows.append((op,a,find(inc(p)),find(inc(strip(p,'0',1)))))
        elif op=='CB':rows.append((op,a,find(inc(strip(p,'0',a))),None))
        elif op=='CC':rows.append((op,a,find(strip(p,'1',a)),None))
        else:rows.append((op,a,None,None))
    return rows
def signature(t):
    rows=cfg(t);vs=sorted(info(t)[2]);out=[]
    for ns in itertools.product(range(4),repeat=len(vs)):
        r=[0]*9
        for i,n in zip(vs,ns):r[i]=n
        q=0
        for steps in range(10000):
            if q==-1:break
            op,a,pos,zero=rows[q]
            if op=='CI':r[a]+=1;q=pos
            elif op=='CD':
                if r[a]:r[a]-=1;q=pos
                else:q=zero
            elif op in ('CB','CC'):q=pos
            else:q=-2;break
        else:return None
        out.append((q,tuple(r[i] for i in vs)))
    return tuple(vs),tuple(out)
def main():
    uniq=collections.defaultdict(list)
    for p,t in NODES.items():uniq[t].append(p)
    for p,t in LEAVES.items():uniq[t].append(p)
    pool={t:ps for t,ps in uniq.items() if info(t)[1]==(0,0) and info(t)[0]<=60 and len(info(t)[2])<=3}
    sigs=collections.defaultdict(list)
    for t,ps in pool.items():
        s=signature(t)
        if s is not None:sigs[s].append(t)
    groups=[]
    for ts in sigs.values():
        if len(ts)>1:
            g=[{'leaves':info(t)[0],'locations':pool[t],'tree':t} for t in sorted(ts,key=lambda t:info(t)[0])]
            groups.append(g)
    (BASE/'semantic_groups.json').write_text(json.dumps({'status':'BOUNDED_PROPOSALS_NOT_PROOFS','unique_trees':len(uniq),'closed_pool':len(pool),'groups':groups},indent=2)+'\n')
    print('unique',len(uniq),'pool',len(pool),'groups',len(groups))
    for g in groups:
        for x in g:print(x['leaves'],len(x['locations']),x['locations'][:2],x['tree'])
        print()
if __name__=='__main__':main()
