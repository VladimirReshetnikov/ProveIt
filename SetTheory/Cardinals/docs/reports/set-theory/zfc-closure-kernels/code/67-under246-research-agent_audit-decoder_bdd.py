#!/usr/bin/env python3
"""Search exact read-only episode equivalence by canonical decision diagrams.

This is a discovery script. Each compared episode halts at a designated
terminal state before executing its transition. Tape symbols are arbitrary.
"""
from pathlib import Path
from functools import lru_cache
import json
import sys
import os

SOURCE_ROOT=Path(os.environ.get('ZFC246_SOURCE',str(Path(__file__).resolve().parents[1]/'sources/context246/zfc-context246')))
SRC=SOURCE_ROOT/'machine/zfc_prefix246_old.tm'
T={}
for line in SRC.read_text().splitlines():
    if line and not line.startswith('#'):
        q,b,w,d,t=line.split()
        T[int(q),int(b)]=int(w),(-1 if d=='L' else 1),int(t)

nodes=[]
intern={}
def make(key):
    if key not in intern:
        intern[key]=len(nodes)
        nodes.append(key)
    return intern[key]
def leaf(q,h):return make(('leaf',q,h))
def node(v,l,r):
    if l==r:return l
    assert all(nodes[c][0]=='leaf' or nodes[c][1]>v for c in (l,r))
    return make(('node',v,l,r))
def rootv(i):return nodes[i][1] if nodes[i][0]=='node' else 1000000
def child(i,v,b):
    a=nodes[i]
    return a[2+b] if a[0]=='node' and a[1]==v else i

@lru_cache(None)
def choose(v,l,r):
    if l==r:return l
    u=min(v,rootv(l),rootv(r))
    if u==v:return node(v,child(l,v,0),child(r,v,1))
    return node(u,choose(v,child(l,u,0),child(r,u,0)),
                  choose(v,child(l,u,1),child(r,u,1)))

@lru_cache(None)
def shift(i,d):
    a=nodes[i]
    if a[0]=='leaf':return leaf(a[1],a[2]+d)
    return node(a[1]+d,shift(a[2],d),shift(a[3],d))

@lru_cache(None)
def restrict(i,v,b):
    a=nodes[i]
    if a[0]=='leaf' or a[1]>v:return i
    if a[1]==v:return a[2+b]
    return node(a[1],restrict(a[2],v,b),restrict(a[3],v,b))

pure={q for q,b in T if all(T[q,b][0]==b for b in (0,1))}
cuts={q for q in pure if any(T[q,b][2]==q for b in (0,1))}
cuts.update(map(int,sys.argv[1:]))
# Break the remaining graph cycles, which need not correspond to actual tape
# loops; treating a cutpoint as a terminal only loses candidate comparisons.
color={}
def visit(q):
    if q not in pure or q in cuts:return
    color[q]=1
    for b in (0,1):
        r=T[q,b][2]
        if r not in pure or r in cuts:continue
        if color.get(r)==1:cuts.add(r)
        elif not color.get(r):visit(r)
    color[q]=2
for q in sorted(pure):
    if q not in color:visit(q)

@lru_cache(None)
def summary(q):
    if q not in pure or q in cuts:return leaf(q,0)
    a=[]
    for b in (0,1):
        w,d,t=T[q,b]
        assert w==b
        a.append(shift(summary(t),d))
    return choose(0,*a)

groups={}
for q in sorted(Tq:={q for q,b in T}):
    groups.setdefault(summary(q),[]).append(q)
equivs=[qs for qs in groups.values() if len(qs)>1]
contextual=[]
@lru_cache(None)
def depends(r,q):
    if r==q:return True
    if r not in pure or r in cuts:return False
    return any(depends(T[r,b][2],q) for b in (0,1))
incoming={q:[] for q in Tq}
for (q,b),(w,d,t) in T.items():
    if t in incoming:incoming[t].append((q,b,w,d))
@lru_cache(None)
def histories(q,k):
    if not k:return ((),)
    out=set()
    for s,b,w,d in incoming[q]:
        for pairs in histories(s,k-1):
            a=dict(pairs)
            if 0 in a and a[0]!=b:continue
            a[0]=w
            out.add(tuple(sorted((i-d,v) for i,v in a.items())))
    return tuple(sorted(out))
@lru_cache(None)
def cube(i,pairs):
    for v,b in pairs:i=restrict(i,v,b)
    return i
for q in sorted(Tq & pure - cuts):
    if not incoming[q]:continue
    for r in sorted(Tq - {q}):
        if all(restrict(summary(q),-d,w)==restrict(summary(r),-d,w)
            for s,b,w,d in incoming[q]):
            contextual.append(dict(remove=q,replace=r,incoming=incoming[q]))
index={}
for w in (0,1):
    for d in (-1,1):
        for r in sorted(Tq):
            key=w,restrict(shift(summary(r),d),0,w)
            index.setdefault(key,[]).append((d,r))
reversals=[]
for q in sorted(Tq & pure - cuts):
    if not incoming[q]:continue
    entries=[]
    for s,b,w,d in incoming[q]:
        k=w,restrict(shift(summary(q),d),0,w)
        opts=[(dd,r) for dd,r in index.get(k,[]) if r!=q and not depends(r,q)]
        if not opts:break
        entries.append(dict(source=s,read=b,old=[w,d,q],alternatives=opts))
    else:reversals.append(dict(remove=q,replacements=entries))
deep=[]
for depth in (2,3,4,5,6,8,10):
    found=[]
    for q in sorted(Tq & pure - cuts):
        hs=histories(q,depth)
        if not hs:continue
        sq=summary(q)
        first=hs[0]
        for r in sorted(Tq - {q}):
            if depends(r,q):continue
            sr=summary(r)
            if cube(sq,first)!=cube(sr,first):continue
            if all(cube(sq,c)==cube(sr,c) for c in hs[1:]):
                found.append(dict(remove=q,replace=r,contexts=len(hs)))
    deep.append(dict(depth=depth,candidates=found,max_history_count=max(len(histories(q,depth)) for q in Tq)))
    if found:break
print(json.dumps(dict(readonly_states=len(pure),cuts=sorted(cuts),
    bdd_nodes=len(nodes),equivalences=equivs,contextual=contextual,reversals=reversals,deep=deep),indent=2))
Path(__file__).with_suffix('.json').write_text(json.dumps(dict(readonly_states=len(pure),
    cuts=sorted(cuts),bdd_nodes=len(nodes),equivalences=equivs,contextual=contextual,reversals=reversals,deep=deep),indent=2)+'\n')
