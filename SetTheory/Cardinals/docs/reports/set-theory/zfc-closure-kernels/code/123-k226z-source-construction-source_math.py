#!/usr/bin/env python3
"""Exact source graph and closed rotation checker.

Adapted from ProveIt build_zfc235.py at commit0128d662fd46f72dc84505176ae8ec28affb2d9d.
The original license and attribution are preserved under licenses/.
"""
from functools import cache
from collections import defaultdict
DISPATCH=84

def require(p,m):
    if not p:raise ValueError(m)

def is_leaf(t):return isinstance(t[0],str)

def tree(rows):
    trie={};seen=set()
    for p,o,r in rows:
        require(p and not(set(p)-{'0','1'}) and p not in seen,'Malformed/duplicate source path');seen.add(p)
        require(o in('CI','CD','CB','CC','CH'),'Source opcode')
        require((o=='CH' and r is None) or (o!='CH' and type(r) is int and r>=0),'Source operand')
        require(o not in('CI','CD') or r<9,'Source register')
        at=trie
        for b in p:
            require('leaf' not in at,'Source is not prefix-free');at=at.setdefault(b,{})
        require(not at,'Repeated/overlapping source leaf');at['leaf']=(o,r)
    def visit(n):
        if 'leaf' in n:
            require(set(n)=={'leaf'},'Leaf with children');return n['leaf']
        require(set(n)=={'0','1'},'Non-full source tree');return visit(n['0']),visit(n['1'])
    return visit(trie)

def sites(t,p=''):
    if is_leaf(t):return [(p,*t)]
    return sites(t[0],p+'0')+sites(t[1],p+'1')

@cache
def boundary(t):
    if is_leaf(t):
        o,r=t
        return (1,0,False) if o=='CD' else (r,0,False) if o=='CB' else (0,r,False) if o=='CC' else (0,0,o=='CH')
    a,b=map(boundary,t)
    return max(max(a[0]-1,0),b[0]),max(a[1],max(b[1]-1,0)),a[2] or b[2]

def graph(rows):
    ordered=sorted(tuple(x) for x in rows);leaves={p:i for i,(p,o,r) in enumerate(ordered)}
    prefixes={p[:k] for p in leaves for k in range(len(p))};mx=max(map(len,leaves))
    require(not(set(leaves)&prefixes),'Source is not prefix-free')
    require(all(p+c in prefixes or p+c in leaves for p in prefixes for c in'01'),'Source is not full')
    def locate(p):
        word=p+'0'*mx
        for k in range(1,mx+1):
            if word[:k] in leaves:
                require('1' not in p[k:],'Noncanonical successor suffix');return leaves[word[:k]]
        raise ValueError('Unresolved source successor')
    def inc(p):return format((int(p,2)+1)%(1<<len(p)),'0'+str(len(p))+'b') if p else ''
    def cut(p,c,k):
        if k==0:return p
        pos=[i for i,b in enumerate(p) if b==c]
        return p[:pos[-k]] if len(pos)>=k else ''
    gg=[]
    for p,o,r in ordered:
        if o=='CI':gg.append(('INC',r,locate(inc(p))))
        elif o=='CD':gg.append(('DEC',r,locate(inc(p)),locate(inc(cut(p,'0',1)))))
        elif o=='CB':gg.append(('JUMP',locate(inc(cut(p,'0',r)))))
        elif o=='CC':gg.append(('JUMP',locate(cut(p,'1',r))))
        else:gg.append(('HALT',))
    return ordered,gg,locate('')

def metrics(t):
    live=set()
    def visit(n):
        if n in live:return
        live.add(n)
        if not is_leaf(n):visit(n[0]);visit(n[1])
    visit(t);ss=sites(t)
    return dict(dag_nodes=len(live),leaf_occurrences=len(ss),maximum_depth=max(len(p) for p,o,r in ss),
                maximum_zero_run=max(len(z) for p,o,r in ss for z in p.split('1')))

def decoder_mapping(root,t):
    m={};inverse=defaultdict(set)
    def visit(n,q):
        if is_leaf(n):return
        if n in m:require(m[n]==q,'Inconsistent source decoder mapping');return
        m[n]=q;inverse[q].add(n)
        for b in(0,1):
            w,d,z=t[q,b]
            if (w,d)==(b,1):visit(n[b],z)
    visit(root,DISPATCH);return m,inverse

def stage(root,t,q,q2,direction):
    mapping,inverse=decoder_mapping(root,t)
    require(len(inverse[q])==1 and len(inverse[q2])==1,'Ambiguous decoder states')
    n=next(iter(inverse[q]));child=n[1 if direction=='left' else 0]
    require(not is_leaf(child) and mapping[child]==q2,'Unexpected child state')
    require(all(t[p,b][:2]==(b,1) for p in(q,q2) for b in(0,1)),'A rotation row is not a pure decoder step')
    incoming=[(p,b) for(p,b),(w,d,z) in t.items() if z==q2]
    require(incoming==[(q,1 if direction=='left' else 0)],'Intermediate decoder state has another incoming row')
    if direction=='left':a,(b,c)=n;replacement=(a,b),c
    else:(a,b),c=n;replacement=a,(b,c)
    chunks=(a,b,c)
    require(all(boundary(v)==(0,0,False) for v in chunks),'A source chunk has escaping control or a halt')
    paths=[]
    def occurrences(v,p=''):
        if v==n:paths.append(p);return
        if not is_leaf(v):occurrences(v[0],p+'0');occurrences(v[1],p+'1')
    occurrences(root)
    @cache
    def replace(v):
        if v==n:return replacement
        return v if is_leaf(v) else (replace(v[0]),replace(v[1]))
    newroot=replace(root);new=dict(t)
    if direction=='left':
        qa=t[q,0][2];qb=t[q2,0][2];qc=t[q2,1][2]
        new[q,0]=(0,1,q2);new[q,1]=(1,1,qc);new[q2,0]=(0,1,qa);new[q2,1]=(1,1,qb)
    else:
        qa=t[q2,0][2];qb=t[q2,1][2];qc=t[q,1][2]
        new[q,0]=(0,1,qa);new[q,1]=(1,1,q2);new[q2,0]=(0,1,qb);new[q2,1]=(1,1,qc)
    cert=dict(direction=direction,outer_state=q,inner_state=q2,paths=paths,
              chunk_leaf_counts=[len(sites(v)) for v in chunks],chunk_boundaries=[boundary(v) for v in chunks],
              literal_edits=[dict(row=[p,b],before=t[p,b],after=new[p,b]) for p,b in sorted(new) if t[p,b]!=new[p,b]],
              metrics=metrics(newroot))
    return newroot,new,cert
