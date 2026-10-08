"""Independent literal checks and a same-harness selected-direction baseline.

The baseline implements the mathematical greedy-unit-cut + exact-line policy,
not the current production scheduler or its adaptive triggering.
"""
from __future__ import annotations
from collections import deque,Counter
from itertools import product
from .slp import Grammar
from .histogram import profile,reduced_image

def free_reduce(word):
    out=[]
    for x in word:
        if out and out[-1]==-x: out.pop()
        else: out.append(x)
    return out

def cyclic_reduce(word):
    out=free_reduce(word); lo=0; hi=len(out)
    while hi-lo>1 and out[lo]==-out[hi-1]: lo+=1; hi-=1
    return out[lo:hi]

def canonical(word):
    w=cyclic_reduce(word)
    return min(tuple(w[i:]+w[:i]) for i in range(len(w))) if w else ()

def substitute(word, images):
    out=[]
    for x in word: out.extend(images.get(x,[x]))
    return cyclic_reduce(out)

def literal_shear(word,a,z):
    out=[]
    def run(e): return [a if e>=0 else -a]*abs(e)
    for x in word:
        if abs(x)==abs(a): out.append(x)
        else: out.extend(run(-z.get(-x,0))+[x]+run(z.get(x,0)))
    return cyclic_reduce(out)

def literal_histogram(word,a):
    positions=[i for i,x in enumerate(word) if abs(x)!=abs(a)]
    if not positions: return len(word),Counter()
    h=Counter(); n=len(word)
    for j,i in enumerate(positions):
        t=positions[(j+1)%len(positions)]; k=(i+1)%n; e=0
        while k!=t:
            e+=1 if word[k]==a else -1; k=(k+1)%n
        h[(word[i],-word[t],e)]+=1
    return len(positions),h

def mincut(n,edges,s,t):
    cap=[[0]*n for _ in range(n)]
    for u,v,w in edges:
        if u!=v: cap[u][v]+=w
    value=0
    while True:
        parent={s:None}; q=deque([s])
        while q and t not in parent:
            u=q.popleft()
            for v,c in enumerate(cap[u]):
                if c>0 and v not in parent: parent[v]=u; q.append(v)
        if t not in parent: return value,set(parent)
        v=t; delta=None
        while v!=s:
            u=parent[v]; delta=cap[u][v] if delta is None else min(delta,cap[u][v]); v=u
        v=t
        while v!=s:
            u=parent[v]; cap[u][v]-=delta; cap[v][u]+=delta; v=u
        value+=delta

def fixed_power(p,t):
    vertices=sorted({x for u,v,_ in p.gaps for x in (u,v)})
    idx={v:i for i,v in enumerate(vertices)}; h={v:0 for v in vertices}; edges=[]
    for (u,v,e),w in p.gaps.items():
        slope=(1 if e>=0 else -1)*min(abs(e),t)
        h[u]+=w*slope; h[v]-=w*slope
        c=w*max(0,t-abs(e))
        if c and u!=v: edges.extend([(idx[u],idx[v],c),(idx[v],idx[u],c)])
    s=len(vertices); sink=s+1; offset=0
    for v,w in h.items():
        if w>=0: edges.append((idx[v],sink,w))
        else: edges.append((s,idx[v],-w)); offset+=w
    flow,side=mincut(sink+1,edges,s,sink)
    labels={v:int(idx[v] in side) for v in vertices}
    value=p.original_length+offset+flow
    assert value==p.value({v:t*x for v,x in labels.items()})
    return value,labels

def first_line_minimum(p,labels):
    h=Counter()
    for (u,v,e),w in p.gaps.items():
        d=labels.get(u,0)-labels.get(v,0)
        if d: h[-e*d]+=w
    if not h: return 0
    total=sum(h.values()); cum=0
    for k in sorted(h):
        cum+=h[k]
        if 2*cum>=total: return max(0,k)
    raise AssertionError

def selected_line_step(g,roots,generators):
    before=sum(g.meta[n].length for n in roots); best=(before,None,None,None)
    for a in sorted(generators):
        p=profile(g,roots,a); value,labels=fixed_power(p,1)
        if value<best[0]: best=(value,a,p,labels)
    if best[1] is None: return g,roots[:],{'gain':0,'power':0}
    _,a,p,labels=best; t=first_line_minimum(p,labels); z={v:t*x for v,x in labels.items()}
    out,new=reduced_image(g,roots,p,z)
    return out,new,{'gain':before-p.value(z),'power':t,'multiplier':a,'potentials':z}

def artin_presentation(strands,braid,max_letters=100000):
    """Meridians pushed through a braid, with closure identifications.

    sigma_i sends (x_i,x_{i+1}) to (x_i x_{i+1} x_i^-1,x_i).
    The inverse convention is checked by inverse-pair tests.
    """
    labels=[[i] for i in range(1,strands+1)]; permutation=list(range(strands))
    for letter in braid:
        i=abs(letter)-1
        if not 0<=i<strands-1: raise ValueError('invalid braid generator')
        x,y=labels[i],labels[i+1]
        inv=lambda w:[-z for z in reversed(w)]
        if letter>0: labels[i],labels[i+1]=free_reduce(x+y+inv(x)),x
        else: labels[i],labels[i+1]=y,free_reduce(inv(y)+x+y)
        permutation[i],permutation[i+1]=permutation[i+1],permutation[i]
        if sum(map(len,labels))>max_letters: raise ValueError('literal presentation cap')
    relators=[cyclic_reduce(w+[-i]) for i,w in enumerate(labels,1)]
    cycles=0; visited=set()
    for i in range(strands):
        if i not in visited:
            cycles+=1; j=i
            while j not in visited: visited.add(j); j=permutation[j]
    return relators,cycles

def eliminate_singletons(words,alive,cap=100000):
    """Exact elementary Tietze preprocessing; source tuples retained in audits."""
    words=[cyclic_reduce(w) for w in words]; alive=set(alive); steps=[]
    while True:
        candidates=[]
        for i,w in enumerate(words):
            counts=Counter(map(abs,w))
            for g,c in counts.items():
                if c==1: candidates.append((len(w),i,g))
        if not candidates: break
        _,i,g=min(candidates); w=words[i]; j=next(j for j,x in enumerate(w) if abs(x)==g)
        rest=w[j+1:]+w[:j]
        replacement=[-x for x in reversed(rest)] if w[j]>0 else rest
        images={g:replacement,-g:[-x for x in reversed(replacement)]}
        new=[[] if k==i else substitute(v,images) for k,v in enumerate(words)]
        if sum(map(len,new))>cap: break
        words=new; alive.remove(g); steps.append({'relation':i,'generator':g})
    return words,sorted(alive),steps
