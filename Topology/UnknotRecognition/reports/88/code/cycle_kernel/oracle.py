"""Exponential small-width oracles, deliberately separate from kernel construction.

The transfer oracle enumerates tile colorings. The graph oracle eliminates graph
vertices. Neither routine is a production complexity claim.
"""
from itertools import product
from .model import Graph

def mul4(a,b,k):
    c=[k+1]*4
    for i,x in enumerate(a):
        if x>k:continue
        for j,y in enumerate(b):
            if y<=k and x+y<c[i|j]:c[i|j]=x+y
    return tuple(c)

def enumerate_signature(g:Graph,k=3,max_vertices=18):
    if g.n>max_vertices:raise ValueError('coloring oracle cap')
    w=len(g.left);z=1<<w;out=[[[k+1]*4 for _ in range(z)] for _ in range(z)]
    for mask in range(1<<g.n):
        c=0;f=0
        for a,b in g.edges:
            x=(mask>>a)&1;y=(mask>>b)&1
            if x!=y:c+=1
            else:f|=1<<x
        if c>k:continue
        a=sum(((mask>>v)&1)<<i for i,v in enumerate(g.left))
        b=sum(((mask>>v)&1)<<i for i,v in enumerate(g.right))
        out[a][b][f]=min(out[a][b][f],c)
    return out

def sig_product(a,b,k=3):
    z=len(a);o=[[[k+1]*4 for _ in range(z)] for _ in range(z)]
    for x in range(z):
        for y in range(z):
            if min(a[x][y])>k:continue
            for t in range(z):
                if min(b[y][t])>k:continue
                q=mul4(a[x][y],b[y][t],k)
                for f in range(4):o[x][t][f]=min(o[x][t][f],q[f])
    return o

def signature_power(g:Graph,n:int,k=3):
    if len(g.left)>4:raise ValueError('transfer oracle width cap')
    a=enumerate_signature(g,k);r=None
    while n:
        if n&1:r=a if r is None else sig_product(r,a,k)
        n>>=1
        if n:a=sig_product(a,a,k)
    return r

def graph_signature(g:Graph,k=3,max_bag=18):
    """Exact variable elimination, retaining every external coloring and mark."""
    boundary=tuple(dict.fromkeys(g.left+g.right));bs=set(boundary)
    factors=[]
    for a,b in g.edges:
        vs=tuple(sorted({a,b}));table=[]
        for mask in range(1<<len(vs)):
            x=(mask>>vs.index(a))&1;y=(mask>>vs.index(b))&1
            f=[k+1]*4
            if x!=y:f[0]=min(1,k+1)
            else:f[1<<x]=0
            table.append(tuple(f))
        factors.append((vs,table))
    remain=set(range(g.n))-bs
    while remain:
        neighborhoods={v:{v} for v in remain}
        for vs,tab in factors:
            for v in set(vs)&remain:neighborhoods[v].update(vs)
        v=min(remain,key=lambda x:(len(neighborhoods[x]),x));remain.remove(v)
        use=[f for f in factors if v in f[0]]
        factors=[f for f in factors if v not in f[0]]
        if not use:continue
        allvs=tuple(sorted(set().union(*(set(f[0]) for f in use))))
        if len(allvs)>max_bag:raise ValueError('elimination oracle bag cap')
        outvs=tuple(x for x in allvs if x!=v);oi={x:i for i,x in enumerate(outvs)}
        tab=[]
        for mask in range(1<<len(outvs)):
            best=[k+1]*4
            for bit in (0,1):
                val=(0,k+1,k+1,k+1)
                for vs,old in use:
                    mm=sum((bit if x==v else (mask>>oi[x])&1)<<i for i,x in enumerate(vs))
                    val=mul4(val,old[mm],k)
                for f in range(4):best[f]=min(best[f],val[f])
            tab.append(tuple(best))
        factors.append((outvs,tab))
    z=1<<len(g.left);out=[[[k+1]*4 for _ in range(z)] for _ in range(z)]
    for mask in range(1<<len(boundary)):
        colors={x:(mask>>i)&1 for i,x in enumerate(boundary)};val=(0,k+1,k+1,k+1)
        for vs,tab in factors:
            mm=sum(colors[x]<<i for i,x in enumerate(vs));val=mul4(val,tab[mm],k)
        a=sum(colors[x]<<i for i,x in enumerate(g.left));b=sum(colors[x]<<i for i,x in enumerate(g.right))
        out[a][b]=list(val)
    return out
