"""Exact weighted-median solution on forests of parallel-edge bundles.

Self-loops are constant terms. Every non-loop bundle is optimized independently;
acyclicity makes the independently chosen potential differences compatible.
"""
from collections import defaultdict,Counter


def forest_solution(gaps):
    vertices={x for u,v,_ in gaps for x in (u,v)}
    bundles=defaultdict(list); dual={}; value=0
    for (u,v,e),w in gaps.items():
        if u==v:
            dual[(u,v,e)]=w*((e>0)-(e<0)); value+=w*abs(e)
        else:
            a,b=sorted((u,v)); orientation=1 if u==a else -1
            bundles[(a,b)].append(((u,v,e),w,orientation,orientation*e))
    parent={v:v for v in vertices}
    def root(v):
        while parent[v]!=v:
            parent[v]=parent[parent[v]]; v=parent[v]
        return v
    for a,b in sorted(bundles):
        x,y=root(a),root(b)
        if x==y: return None
        parent[x]=y
    adj=defaultdict(list)
    for (a,b),entries in sorted(bundles.items()):
        histogram=Counter()
        for _,w,_,t in entries: histogram[t]+=w
        total=sum(histogram.values()); cumulative=0
        for median in sorted(histogram):
            cumulative+=histogram[median]
            if 2*cumulative>=total: break
        adj[a].append((b,median)); adj[b].append((a,-median))
        imbalance=0; zero=[]
        for key,w,orientation,t in entries:
            value+=w*abs(t-median)
            if t==median: zero.append((key,w,orientation))
            else:
                directed=w*((t>median)-(t<median)); imbalance+=directed
                dual[key]=orientation*directed
        need=-imbalance
        for key,w,orientation in zero:
            directed=max(-w,min(w,need)); dual[key]=orientation*directed; need-=directed
        if need: raise AssertionError('median failed dual feasibility')
    z={}
    for start in sorted(vertices):
        if start in z: continue
        z[start]=0; todo=[start]
        while todo:
            u=todo.pop()
            for v,delta in adj[u]:
                if v not in z: z[v]=z[u]+delta; todo.append(v)
    return z,dual,value
