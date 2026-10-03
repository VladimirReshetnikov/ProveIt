#!/usr/bin/env python3
"""Literal periodic Z^3 circuit router. No path-finding or upstream code.

Every primitive port is used by at most one edge. Edge translates are indexed by
source cell (x,t); (dx,dt) is either (0,0) or (k,1), -2 <= k <= 2.
Supports are represented modulo (7B,4B,336M+84). Missing sites have height zero.
"""
from __future__ import annotations
from collections import Counter, defaultdict
from dataclasses import dataclass
from itertools import product
import argparse, json

STEP=((1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1))

def require(condition, detail="verification failed"):
    if not condition:
        raise AssertionError(detail)

@dataclass(frozen=True)
class Edge:
    a: int
    ap: str
    b: int
    bp: str
    dx: int = 0
    dt: int = 0

PORTS={"AND":("L","R","B"),"OR":("L","R","B"),
       "FORK":("L","R","B"),"WIRE":("L","R"),"DIODE":("L","R")}

def primitive(kind):
    require(kind in PORTS, 'periodic_router.py: invariant at original line 29')
    h={(u,0,0):5 for u in range(-12,13)}
    if kind in ("AND","OR","FORK"):
        h.update({(0,v,0):5 for v in range(-12,0)})
    if kind in ("AND","OR"):
        h[(0,0,0)]=4 if kind=="AND" else 5
        for sign in (-1,1):
            h[(sign*4,0,0)]=4
            h[(sign*4,1,0)]=5
            h[(sign*5,1,0)]=5
    if kind=="DIODE":
        h[(0,0,0)]=4
        h[(-1,1,0)]=5
        h[(0,1,0)]=5
    return h

def port(i,p):
    c=24+48*i
    return {"L":(c-12,24),"R":(c+12,24),"B":(c,12)}[p]

def segment(a,b):
    delta=[b[i]-a[i] for i in range(3)]
    nz=[i for i,d in enumerate(delta) if d]
    require(len(nz) <= 1, (a, b))
    if not nz:
        yield a
        return
    i=nz[0]; d=1 if delta[i]>0 else -1
    for j in range(abs(delta[i])+1):
        q=list(a);q[i]+=d*j
        yield tuple(q)

def corners(n,m,e,edge,x,t):
    B=48*(n+1)
    H=64+12*(e+m*((x%7)+7*(t%4)))
    au,av=port(edge.a,edge.ap)
    bu,bv=port(edge.b,edge.bp)
    ax,ay=x*B+au,t*B+av
    bx,by=(x+edge.dx)*B+bu,(t+edge.dt)*B+bv
    Y=t*B+B//2
    return [(ax,ay,0),(ax,ay,H),(ax+4,ay,H),(ax+4,Y,H),
            (bx+4,Y,H),(bx+4,by,H),(bx,by,H),(bx,by,0)]

def route(n,m,e,edge,x,t):
    cs=corners(n,m,e,edge,x,t)
    for j,(a,b) in enumerate(zip(cs,cs[1:])):
        for k,q in enumerate(segment(a,b)):
            if j==0 or k:
                yield q

def compile_support(kinds,edges,check_ownership=True):
    n=len(kinds);m=len(edges)
    require(n >= 1 and m >= 1, 'periodic_router.py: invariant at original line 81')
    used=set()
    for e in edges:
        require(e.dx == e.dt == 0 or (e.dt == 1 and -2 <= e.dx <= 2), 'periodic_router.py: invariant at original line 84')
        for i,p in ((e.a,e.ap),(e.b,e.bp)):
            require(0 <= i < n and p in PORTS[kinds[i]], 'periodic_router.py: invariant at original line 86')
            require((i, p) not in used, ('port used twice', i, p))
            used.add((i,p))
    B=48*(n+1); periods=(7*B,4*B,336*m+84)
    norm=lambda p:tuple(p[i]%periods[i] for i in range(3))
    support={};owners=defaultdict(set)
    def put(p,h,owner):
        p=norm(p)
        require(p not in support or support[p] == h, ('height conflict', p))
        support[p]=h
        if check_ownership:owners[p].add(owner)
    for x,t in product(range(7),range(4)):
        for i,kind in enumerate(kinds):
            for p,h in primitive(kind).items():
                put((x*B+24+48*i+p[0],t*B+24+p[1],p[2]),h,("g",x,t,i))
        for j,e in enumerate(edges):
            for p in route(n,m,j,e,x,t):
                put(p,5,("e",x,t,j))
    return support,owners,periods

def check(kinds,edges):
    support,owners,periods=compile_support(kinds,edges)
    norm=lambda p:tuple(p[i]%periods[i] for i in range(3))
    outside=Counter();max_degree=0;bad_adjacencies=[]
    # Every overlap is exactly one wire/gate port. Other adjacencies must have
    # a shared owner: this catches nonconsecutive self-touch separately below.
    for p,os in owners.items():
        require(len(os) <= 2, ('multiple overlap', p, os))
        if len(os)==2:
            require({o[0] for o in os} == {'g', 'e'}, ('invalid overlap', p, os))
    for p in support:
        deg=0
        for d in STEP:
            q=norm(tuple(p[i]+d[i] for i in range(3)))
            if q in support:
                deg+=1
                if not (owners[p]&owners[q]):
                    bad_adjacencies.append((p,q,owners[p],owners[q]))
            else:outside[q]+=1
        max_degree=max(max_degree,deg)
    require(not bad_adjacencies, bad_adjacencies[:5])
    require(max_degree <= 3, max_degree)
    leakage=max(outside.values(),default=0)
    require(leakage <= 2, (leakage, [p for p, c in outside.items() if c > 2][:10]))
    # Check each path itself is induced, modulo all three periods.
    n=len(kinds);m=len(edges)
    for x,t in product(range(7),range(4)):
        for j,e in enumerate(edges):
            ps=[norm(p) for p in route(n,m,j,e,x,t)]
            require(len(set(ps)) == len(ps), ('self-overlap', j, x, t))
            pos={p:i for i,p in enumerate(ps)}
            for i,p in enumerate(ps):
                for d in STEP:
                    q=norm(tuple(p[k]+d[k] for k in range(3)))
                    if q in pos:require(abs(pos[q] - i) == 1, ('self-adjacency', j, x, t, p, q))
    return {"primitives":n,"edges":m,"periods":periods,
            "nonzero_sites":len(support),"maximum_support_degree":max_degree,
            "maximum_offsupport_neighbors":leakage,
            "unintended_adjacencies":0,"induced_routes":True,
            "dense_table_sites":periods[0]*periods[1]*periods[2]}


def examples():
    yield "all_offsets",["WIRE"]*5,[Edge(i,"R",i,"L",i-2,1) for i in range(5)]
    # A finite internal DAG followed by temporal edges. Remaining ports are
    # allowed to be unused; unused tails end within their primitive boxes.
    kinds=["WIRE","FORK","AND","OR","DIODE","WIRE"]
    edges=[Edge(0,"R",1,"L"),Edge(1,"R",2,"L"),Edge(1,"B",3,"L"),
           Edge(2,"B",3,"R"),Edge(3,"B",4,"L"),Edge(4,"R",5,"L"),
           Edge(5,"R",0,"L",-2,1)]
    yield "mixed_internal_temporal",kinds,edges

if __name__=="__main__":
    parser=argparse.ArgumentParser();parser.add_argument("--output")
    args=parser.parse_args()
    result={name:check(kinds,edges) for name,kinds,edges in examples()}
    s=json.dumps(result,indent=2)
    print(s)
    if args.output:
        with open(args.output,"w") as f:f.write(s+"\n")
