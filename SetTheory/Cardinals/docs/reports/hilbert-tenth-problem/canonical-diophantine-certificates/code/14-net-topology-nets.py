#!/usr/bin/env python3
"""Two independent exact reducers for Lafont's interaction combinators.

Ports are pairs (cell_id, local_port). Negative cell_id denotes a fixed free
port, with local_port=0. Cell identifiers are persistent, never recycled.
The component reducer retains parallel edges. The local reducer uses only
the four-port kernel or endpoint relocation. Bare loops are counted exactly.
"""
from __future__ import annotations
from collections import defaultdict
from dataclasses import dataclass
from typing import Iterator

TYPES = ('e','g','d')
ARITY = {'e':0,'g':2,'d':2}
Port = tuple[int,int]
@dataclass
class Net:
    cells: dict[int,str]
    mate: dict[Port,Port]
    loops: int = 0
    fresh: int = 0
    def copy(self) -> 'Net':
        return Net(self.cells.copy(),self.mate.copy(),self.loops,self.fresh)
    def check(self):
        if type(self.loops) is not int or self.loops<0: raise ValueError('bad loops')
        if type(self.fresh) is not int or self.fresh<0: raise ValueError('bad fresh counter')
        ports=set()
        for p,q in self.mate.items():
            for endpoint in (p,q):
                if (type(endpoint) is not tuple or len(endpoint)!=2
                    or any(type(x) is not int for x in endpoint)):
                    raise ValueError("ports must be pairs of exact integers")
        for c,t in self.cells.items():
            if type(c) is not int or c<0 or c>=self.fresh or t not in ARITY:
                raise ValueError('bad cell')
            ports.update((c,p) for p in range(ARITY[t]+1))
        for p in self.mate:
            if p[0]<0:
                if p[1]!=0: raise ValueError('bad free port')
                ports.add(p)
        if set(self.mate)!=ports: raise ValueError('missing or extra ports')
        for p,q in self.mate.items():
            if p==q or self.mate.get(q)!=p: raise ValueError('not a perfect matching')
    def signature(self):
        return (tuple(sorted(self.cells.items())),tuple(sorted(self.mate.items())),self.loops,self.fresh)
    def active(self):
        return sorted((c,d) for c in self.cells
                      if (d:=self.mate[(c,0)][0])>c and self.mate[(c,0)][1]==0 and d in self.cells)
    def agent_free(self): return not self.cells

def connect(m: dict, a: Port, b: Port):
    if a==b: raise ValueError('self-pair')
    m[a]=b; m[b]=a

def template(N: Net, u: int, v: int):
    """Return boundary, new cells, RHS edges; boundary uses old port names."""
    N.check()
    if (u,v) not in N.active(): raise ValueError('not an ordered active pair')
    a,b=N.cells[u],N.cells[v]
    B=[(c,p) for c in (u,v) for p in range(1,ARITY[N.cells[c]]+1)]
    fresh=N.fresh; new={}; edges=[]
    if a==b:
        if a!='e':
            perm=(2,1) if a=='g' else (1,2)
            edges=[((u,i),(v,perm[i-1])) for i in (1,2)]
    elif 'e' in (a,b):
        c=v if a=='e' else u
        new={fresh:'e',fresh+1:'e'}
        edges=[((c,i),(fresh+i-1,0)) for i in (1,2)]
    else:
        g=u if a=='g' else v; d=v if a=='g' else u
        new={fresh:'d',fresh+1:'d',fresh+2:'g',fresh+3:'g'}
        edges=[((g,i),(fresh+i-1,0)) for i in (1,2)]
        edges += [((d,j),(fresh+1+j,0)) for j in (1,2)]
        edges += [((fresh+i-1,j),(fresh+1+j,i)) for i in (1,2) for j in (1,2)]
    return B,new,edges

def rewrite_components(N: Net,u: int,v: int) -> Net:
    B,new,rhs=template(N,u,v); O=N.copy()
    del O.cells[u]; del O.cells[v]; O.cells.update(new); O.fresh+=len(new)
    adj=defaultdict(list)
    # Lists deliberately preserve a pair of parallel edges as a 2-edge cycle.
    for p,q in N.mate.items():
        if p<q and {p,q}!={(u,0),(v,0)}:
            adj[p].append(q); adj[q].append(p)
    for p,q in rhs:
        adj[p].append(q); adj[q].append(p)
    internal=set(B); visited=set(); O.mate={}
    for start in sorted(adj):
        if start in visited: continue
        todo=[start]; comp=set()
        while todo:
            p=todo.pop()
            if p in comp: continue
            comp.add(p); todo.extend(adj[p])
        visited.update(comp)
        ends=sorted(comp-internal)
        if not ends:
            assert all(len(adj[p])==2 for p in comp)
            O.loops+=1
        else:
            assert len(ends)==2 and all(len(adj[p])==(2 if p in internal else 1) for p in comp)
            connect(O.mate,*ends)
    O.check(); return O

def rewrite_local(N: Net,u: int,v: int) -> Net:
    B,new,rhs=template(N,u,v); O=N.copy()
    a,b=N.cells[u],N.cells[v]; removed={p for p in N.mate if p[0] in (u,v)}
    for p in removed: O.mate.pop(p)
    del O.cells[u]; del O.cells[v]; O.cells.update(new); O.fresh+=len(new)
    Bset=set(B)
    if a==b and a!='e':
        from certificates import JDELTA,JGAMMA,loop_witness,EDGES,ename
        J=JGAMMA if a=='g' else JDELTA
        M={e for e in EDGES if N.mate[B[e[0]]]==B[e[1]]}
        W=loop_witness(M,J)
        for i,j in EDGES:
            if W['g'+ename(i,j)]: connect(O.mate,N.mate[B[i]],N.mate[B[j]])
        O.loops+=W['cycles']
    elif a!=b:
        # Endpoint relocation. All RHS boundary endpoints attach to new principals.
        rho={p:q for p,q in rhs if p in Bset}
        for p in B:
            old=N.mate[p]; dst=rho[old] if old in Bset else old
            connect(O.mate,rho[p],dst)
        for p,q in rhs:
            if p not in Bset: connect(O.mate,p,q)
    O.check(); return O

def matchings(points: tuple) -> Iterator[list[tuple]]:
    if not points:
        yield []; return
    a=points[0]
    for i in range(1,len(points)):
        b=points[i]; rest=points[1:i]+points[i+1:]
        for M in matchings(rest): yield [(a,b)]+M

def make_net(types: list[str], wires: list[tuple[Port,Port]], loops=0) -> Net:
    mate={}
    for p,q in wires:
        if p in mate or q in mate: raise ValueError('duplicate endpoint')
        connect(mate,p,q)
    N=Net(dict(enumerate(types)),mate,loops,len(types)); N.check(); return N

def obstruction_examples():
    ans=[]
    for W in ([[0,3],[1,7],[2,9],[4,10],[5,6],[8,11]],
              [[0,3],[1,7],[2,9],[4,10],[5,8],[6,11]]):
        ans.append(make_net(['d']*4,[(divmod(a,3),divmod(b,3)) for a,b in W]))
    return ans
