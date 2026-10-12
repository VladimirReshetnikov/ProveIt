"""Finite undirected multigraphs. Edge occurrences, loops and isolated vertices survive."""
from __future__ import annotations
from dataclasses import dataclass
from typing import Hashable, Iterable

class DSU:
    def __init__(self, n: int): self.p=list(range(n)); self.sz=[1]*n
    def find(self, x: int) -> int:
        while self.p[x]!=x:
            self.p[x]=self.p[self.p[x]]; x=self.p[x]
        return x
    def union(self, a: int, b: int) -> None:
        a,b=self.find(a),self.find(b)
        if a==b:return
        if self.sz[a]<self.sz[b]:a,b=b,a
        self.p[b]=a; self.sz[a]+=self.sz[b]

@dataclass(frozen=True)
class Graph:
    n: int
    edges: tuple[tuple[int,int], ...]
    left: tuple[int,...]=()
    right: tuple[int,...]=()
    def __post_init__(self):
        if type(self.n) is not int or self.n<0:raise ValueError('invalid vertex count')
        for e in self.edges:
            if len(e)!=2 or any(type(v) is not int or not 0<=v<self.n for v in e):
                raise ValueError('invalid edge')
        for ports in (self.left,self.right):
            if len(set(ports))!=len(ports) or any(type(v) is not int or not 0<=v<self.n for v in ports):
                raise ValueError('invalid port list')
    def validate_tile(self) -> None:
        if not self.left or len(self.left)!=len(self.right) or set(self.left)&set(self.right):
            raise ValueError('a tile needs equal, nonempty, disjoint port lists')
    def to_dict(self) -> dict:
        return dict(n=self.n,edges=[list(e) for e in self.edges],left=list(self.left),right=list(self.right))
    @classmethod
    def from_dict(cls,d:dict) -> 'Graph':
        if not isinstance(d,dict) or set(d)-{'n','edges','left','right'}:raise ValueError('invalid graph object')
        return cls(d['n'],tuple(tuple(e) for e in d['edges']),tuple(d.get('left',())),tuple(d.get('right',())))

def components(g: Graph) -> tuple[tuple[int,...],tuple[tuple[int,...],...]]:
    d=DSU(g.n)
    for a,b in g.edges:d.union(a,b)
    roots={}; lab=[]; groups=[]
    for v in range(g.n):
        r=d.find(v)
        if r not in roots:roots[r]=len(groups);groups.append([])
        i=roots[r];lab.append(i);groups[i].append(v)
    return tuple(lab),tuple(tuple(x) for x in groups)

class Builder:
    """Named finite CW graph assembly; equalities identify vertices, never edges."""
    def __init__(self):self.names={};self.ed=[];self.eq=[]
    def vertex(self,x:Hashable)->int:
        if x not in self.names:self.names[x]=len(self.names)
        return self.names[x]
    def edge(self,a:Hashable,b:Hashable):self.ed.append((self.vertex(a),self.vertex(b)))
    def identify(self,a:Hashable,b:Hashable):self.eq.append((self.vertex(a),self.vertex(b)))
    def add(self,g:Graph,key:Hashable):
        for v in range(g.n):self.vertex((key,v))
        for a,b in g.edges:self.edge((key,a),(key,b))
    def finish(self,left:Iterable[Hashable]=(),right:Iterable[Hashable]=()):
        left,right=tuple(left),tuple(right)
        for x in left+right:self.vertex(x)
        d=DSU(len(self.names))
        for a,b in self.eq:d.union(a,b)
        ids={};m=[]
        for i in range(len(self.names)):m.append(ids.setdefault(d.find(i),len(ids)))
        lookup={x:m[i] for x,i in self.names.items()}
        g=Graph(len(ids),tuple((m[a],m[b]) for a,b in self.ed),
                tuple(lookup[x] for x in left),tuple(lookup[x] for x in right))
        return g,lookup

def chain(gs:Iterable[Graph])->Graph:
    gs=list(gs)
    if not gs:raise ValueError('empty chain has no implicit interface')
    b=Builder()
    for i,g in enumerate(gs):
        b.add(g,i)
        if i:
            if len(gs[i-1].right)!=len(g.left):raise ValueError('interface mismatch')
            for x,y in zip(gs[i-1].right,g.left):b.identify((i-1,x),(i,y))
    return b.finish([(0,x) for x in gs[0].left],[(len(gs)-1,x) for x in gs[-1].right])[0]

def power_explicit(g:Graph,n:int,cap:int=10000)->Graph:
    if type(n)is not int or not 1<=n<=cap:raise ValueError('explicit expansion cap or invalid count')
    return chain([g]*n)

def close(g:Graph)->Graph:
    if len(g.left)!=len(g.right):raise ValueError('closure interface mismatch')
    b=Builder();b.add(g,0)
    for a,c in zip(g.left,g.right):b.identify((0,a),(0,c))
    return b.finish()[0]

def induced(g:Graph,vs:Iterable[int])->Graph:
    vs=tuple(sorted(vs)); ix={v:i for i,v in enumerate(vs)}
    return Graph(len(vs),tuple((ix[a],ix[b]) for a,b in g.edges if a in ix and b in ix))
