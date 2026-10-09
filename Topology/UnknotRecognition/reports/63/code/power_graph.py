"""Exact power-conjugacy graph inference. This module never returns a knot verdict.

An edge denotes x_s**a = w*x_t**b*w^-1. `plain` means w=1.
The caller must establish these relations in a classical knot group before
interpreting `killed` as a valid group operation. No torsion-free flag is accepted.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from collections import deque
from typing import Iterable

@dataclass(frozen=True)
class Edge:
    s: int
    t: int
    a: int
    b: int
    plain: bool = False

    def validate(self, vertices: set[int]) -> None:
        if any(type(x) is not int for x in (self.s,self.t,self.a,self.b)):
            raise ValueError('edge integers must be strict integers')
        if self.s not in vertices or self.t not in vertices or not self.a or not self.b:
            raise ValueError('invalid endpoint or zero exponent')
        if type(self.plain) is not bool:
            raise ValueError('plain must be a boolean')


def _cycle(s: int, t: int, eid: int, parent: dict[int,tuple[int,int,int]|None]):
    # Tree path s -> t followed by the reverse of edge s -> t.
    left=[]; x=s; positions={s:0}
    while parent[x] is not None:
        p,j,d=parent[x]; left.append([j,-d]); x=p; positions[x]=len(left)
    right=[]; y=t
    while y not in positions:
        p,j,d=parent[y]; right.append([j,d]); y=p
    return left[:positions[y]] + list(reversed(right)) + [[eid,-1]]


def _components(vertices, edges):
    adj={v:[] for v in vertices}
    for j,e in enumerate(edges):
        adj[e.s].append((e.t,j,1)); adj[e.t].append((e.s,j,-1))
    comp={}; groups=[]
    for v in sorted(vertices):
        if v in comp: continue
        idx=len(groups); group=[]; q=deque([v]); comp[v]=idx
        while q:
            x=q.popleft(); group.append(x)
            for y,_,_ in adj[x]:
                if y not in comp: comp[y]=idx; q.append(y)
        groups.append(sorted(group))
    return adj,comp,groups


def infer(vertices: Iterable[int], edges: list[Edge], *, modular: bool=True) -> dict:
    """Maximal graph-level annihilation using absolute ratios and plain signs.

    A deterministic mod-65537 pass can find positive witnesses cheaply. An exact
    rational pass processes all as-yet-undecided components; no probabilistic
    equality test or unverified hash is used.
    """
    vertices=list(vertices)
    if len(set(vertices))!=len(vertices) or any(type(v) is not int or v<=0 for v in vertices):
        raise ValueError('vertices must be distinct positive integers')
    vs=set(vertices)
    for e in edges: e.validate(vs)
    adj,comp,groups=_components(vs,edges)
    found={}; stats={'modular_edges':0,'rational_edges':0,'sign_edges':0}

    def pass_values(mode):
        values={}; parent={}
        for start in sorted(vs):
            if comp[start] in found or start in values: continue
            values[start]=1 if mode!='rational' else Fraction(1)
            parent[start]=None; q=deque([start])
            while q and comp[start] not in found:
                x=q.popleft()
                for y,j,d in adj[x]:
                    e=edges[j]
                    if mode=='sign' and not e.plain: continue
                    aa,bb=(e.a,e.b) if d==1 else (e.b,e.a)
                    if mode=='modular':
                        aa=abs(aa)%65537; bb=abs(bb)%65537
                        if aa==0 or bb==0: continue
                        want=values[x]*aa*pow(bb,-1,65537)%65537
                    elif mode=='rational':
                        want=values[x]*Fraction(abs(aa),abs(bb))
                    else:
                        want=values[x]*(1 if aa*bb>0 else -1)
                    stats[mode+'_edges' if mode!='sign' else 'sign_edges']+=1
                    if y not in values:
                        values[y]=want; parent[y]=(x,j,d); q.append(y)
                    elif values[y]!=want:
                        # _cycle expects an edge with its declared orientation.
                        cyc=_cycle(e.s,e.t,j,parent)
                        found[comp[x]]={'mode':'plain' if mode=='sign' else 'modulus',
                                        'walk':cyc}
                        break
    if modular: pass_values('modular')
    pass_values('rational')
    pass_values('sign')
    witnesses=[found[k] for k in sorted(found)]
    killed=sorted(v for k in found for v in groups[k])
    return {'killed':killed,'witnesses':witnesses,'stats':stats}
