"""Finite-group transport recovered from a lifted moment census.

Convention: (x,g) -> (y,g*t). Deck transformations act on the LEFT.
Source labels must define a local system on quotient vertices. The compiler
checks recovered endpoint equivariance, not the source's geometric validity.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import permutations
from typing import Sequence
from moment_kernel import Pairing, Oracle, moment_weights, decode_pairs, packed_moment_weights, decode_packed

@dataclass(frozen=True)
class Group:
    table: tuple[tuple[int,...],...]
    identity: int=0
    def validate(self):
        n=len(self.table);r=list(range(n));e=self.identity
        if not n or not 0<=e<n:raise ValueError('invalid identity')
        if any(len(row)!=n or sorted(row)!=r for row in self.table):raise ValueError('not a group table')
        if any(self.table[e][x]!=x or self.table[x][e]!=x for x in r):raise ValueError('identity failed')
        if any(self.table[self.table[a][b]][c]!=self.table[a][self.table[b][c]] for a in r for b in r for c in r):
            raise ValueError('associativity failed')
    def mul(self,a,b):return self.table[a][b]
    def inv(self,a):return self.table[a].index(self.identity)


def cyclic_group(n: int) -> Group:
    if n<1:raise ValueError('nonempty group')
    return Group(tuple(tuple((a+b)%n for b in range(n)) for a in range(n)))


def symmetric_three() -> Group:
    perms=list(permutations(range(3)));index={p:i for i,p in enumerate(perms)}
    # Multiplication is composition a after b; identity permutation comes first.
    return Group(tuple(tuple(index[tuple(a[b[x]] for x in range(3))] for b in perms) for a in perms))


def transport_census(size: int, labelled_pairs: Sequence[tuple[Pairing,int]],
                     terminals: Sequence[int], edge_mass: Sequence[tuple[int,int,int]],
                     group: Group, oracle: Oracle, *, packed: bool=True):
    group.validate();g=len(group.table);pairs=[]
    if len(terminals)%2:raise ValueError('two terminal occurrences per port')
    if not terminals:return ()
    for p,t in labelled_pairs:
        p.validate(size)
        if type(t) is not int or not 0<=t<g:raise ValueError('invalid transport')
        for sheet in range(g):
            other=group.mul(sheet,t)
            pairs.append(Pairing(p.a+sheet*size,p.b+sheet*size,p.c+other*size,p.d+other*size,p.reverse))
    lifted_terminals=[x+sheet*size for x in terminals for sheet in range(g)]
    mass=[(a+sheet*size,b+sheet*size,m) for sheet in range(g) for a,b,m in edge_mass]
    if packed:
        weights=packed_moment_weights(size*g,lifted_terminals,mass)
        decoded=decode_packed(oracle(size*g,pairs,weights,1),len(lifted_terminals))
    else:
        weights=moment_weights(size*g,lifted_terminals,mass)
        decoded=decode_pairs(oracle(size*g,pairs,weights,4),len(lifted_terminals))
    data={}
    for a,b,l in decoded:
        i,s=divmod(a-1,g);j,t=divmod(b-1,g)
        if i==j:raise ValueError('a path lift joins two sheets of the same base terminal')
        key=(i+1,j+1);row=data.setdefault(key,{})
        if s in row:raise ValueError('duplicate source sheet')
        row[s]=(t,l)
    used=[];result=[]
    for (i,j),mapping in sorted(data.items()):
        if set(mapping)!=set(range(g)):raise ValueError('incomplete path fibre')
        transport,length=mapping[group.identity]
        for sheet in range(g):
            if mapping[sheet]!=(group.mul(sheet,transport),length):
                raise ValueError('endpoint map violates deck equivariance')
        result.append((i,j,length,transport));used.extend((i,j))
    if sorted(used)!=list(range(1,len(terminals)+1)):raise ValueError('base terminal partition failed')
    return tuple(result)


def boundary_holonomies(transports, port_transports: Sequence[int], group: Group):
    """One oriented holonomy per active cycle, with deterministic starting terminal.

    This uses authenticated local port frames; it does not establish coherent
    orientation of a base surface. Returns (start_terminal, group_element).
    """
    gap={}
    for i,j,_,t in transports:
        if i in gap or j in gap:raise ValueError('repeated terminal')
        gap[i]=(j,t);gap[j]=(i,group.inv(t))
    p=len(port_transports)
    if set(gap)!=set(range(1,2*p+1)):raise ValueError('missing terminal')
    if any(type(t) is not int or not 0<=t<len(group.table) for t in port_transports):
        raise ValueError('invalid port transport')
    unused=set(gap);out=[]
    while unused:
        start=min(unused);x=start;h=group.identity
        while True:
            y=x+1 if x%2 else x-1;t=port_transports[(x-1)//2]
            if x%2==0:t=group.inv(t)
            h=group.mul(h,t);unused.discard(x);unused.discard(y)
            z,t=gap[y];h=group.mul(h,t);x=z
            if x==start:break
        out.append((start,h))
    return tuple(out)


def forget_transport(transports,port_transports: Sequence[int],keep: Sequence[int],group: Group):
    """Transport of surviving paths after unmarking unit ports.

    Ordered multiplication is essential. Terminal-free holonomies are not
    returned; preserve the fine kernel when future reactivation is required.
    """
    p=len(port_transports);kept=set(keep)
    if len(kept)!=len(keep) or any(type(j) is not int or not 0<=j<p for j in keep):raise ValueError('invalid kept ports')
    gap={}
    for a,b,l,t in transports:gap[a]=(b,l,t);gap[b]=(a,l,group.inv(t))
    if set(gap)!=set(range(1,2*p+1)):raise ValueError('incomplete terminal matching')
    renumber={2*j+e+1:2*k+e+1 for k,j in enumerate(keep) for e in (0,1)}
    result=[];seen=set()
    for start in renumber:
        if start in seen:continue
        x=start;length=0;h=group.identity;steps=0
        while True:
            y,l,t=gap[x];length+=l;h=group.mul(h,t)
            if (y-1)//2 in kept:break
            t=port_transports[(y-1)//2]
            if y%2==0:t=group.inv(t)
            h=group.mul(h,t);length+=1;x=y+1 if y%2 else y-1;steps+=1
            if steps>p:raise ValueError('malformed continuation graph')
        seen.update((start,y));a,b=renumber[start],renumber[y]
        if a>b:a,b=b,a;h=group.inv(h)
        result.append((a,b,length,h))
    return tuple(sorted(result))
