"""Exact terminal-pair recovery from additive orbit histograms.

All source intervals are half-open except Pairing endpoints, which are inclusive.
This module does not certify that its input is a surface or recognize a knot.
"""
from __future__ import annotations
from dataclasses import dataclass
from collections import Counter
from math import isqrt
from typing import Callable, Iterable, Sequence

class Incomplete(RuntimeError):
    """Resource exhaustion: no topological conclusion is authorized."""

@dataclass(frozen=True)
class Pairing:
    a: int
    b: int
    c: int
    d: int
    reverse: bool = False
    def validate(self, size: int) -> None:
        if any(type(x) is not int for x in (self.a,self.b,self.c,self.d)):
            raise ValueError('integer pairing endpoints required')
        if type(self.reverse) is not bool:
            raise ValueError('Boolean reversal required')
        if not (0 <= self.a <= self.b < size and 0 <= self.c <= self.d < size
                and self.b-self.a == self.d-self.c):
            raise ValueError('invalid interval pairing')
    def image(self, x: int) -> int:
        return self.d-(x-self.a) if self.reverse else self.c+(x-self.a)

Weight = tuple[int, int, tuple[int, ...]]
Histogram = list[tuple[tuple[int, ...], int]]
Oracle = Callable[[int, Sequence[Pairing], Sequence[Weight], int], Histogram]


def canonical_weights(size: int, additions: Iterable[Weight], dimension: int) -> list[Weight]:
    """Endpoint sweep; never loops over represented points."""
    if type(size) is not int or size < 0 or type(dimension) is not int or dimension < 1:
        raise ValueError('invalid universe or dimension')
    delta: dict[int,list[int]] = {0:[0]*dimension, size:[0]*dimension}
    for lo,hi,value in additions:
        if type(lo) is not int or type(hi) is not int or not 0<=lo<=hi<=size:
            raise ValueError('invalid weight interval')
        if len(value)!=dimension or any(type(v) is not int for v in value):
            raise ValueError('invalid weight vector')
        if lo==hi: continue
        for x,sign in ((lo,1),(hi,-1)):
            d=delta.setdefault(x,[0]*dimension)
            for j,v in enumerate(value): d[j]+=sign*v
    endpoints=sorted(delta); current=[0]*dimension; out=[]
    for lo,hi in zip(endpoints,endpoints[1:]):
        for j,v in enumerate(delta[lo]): current[j]+=v
        row=tuple(current)
        if out and out[-1][1]==lo and out[-1][2]==row:
            out[-1]=(out[-1][0],hi,row)
        else: out.append((lo,hi,row))
    return out


def moment_weights(size: int, terminals: Sequence[int],
                   edge_mass: Sequence[tuple[int,int,int]]) -> list[Weight]:
    """Each terminal occurrence gets a distinct ID, even at a shared point."""
    additions: list[Weight]=[]
    for i,x in enumerate(terminals,1):
        if type(x) is not int or not 0<=x<size: raise ValueError('invalid terminal point')
        additions.append((x,x+1,(1,i,i*i,0)))
    for lo,hi,mass in edge_mass:
        if type(mass) is not int or mass<0: raise ValueError('nonnegative edge mass required')
        additions.append((lo,hi,(0,0,0,mass)))
    return canonical_weights(size,additions,4)


def decode_pairs(histogram: Histogram, terminal_count: int) -> tuple[tuple[int,int,int],...]:
    """Decode (count,sum,squares,length); reject invalid touched profiles."""
    if type(terminal_count) is not int or terminal_count<0 or terminal_count%2:
        raise ValueError('an even number of terminal occurrences is required')
    seen=set(); result=[]
    for w,multiplicity in histogram:
        if len(w)!=4 or any(type(x) is not int or x<0 for x in w):
            raise ValueError('invalid moment profile')
        if type(multiplicity) is not int or multiplicity<1:
            raise ValueError('positive integer orbit multiplicity required')
        t,s,q,length=w
        if t==0:
            if s or q: raise ValueError('unmarked orbit has terminal moments')
            continue
        if t!=2 or multiplicity!=1:
            raise ValueError('each touched orbit must have exactly two unique terminals')
        square=2*q-s*s
        if square<=0: raise ValueError('distinct terminal labels required')
        d=isqrt(square)
        if d*d!=square or (s-d)%2: raise ValueError('invalid pair discriminant')
        i,j=(s-d)//2,(s+d)//2
        if not 1<=i<j<=terminal_count or i*i+j*j!=q:
            raise ValueError('decoded labels out of range')
        if i in seen or j in seen: raise ValueError('repeated terminal label')
        seen.update((i,j)); result.append((i,j,length))
    if len(seen)!=terminal_count: raise ValueError('missing terminal labels')
    return tuple(sorted(result))


class DSU:
    def __init__(self,n: int): self.parent=list(range(n)); self.rank=[0]*n
    def find(self,x: int) -> int:
        while self.parent[x]!=x:
            self.parent[x]=self.parent[self.parent[x]];x=self.parent[x]
        return x
    def union(self,a: int,b: int) -> None:
        a,b=self.find(a),self.find(b)
        if a==b:return
        if self.rank[a]<self.rank[b]:a,b=b,a
        self.parent[b]=a
        if self.rank[a]==self.rank[b]:self.rank[a]+=1

@dataclass(frozen=True)
class Kernel:
    pairs: tuple[tuple[int,int,int],...]
    port_owners: tuple[int,...]
    active_counts: tuple[int,...]
    passive_counts: tuple[int,...]
    weighted_calls: int


def assemble_kernel(pairs: tuple[tuple[int,int,int],...], port_owners: Sequence[int],
                    boundary_counts: Sequence[int], calls: int=1) -> Kernel:
    p=len(port_owners); s=len(boundary_counts)
    if any(type(x) is not int or x<0 for x in boundary_counts):
        raise ValueError('invalid certified boundary count')
    if any(type(x) is not int or not 0<=x<s for x in port_owners):
        raise ValueError('invalid port owner')
    # Revalidate pair partition even for externally provided decoded records.
    used=[i for a,b,_ in pairs for i in (a,b)]
    if sorted(used)!=list(range(1,2*p+1)) or any(l<0 for _,_,l in pairs):
        raise ValueError('invalid residual matching')
    dsu=DSU(2*p)
    for j in range(p):dsu.union(2*j,2*j+1)
    for i,j,_ in pairs:
        if port_owners[(i-1)//2]!=port_owners[(j-1)//2]:
            raise ValueError('residual path crosses declared surface owners')
        dsu.union(i-1,j-1)
    roots={}; active=[0]*s
    for j,owner in enumerate(port_owners): roots[dsu.find(2*j)]=owner
    for owner in roots.values():active[owner]+=1
    passive=tuple(b-a for b,a in zip(boundary_counts,active))
    if any(x<0 for x in passive):raise ValueError('boundary count below active cycle count')
    return Kernel(pairs,tuple(port_owners),tuple(active),passive,calls)


def compile_kernel(size: int, pairings: Sequence[Pairing], terminals: Sequence[int],
                   edge_mass: Sequence[tuple[int,int,int]], port_owners: Sequence[int],
                   boundary_counts: Sequence[int], oracle: Oracle) -> Kernel:
    if len(terminals)!=2*len(port_owners): raise ValueError('two endpoint occurrences per port')
    for pair in pairings:pair.validate(size)
    if not terminals:
        return assemble_kernel((),port_owners,boundary_counts,0)
    weights=moment_weights(size,terminals,edge_mass)
    histogram=oracle(size,pairings,weights,4)
    pairs=decode_pairs(histogram,len(terminals))
    return assemble_kernel(pairs,port_owners,boundary_counts)


def decode_bounded_moments(histogram: Histogram, labels: int, bound: int) -> tuple[tuple[int,...],...]:
    """General fixed occupancy decoder using Newton identities and root scanning.

    Input coordinates: terminal count, sum i, ..., sum i**bound.
    This intentionally favors a simple independently checkable decoder over speed.
    """
    if labels<0 or bound<1: raise ValueError('invalid bound')
    out=[]; seen=set()
    for w,mult in histogram:
        if len(w)!=bound+1 or any(type(x) is not int or x<0 for x in w) or mult<1:
            raise ValueError('bad moment record')
        t=w[0]
        if t==0:
            if any(w):raise ValueError('unmarked nonzero moments')
            continue
        if t>bound or mult!=1:raise ValueError('occupancy or multiplicity violation')
        e=[1]
        for k in range(1,t+1):
            value=sum((-1)**(j-1)*e[k-j]*w[j] for j in range(1,k+1))
            if value%k:raise ValueError('nonintegral Newton coefficient')
            e.append(value//k)
        roots=[]
        for x in range(1,labels+1):
            value=1
            for k in range(1,t+1):value=value*x+(-1)**k*e[k]
            if value==0:roots.append(x)
        if len(roots)!=t or any(sum(x**k for x in roots)!=w[k] for k in range(1,bound+1)):
            raise ValueError('invalid or repeated roots')
        if any(x in seen for x in roots):raise ValueError('repeated label')
        seen.update(roots);out.append(tuple(roots))
    if len(seen)!=labels:raise ValueError('missing labels')
    return tuple(sorted(out))


def packing_shift(terminal_count: int) -> int:
    if type(terminal_count) is not int or terminal_count<1:raise ValueError('positive terminal count')
    r=terminal_count
    return (r*(r+1)*(2*r+1)//6).bit_length()


def packed_moment_weights(size: int,terminals: Sequence[int],edge_mass: Sequence[tuple[int,int,int]]):
    """No carries in the three low fields: all terminal moments are globally bounded."""
    shift=packing_shift(len(terminals)); additions=[]
    for i,x in enumerate(terminals,1):
        if type(x) is not int or not 0<=x<size:raise ValueError('invalid terminal point')
        additions.append((x,x+1,(1+(i<<shift)+(i*i<<(2*shift)),)))
    for a,b,m in edge_mass:
        if type(m) is not int or m<0:raise ValueError('nonnegative edge mass required')
        additions.append((a,b,(m<<(3*shift),)))
    return canonical_weights(size,additions,1)


def decode_packed(histogram: Histogram,terminal_count: int):
    shift=packing_shift(terminal_count);mask=(1<<shift)-1;vectors=[]
    for row,n in histogram:
        if len(row)!=1 or type(row[0]) is not int or row[0]<0:raise ValueError('nonnegative scalar weight required')
        w=row[0]
        vectors.append(((w&mask,(w>>shift)&mask,(w>>(2*shift))&mask,w>>(3*shift)),n))
    return decode_pairs(vectors,terminal_count)


def compile_kernel_packed(size: int, pairings: Sequence[Pairing],terminals: Sequence[int],
                          edge_mass: Sequence[tuple[int,int,int]],port_owners: Sequence[int],
                          boundary_counts: Sequence[int],oracle: Oracle) -> Kernel:
    if len(terminals)!=2*len(port_owners):raise ValueError('two endpoint occurrences per port')
    for pair in pairings:pair.validate(size)
    if not terminals:return assemble_kernel((),port_owners,boundary_counts,0)
    weights=packed_moment_weights(size,terminals,edge_mass)
    hist=oracle(size,pairings,weights,1)
    pairs=decode_packed(hist,len(terminals))
    before=sum((b-a)*w[0] for a,b,w in weights)
    after=sum(n*w[0] for w,n in hist)
    if before!=after:raise ValueError('scalar mass conservation failed')
    return assemble_kernel(pairs,port_owners,boundary_counts)


def kernel_record(kernel: Kernel) -> dict:
    """JSON-safe interface output; large lengths use exact hexadecimal strings.

    This is a derived interface record, not a source-geometry or knot certificate.
    """
    def integer(n):return n if n.bit_length()<=256 else hex(n)
    return {'schema':'moment-boundary-kernel-v1',
            'pairs':[{'endpoints':[i,j],'unmarked_edges':integer(l),'zero':l==0} for i,j,l in kernel.pairs],
            'port_owners':list(kernel.port_owners),'active_counts':list(kernel.active_counts),
            'passive_counts':[integer(n) for n in kernel.passive_counts],'weighted_calls':kernel.weighted_calls}
