"""Independent finite reference and a restricted binary block oracle.

The block oracle is NOT a general AHT implementation. Its accepted pairings
are unit translations, identities, and singleton bridges. It rejects other
families rather than silently expanding them.
"""
from __future__ import annotations
from bisect import bisect_right
from collections import Counter
from typing import Sequence
from moment_kernel import DSU, Pairing, Weight, Histogram, Incomplete, canonical_weights


def literal_oracle(size: int, pairs: Sequence[Pairing], weights: Sequence[Weight],
                   dimension: int, cap: int=200000) -> Histogram:
    if size>cap:raise Incomplete('literal reference point cap')
    dsu=DSU(size)
    for p in pairs:
        p.validate(size)
        for x in range(p.a,p.b+1):dsu.union(x,p.image(x))
    values=[[0]*dimension for _ in range(size)]
    for a,b,w in canonical_weights(size,weights,dimension):
        for x in range(a,b): values[x]=list(w)
    totals={}
    for x,w in enumerate(values):
        v=totals.setdefault(dsu.find(x),[0]*dimension)
        for j,z in enumerate(w):v[j]+=z
    counts=Counter(tuple(w) for w in totals.values())
    return sorted(counts.items())


class Prefix:
    def __init__(self,size: int,weights: Sequence[Weight],dimension: int):
        self.runs=canonical_weights(size,weights,dimension)
        self.starts=[a for a,_,_ in self.runs];self.dimension=dimension;self.size=size
        total=[0]*dimension;self.prefix=[]
        for a,b,w in self.runs:
            self.prefix.append(tuple(total))
            for j,z in enumerate(w):total[j]+=(b-a)*z
        self.total=tuple(total)
    def at(self,x: int) -> tuple[int,...]:
        if x==self.size:return self.total
        i=bisect_right(self.starts,x)-1
        a,_,w=self.runs[i]
        return tuple(v+(x-a)*z for v,z in zip(self.prefix[i],w))
    def interval(self,a: int,b: int) -> tuple[int,...]:
        return tuple(y-x for x,y in zip(self.at(a),self.at(b)))


def block_oracle(size: int,pairs: Sequence[Pairing],weights: Sequence[Weight],dimension: int) -> Histogram:
    intervals=[]; bridges=[]
    for p in pairs:
        p.validate(size)
        if p.a==p.b:
            bridges.append((p.a,p.c));intervals.extend(((p.a,p.a),(p.c,p.c)))
        elif not p.reverse and p.c==p.a:
            pass
        elif not p.reverse and abs(p.c-p.a)==1:
            intervals.append((min(p.a,p.c),max(p.b,p.d)))
        else:raise Incomplete('unsupported family in restricted block oracle')
    intervals.sort(); blocks=[]
    for a,b in intervals:
        if blocks and a<=blocks[-1][1]:blocks[-1]=(blocks[-1][0],max(b,blocks[-1][1]))
        else:blocks.append((a,b))
    starts=[a for a,_ in blocks];dsu=DSU(len(blocks))
    for a,b in bridges:dsu.union(bisect_right(starts,a)-1,bisect_right(starts,b)-1)
    pref=Prefix(size,weights,dimension);totals={}
    for i,(a,b) in enumerate(blocks):
        row=totals.setdefault(dsu.find(i),[0]*dimension)
        for j,z in enumerate(pref.interval(a,b+1)):row[j]+=z
    counts=Counter(tuple(w) for w in totals.values())
    # Points outside blocks are isolated. Count constant-weight runs in binary.
    gaps=[];at=0
    for a,b in blocks:
        if at<a:gaps.append((at,a))
        at=b+1
    if at<size:gaps.append((at,size))
    run=0
    for a,b in gaps:
        while a<b:
            while pref.runs[run][1]<=a:run+=1
            _,stop,w=pref.runs[run];end=min(b,stop)
            counts[w]+=end-a;a=end
    return sorted(counts.items())
