"""Independent small, unreduced F_2 Khovanov crossing-cube audit for braid closures.

This file intentionally does not import the register or port implementation. It
builds circles by union-find and applies the multiplication/comultiplication of
F_2[x]/(x^2) to enhanced states. The audit is exponential and strictly size-capped.
It is not a replacement for the maintained scanner. Quantum grading is omitted.
"""
from __future__ import annotations


class UnionFind:
    def __init__(self,n): self.parent=list(range(n));self.size=[1]*n
    def find(self,a):
        while a != self.parent[a]:
            self.parent[a]=self.parent[self.parent[a]];a=self.parent[a]
        return a
    def join(self,a,b):
        a,b=self.find(a),self.find(b)
        if a==b:return
        if self.size[a]<self.size[b]:a,b=b,a
        self.parent[b]=a;self.size[a]+=self.size[b]


def circles(strands,word,state):
    n=len(word); uf=UnionFind(strands*(n+1))
    for j,g in enumerate(word):
        i=abs(g)-1
        cap = ((state >> j)&1) if g>0 else 1-((state >> j)&1)
        for k in range(strands):
            if k not in (i,i+1) or not cap:
                uf.join(j*strands+k,(j+1)*strands+k)
        if cap:
            uf.join(j*strands+i,j*strands+i+1)
            uf.join((j+1)*strands+i,(j+1)*strands+i+1)
    for k in range(strands): uf.join(k,n*strands+k)
    groups={}
    for v in range(strands*(n+1)): groups.setdefault(uf.find(v),set()).add(v)
    return tuple(sorted((frozenset(v) for v in groups.values()),key=min))


def saddle_labels(source,target,label):
    common={i:target.index(c) for i,c in enumerate(source) if c in target}
    src=[i for i in range(len(source)) if i not in common]
    dst=[j for j in range(len(target)) if target[j] not in source]
    out=sum(((label >> i)&1) << j for i,j in common.items())
    if len(src)==2 and len(dst)==1:
        x,y=((label >> i)&1 for i in src)
        if x and y:return []
        return [out | ((x|y) << dst[0])]
    if len(src)==1 and len(dst)==2:
        x=(label >> src[0])&1
        if x:return [out | (1 << dst[0]) | (1 << dst[1])]
        return [out | (1 << dst[0]),out | (1 << dst[1])]
    raise AssertionError('saddle is neither merge nor split')


def cube(strands,word,max_dimension=6000):
    if type(strands) is not int or strands<1 or any(type(g) is not int or not 1<=abs(g)<strands for g in word):
        raise ValueError('invalid braid')
    if len(word)>12:raise ValueError('crossing cap exceeded')
    allcircles=[circles(strands,word,s) for s in range(1 << len(word))]
    offsets=[];n=0
    for cs in allcircles:
        offsets.append(n);n+=1 << len(cs)
    if n>max_dimension:raise ValueError('cube dimension cap exceeded')
    rows=[0]*n;degrees=[0]*n
    negative=sum(g<0 for g in word)
    for state,cs in enumerate(allcircles):
        for label in range(1 << len(cs)):
            index=offsets[state]+label;degrees[index]=state.bit_count()-negative
            for j in range(len(word)):
                if state >> j & 1:continue
                t=state | (1 << j)
                for output in saddle_labels(cs,allcircles[t],label):
                    rows[offsets[t]+output] ^= 1 << index
    return rows,degrees


def low_pivot_rank(rows):
    """Independent low-bit sparse row elimination."""
    pivots={}
    for row in rows:
        while row:
            low=row & -row
            if low not in pivots:
                pivots[low]=row;break
            row ^= pivots[low]
    return len(pivots)


def square_zero(rows):
    for row in rows:
        value=0
        while row:
            bit=row & -row; row ^= bit
            value ^= rows[bit.bit_length()-1]
        if value:return False
    return True


def homology(rows,degrees):
    if not square_zero(rows):raise AssertionError('cube differential square is nonzero')
    out={}
    for h in sorted(set(degrees)):
        n=sum(i==h for i in degrees)
        incoming=low_pivot_rank([row for row,k in zip(rows,degrees) if k==h])
        outgoing=low_pivot_rank([row for row,k in zip(rows,degrees) if k==h+1])
        beta=n-incoming-outgoing
        if beta:out[h]=beta
    return out


def components(strands,word):
    permutation=list(range(strands))
    for g in word:
        i=abs(g)-1;permutation[i],permutation[i+1]=permutation[i+1],permutation[i]
    seen=set();count=0
    for i in range(strands):
        if i in seen:continue
        count+=1
        while i not in seen:seen.add(i);i=permutation[i]
    return count
