"""Level-four word algebra, with exact integer coefficients.

Letters: -1 = dt/t, j in {0,1,2,3} = i**j dt/(1-i**j t).
Words use the outer-letter-first iterated-integral convention.
"""
from __future__ import annotations
from collections import Counter
from functools import lru_cache
from typing import Mapping

Word = tuple[int, ...]
IndexWord = tuple[tuple[int, int], ...]
Polynomial = dict[Word, int]
Z = -1

def admissible(w: Word) -> bool:
    return bool(w) and w[0] != 0 and w[-1] != Z and all(-1<=a<=3 for a in w)

def conjugate(w: Word) -> Word:
    return tuple(a if a==Z else (-a)%4 for a in w)

def plus(a: Mapping, b: Mapping, scale=1) -> dict:
    out = dict(a)
    for w,c in b.items():
        out[w] = out.get(w,0)+scale*c
        if not out[w]: del out[w]
    return out

@lru_cache(maxsize=12000)
def shuffle(u: Word, v: Word) -> Polynomial:
    if not u: return {v:1}
    if not v: return {u:1}
    out=Counter()
    for w,c in shuffle(u[1:],v).items(): out[(u[0],)+w]+=c
    for w,c in shuffle(u,v[1:]).items(): out[(v[0],)+w]+=c
    return dict(out)

def shuffle_polynomials(a: Mapping, b: Mapping) -> dict:
    out={}
    for u,x in a.items():
        for v,y in b.items(): out=plus(out,shuffle(u,v),x*y)
    return out

def to_indices(w: Word) -> IndexWord:
    out=[];weight=1;previous=0
    for letter in w:
        if letter==Z: weight+=1
        else:
            out.append((weight,(letter-previous)%4))
            previous=letter;weight=1
    if weight!=1: raise ValueError('Word ends in a zero letter')
    return tuple(out)

def to_word(ind: IndexWord) -> Word:
    out=[];cumulative=0
    for weight,relative in ind:
        if weight<1: raise ValueError('Index must be positive')
        cumulative=(cumulative+relative)%4
        out.extend([Z]*(weight-1)+[cumulative])
    return tuple(out)

@lru_cache(maxsize=12000)
def stuffle(u: IndexWord,v: IndexWord) -> dict[IndexWord,int]:
    if not u: return {v:1}
    if not v: return {u:1}
    out=Counter()
    for w,c in stuffle(u[1:],v).items(): out[(u[0],)+w]+=c
    for w,c in stuffle(u,v[1:]).items(): out[(v[0],)+w]+=c
    a,c=u[0];b,d=v[0]
    for w,m in stuffle(u[1:],v[1:]).items(): out[((a+b,(c+d)%4),)+w]+=m
    return dict(out)

def double_shuffle(u: Word,v: Word) -> Polynomial:
    if not ((admissible(u) or u==(0,)) and admissible(v)):
        raise ValueError('Only admissible factors or one Li_1(1) are allowed')
    out=dict(shuffle(u,v))
    for ind,c in stuffle(to_indices(u),to_indices(v)).items():
        out=plus(out,{to_word(ind):c},-1)
    if not all(admissible(w) for w in out):
        raise ValueError('Divergent terms have not canceled')
    return out

def odd_projection(p: Mapping) -> dict:
    out={}
    for w,c in p.items():
        v=conjugate(w)
        if w<v: out=plus(out,{w:c})
        elif v<w: out=plus(out,{v:-c})
    return out

def delta(w: Word) -> Polynomial:
    return plus({w:1},{conjugate(w):1},-1)

TAU={Z:{0:1,2:-1},0:{Z:1,2:1},1:{2:1,3:-1},2:{2:1},3:{2:1,1:-1}}

def cayley(w: Word) -> Polynomial:
    p={():1}
    for a in reversed(w):
        q={}
        for v,x in p.items():
            for b,y in TAU[a].items(): q=plus(q,{v+(b,):x*y})
        p=q
    if admissible(w) and not all(admissible(v) for v in p):
        raise ValueError('Cayley transform left admissible words')
    return p

def target() -> Polynomial:
    """T whose iterated integral equals 16*i*R in the article."""
    A=(Z,Z,Z,1,1); B=(Z,Z,1,Z,1); C=(Z,Z,Z,1,3); V=(Z,Z,Z,1)
    out={}
    for coef,w in [(56,C),(-408,A),(-192,B)]: out=plus(out,delta(w),coef)
    power={():1}
    for _ in range(5): power=shuffle_polynomials(power,delta((1,)))
    out=plus(out,power,-19)
    return plus(out,shuffle_polynomials(delta(V),{(2,):1}),-112)
