#!/usr/bin/env python3
"""Finite exact checks accompanying the common-domain Hahn linearization article.

Python 3.9+; standard library only. This is NOT a proof of the asymptotic
small-divisor theorem, analytic convergence, strong Hahn summability or novelty.
All arithmetic used in the algebra tests is exact in Q(i).
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Fr
from itertools import product
from random import Random
from typing import Dict, Tuple

@dataclass(frozen=True)
class QI:
    re: Fr = Fr(0)
    im: Fr = Fr(0)
    def __add__(self, other):
        b = other if isinstance(other, QI) else QI(Fr(other))
        return QI(self.re+b.re, self.im+b.im)
    __radd__ = __add__
    def __neg__(self): return QI(-self.re, -self.im)
    def __sub__(self, other): return self + (-other if isinstance(other,QI) else -Fr(other))
    def __mul__(self, other):
        b = other if isinstance(other,QI) else QI(Fr(other))
        return QI(self.re*b.re-self.im*b.im, self.re*b.im+self.im*b.re)
    __rmul__ = __mul__
    def __truediv__(self, other):
        b = other if isinstance(other,QI) else QI(Fr(other))
        den=b.re*b.re+b.im*b.im
        if not den: raise ZeroDivisionError("zero Gaussian rational divisor")
        return self * QI(b.re/den,-b.im/den)
    def __pow__(self, n):
        if n<0: return (QI(Fr(1))/self)**(-n)
        ans=QI(Fr(1)); b=self
        while n:
            if n&1: ans=ans*b
            b=b*b; n//=2
        return ans
    def __bool__(self): return bool(self.re or self.im)

ZERO=QI(); ONE=QI(Fr(1))
Key=Tuple[int,int,int]
Poly=Dict[Key,QI]
TP=3; ZP=6

def add(*polys: Poly) -> Poly:
    r: Poly={}
    for p in polys:
        for k,c in p.items():
            r[k]=r.get(k,ZERO)+c
            if not r[k]: del r[k]
    return r

def scale(p: Poly,c: QI) -> Poly:
    return {k:c*v for k,v in p.items() if c*v}

def mul(p: Poly,q: Poly) -> Poly:
    r: Poly={}
    for (a,b,c),u in p.items():
        for (d,e,f),v in q.items():
            k=(a+d,b+e,c+f)
            if k[0]<=TP and k[1]+k[2]<=ZP:
                r[k]=r.get(k,ZERO)+u*v
                if not r[k]: del r[k]
    return r

def powp(p: Poly,n:int) -> Poly:
    r={(0,0,0):ONE}
    for _ in range(n): r=mul(r,p)
    return r

def compose(p: Poly,maps: Tuple[Poly,Poly]) -> Poly:
    x,y=maps
    xp=[powp(x,n) for n in range(ZP+1)]
    yp=[powp(y,n) for n in range(ZP+1)]
    r:Poly={}
    for (t,a,b),c in p.items():
        r=add(r,mul({(t,0,0):c},mul(xp[a],yp[b])))
    return r

def algebra_tests():
    x={(0,1,0):ONE}; y={(0,0,1):ONE}
    a=QI(Fr(3,5),Fr(4,5)); b=QI(Fr(5,13),Fr(12,13))
    assert a.re*a.re+a.im*a.im==1
    assert b.re*b.re+b.im*b.im==1
    # Two nonidentical unimodular multipliers; denominators checked only
    # in the finite Taylor range used below.
    lam=(a,b); z=(x,y)
    L=(scale(x,a),scale(y,b))
    f=({(1,2,0):ONE,(1,1,1):QI(Fr(2)),(2,0,3):ONE},
       {(1,0,2):QI(Fr(-1)),(1,2,0):ONE,(2,2,1):ONE})
    F=(add(L[0],f[0]),add(L[1],f[1]))
    G=[dict(x),dict(y)]
    nonzero_divisors=0
    # Forward equation L_h g = f(z+g), solved by parameter degree.
    for k in range(1,TP+1):
        rhs=[compose(fi,tuple(G)) for fi in f]
        for j in range(2):
            layer={}
            for (t,u,v),c in rhs[j].items():
                if t==k:
                    den=a**u*b**v-lam[j]
                    assert den
                    nonzero_divisors+=1
                    layer[(t,u,v)]=c/den
            G[j]=add(G[j],layer)
    # Independent inverse convention, using an operator residual recursion.
    H=[dict(x),dict(y)]
    for k in range(1,TP+1):
        residual=[add(compose(H[j],F),scale(H[j],-lam[j])) for j in range(2)]
        for j in range(2):
            layer={}
            for (t,u,v),c in residual[j].items():
                if t==k:
                    den=a**u*b**v-lam[j]
                    assert den
                    layer[(t,u,v)]=-c/den
            H[j]=add(H[j],layer)
    identities=0
    for j in range(2):
        assert compose(F[j],tuple(G))==compose(G[j],L); identities+=1
        assert compose(H[j],F)==scale(H[j],lam[j]); identities+=1
        assert compose(H[j],tuple(G))==z[j]; identities+=1
        assert compose(G[j],tuple(H))==z[j]; identities+=1
    return nonzero_divisors,identities,sum(len(p) for p in G),sum(len(p) for p in H)

def contraction_check(parents, colors, local_leaves, marked):
    m=len(parents); children=[[] for _ in range(m)]
    for v in range(1,m): children[parents[v]].append(v)
    descendants=[{v} for v in range(m)]
    alpha=[list(a) for a in local_leaves]
    weight=[len(children[v])+sum(local_leaves[v])-1 for v in range(m)]
    assert all(w>=1 for w in weight)
    for v in range(m-1,-1,-1):
        for u in children[v]:
            descendants[v]|=descendants[u]
            alpha[v]=[alpha[v][i]+alpha[u][i] for i in range(2)]
    assert sum(alpha[0])-1==sum(weight)
    blocks=[]
    for v in marked:
        nearest=[]
        for u in marked:
            if u==v or u not in descendants[v]: continue
            p=parents[u]
            while p!=v and p not in marked: p=parents[p]
            if p==v: nearest.append(u)
        block=set(descendants[v])
        for u in nearest: block-=descendants[u]
        beta=[alpha[v][i]-sum(alpha[u][i] for u in nearest)
              +sum(colors[u]==i for u in nearest) for i in range(2)]
        assert min(beta)>=0
        assert sum(beta)==1+sum(weight[w] for w in block)>=2
        lhs=[beta[i]-(colors[v]==i) for i in range(2)]
        rhs=[alpha[v][i]-(colors[v]==i)-sum(alpha[u][i]-(colors[u]==i)
                                                        for u in nearest) for i in range(2)]
        assert lhs==rhs
        for previous in blocks: assert not (block & previous)
        blocks.append(block)
    assert sum(1+sum(weight[w] for w in b) for b in blocks)<=sum(weight)+len(marked)

def contraction_tests():
    cases=0; configurations=0
    # Exhaustive recursively labeled rooted trees with <=3 internal vertices,
    # arities 2 or 3, both output colors, all external-leaf color counts,
    # and every nonempty subset of marked internal vertices.
    for m in range(1,4):
        parent_options=product(*(range(v) for v in range(1,m)))
        for tail in parent_options:
            parents=(-1,)+tail
            nc=[parents.count(v) for v in range(m)]
            for arities in product((2,3),repeat=m):
                if any(arities[v]<nc[v] for v in range(m)): continue
                for first in product(*(range(arities[v]-nc[v]+1) for v in range(m))):
                    local=tuple((first[v],arities[v]-nc[v]-first[v]) for v in range(m))
                    for colors in product((0,1),repeat=m):
                        configurations+=1
                        for mask in range(1,1<<m):
                            marked={v for v in range(m) if mask>>v&1}
                            contraction_check(parents,colors,local,marked); cases+=1
    rng=Random(20260922)
    random_cases=1000
    for _ in range(random_cases):
        m=rng.randrange(4,10)
        parents=(-1,)+tuple(rng.randrange(v) for v in range(1,m))
        colors=tuple(rng.randrange(2) for _ in range(m))
        nc=[parents.count(v) for v in range(m)]
        local=[]
        for v in range(m):
            ext=max(0,2-nc[v])+rng.randrange(4)
            first=rng.randrange(ext+1)
            local.append((first,ext-first))
        marked={v for v in range(m) if rng.randrange(2)} or {0}
        contraction_check(parents,colors,tuple(local),marked)
    return configurations,cases,random_cases

def main():
    configurations,cases,random_cases=contraction_tests()
    den,identities,ng,nh=algebra_tests()
    print('PASS: all finite exact checks completed.')
    print(f'Exhaustive colored-tree configurations: {configurations}')
    print(f'Exhaustive marked-subset contraction checks: {cases}')
    print(f'Additional deterministic random contraction checks: {random_cases}')
    print(f'Forward-recurrence nonzero denominator checks: {den}')
    print(f'Exact component conjugacy/inverse identities: {identities}')
    print(f'Truncation: parameter degree <= {TP}, total spatial degree <= {ZP}')
    print(f'Nonzero terms: forward coordinate {ng}; inverse coordinate {nh}')
    print('No floating point or numerical tolerance was used.')
    print('These checks do not prove the infinite or analytic theorems.')

if __name__=='__main__': main()
