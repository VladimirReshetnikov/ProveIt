#!/usr/bin/env python3
"""Independent finite Laurent-block checks of the noncommutative scalar operator.

Unlike verify.py's matrix tests, this applies E + z/L, the scalar polynomials,
and the normalized block inverse G to sparse Laurent series. It checks every
projected word through the finite Q+k budget at jet order 3 for a=+/-1.
Only x exponents 0..3 are needed because all other transfers go downward.
L exponents below -10 are guarded away; after entering the invariant negative
L block, a further GA cannot increase its maximum exponent. This is a finite
regression test, not an independent proof for general Hahn series.
"""
from __future__ import annotations
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
import json
import sympy as sp

XMIN, LMIN, KMAX = 0, -10, 3
# (x exponent, L exponent, z degree) -> exact rational coefficient
Series = dict[tuple[int,int,int], F]
t,z,a=sp.symbols('t z a')


def clean(s: Series) -> Series:
    return {k:v for k,v in s.items() if v and k[0]>=XMIN and k[1]>=LMIN and k[2]<=KMAX}


def plus(*ss: Series) -> Series:
    out: Series={}
    for s in ss:
        for key,value in s.items(): out[key]=out.get(key,F(0))+value
    return clean(out)


def scale(s: Series, c: F) -> Series:
    return clean({k:c*v for k,v in s.items()})


def euler(s: Series, with_z: bool) -> Series:
    out: Series={}
    def add(key,value): out[key]=out.get(key,F(0))+value
    for (alpha,beta,k),c in s.items():
        add((alpha,beta,k),alpha*c)
        add((alpha,beta-1,k),beta*c)
        if with_z: add((alpha,beta-1,k+1),c)
    return clean(out)


def polynomial(s: Series, p: sp.Expr, with_z: bool) -> Series:
    out: Series={}
    for c in sp.Poly(p,t).all_coeffs():
        out=plus(euler(out,with_z),scale(s,F(c)))
    return out


def multiply_residue(s: Series, eta: int) -> Series:
    return clean({(alpha-eta,beta-1,k):c for (alpha,beta,k),c in s.items()})


P=t*(t-1)*(t-2)*(t-3)
D=[-6,2,-2,6]


@lru_cache(None)
def inverse_coefficients(alpha: int, order: int) -> tuple[F,...]:
    q=sp.cancel(P.subs(t,alpha+t)/t)
    terms=[F(sp.expand(q).coeff(t,j)) for j in range(4)]
    cs=[1/terms[0]]
    for j in range(1,order+1):
        cs.append(-sum(terms[h]*cs[j-h] for h in range(1,min(j,3)+1))/terms[0])
    return tuple(cs)


def G(s: Series) -> Series:
    out: Series={}
    for (alpha,beta,k),c in s.items():
        assert 0<=alpha<=3  # All retained blocks are simple roots.
        if beta==-1: continue  # GJ=0.
        b=beta+1
        base=c/F(b)
        fall=F(1)
        for j,coef in enumerate(inverse_coefficients(alpha,b-LMIN)):
            if j: fall*=b-j+1
            if not fall: break
            exponent=b-j
            if exponent==0: continue  # Normalization Lambda G=0.
            key=(alpha,exponent,k)
            out[key]=out.get(key,F(0))+base*coef*fall
    return clean(out)


def A(s: Series, av: int) -> Series:
    q1=-t*(t-2)*((av+9)*t-av-27)/3
    q2=t*(t-1)*(10*t-29)/3
    return plus(polynomial(s,P,True),scale(polynomial(s,P,False),F(-1)),
                multiply_residue(polynomial(s,q1,True),1),
                multiply_residue(polynomial(s,q2,True),2))


def residue_matrix_column(s: Series, k: int) -> list[F]:
    return [s.get((i,-1,k),F(0)) for i in range(4)]


def main() -> None:
    checks=0
    for av in [-1,1]:
        B=sp.Matrix([[0,1,1,0],[0,0,0,1],[0,0,0,av],[0,0,0,0]])
        N=sp.diag(*D)*B
        for source in range(4):
            v={(source,0,0):F(1)}
            for q in range(1,3+KMAX+1):
                w=A(v,av)
                for k in range(KMAX+1):
                    got=residue_matrix_column(w,k)
                    expected=[F(0)]*4
                    if q==1:
                        if k==0: expected=[F(N[i,source]) for i in range(4)]
                        if k==1: expected[source]=F(D[source])
                    if got!=expected:
                        raise AssertionError((av,source,q,k,got,expected))
                    checks+=1
                v=G(w)
    result={'status':'PASS','exact_column_checks':checks,'jet_degree':KMAX,
            'maximum_word_length':3+KMAX,'lowest_retained_L_exponent':LMIN,
            'specializations':[-1,1],
            'scope':'Finite noncommutative scalar-operator regression checks; not a full infinite-support proof.'}
    dest=Path(__file__).resolve().parent/'operator_results.json'
    dest.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
