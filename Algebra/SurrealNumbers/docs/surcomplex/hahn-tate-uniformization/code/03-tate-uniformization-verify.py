#!/usr/bin/env python3
"""Exact finite checks for the formal Tate node chart.

Uses only the Python standard library. Polynomials are dictionaries of integer
coefficients, truncated by total degree. These tests do not prove any infinite
summability assertion, arbitrary-rank theorem, or novelty claim.

Usage: python verify.py --degree 12 --output verification.json
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from time import perf_counter
from typing import Dict, Tuple

Exp = Tuple[int, int]
Poly = Dict[Exp, int]

class Ring:
    def __init__(self, degree: int):
        self.n = degree
    def clean(self, p: Poly) -> Poly:
        return {e:c for e,c in p.items() if c and sum(e) <= self.n}
    def add(self, *ps: Poly) -> Poly:
        out: Poly = {}
        for p in ps:
            for e,c in p.items():
                out[e] = out.get(e,0) + c
        return self.clean(out)
    def scale(self, p: Poly, c: int) -> Poly:
        return self.clean({e:c*a for e,a in p.items()})
    def mul(self, p: Poly, q: Poly) -> Poly:
        out: Poly = {}
        for (i,j),a in p.items():
            for (k,l),b in q.items():
                if i+j+k+l <= self.n:
                    e=(i+k,j+l)
                    out[e] = out.get(e,0)+a*b
        return self.clean(out)
    def powers(self, p: Poly, n: int) -> list[Poly]:
        out=[{(0,0):1}]
        for _ in range(n):
            out.append(self.mul(out[-1],p))
        return out
    def comp(self, p: Poly, a: Poly, b: Poly) -> Poly:
        if not p:
            return {}
        aa=self.powers(a,max(e[0] for e in p))
        bb=self.powers(b,max(e[1] for e in p))
        out: Poly={}
        for (i,j),c in p.items():
            out=self.add(out,self.scale(self.mul(aa[i],bb[j]),c))
        return out
    def homog(self, p: Poly, d: int) -> Poly:
        return {e:c for e,c in p.items() if sum(e)==d}
    def monofn(self, e: Exp, fn: str) -> Poly:
        d=sum(e)
        assert d>0
        out: Poly={}
        for m in range(1,self.n//d+1):
            c = m if fn=='f' else (m*(m-1)//2 if fn=='g' else m*(m+1)//2)
            if c:
                out[(m*e[0],m*e[1])]=c
        return out

def serial(p: Poly, max_degree: int | None=None) -> list[dict]:
    return [{'powers':list(e),'coefficient':c}
            for e,c in sorted(p.items(),key=lambda z:(sum(z[0]),-z[0][0]))
            if max_degree is None or sum(e)<=max_degree]

def pretty(p: Poly, vars=('x','y'), max_degree=4) -> str:
    terms=[]
    for item in serial(p,max_degree):
        i,j=item['powers']; c=item['coefficient']
        mon='*'.join(v+(f'^{e}' if e!=1 else '') for v,e in zip(vars,(i,j)) if e)
        a=str(abs(c)) if abs(c)!=1 or not mon else ''
        term=(a+('*' if a and mon else '')+mon)
        terms.append((' - ' if c<0 else ' + ')+term)
    return ''.join(terms).lstrip(' +') or '0'

def run(n: int) -> dict:
    if n < 4 or n > 18:
        raise ValueError('degree must be between 4 and 18 (12 is recommended)')
    start=perf_counter()
    r=Ring(n); x={(1,0):1}; y={(0,1):1}; q={(1,1):1}
    X=r.monofn((1,0),'f'); Y=r.monofn((1,0),'g')
    for j in range(1,(n+1)//2+1):
        X=r.add(X,r.monofn((j+1,j),'f'),r.monofn((j-1,j),'f'),r.scale(r.monofn((j,j),'f'),-2))
        Y=r.add(Y,r.monofn((j+1,j),'g'),r.scale(r.monofn((j-1,j),'h'),-1),r.monofn((j,j),'f'))
    a4: Poly={}; a6: Poly={}
    # Here q is represented as the first variable to permit later composition.
    for d in range(1,n+1):
        sig3=sum(m**3 for m in range(1,d+1) if d%m==0)
        sig5=sum(m**5 for m in range(1,d+1) if d%m==0)
        numerator=5*sig3+7*sig5
        assert numerator%12==0
        a4[(d,0)]=-5*sig3
        a6[(d,0)]=-numerator//12
    def curve(Q: Poly,A: Poly,B: Poly) -> Poly:
        return r.add(r.mul(B,B),r.mul(A,B),r.scale(r.mul(r.mul(A,A),A),-1),
                     r.scale(r.mul(r.comp(a4,Q,{}),A),-1),r.scale(r.comp(a6,Q,{}),-1))
    checks={}
    checks['curve_identity_F_UV_X_Y']=not curve(q,X,Y)
    U=r.add(x,y); V=r.scale(y,-1)
    for d in range(2,n+1):
        rx=r.homog(r.add(r.comp(X,U,V),r.scale(x,-1)),d)
        ry=r.homog(r.add(r.comp(Y,U,V),r.scale(y,-1)),d)
        U=r.add(U,r.scale(rx,-1),r.scale(ry,-1))
        V=r.add(V,ry)
    checks['X_of_inverse_equals_x']=r.comp(X,U,V)==x
    checks['Y_of_inverse_equals_y']=r.comp(Y,U,V)==y
    checks['U_of_chart_equals_U']=r.comp(U,X,Y)==x
    checks['V_of_chart_equals_V']=r.comp(V,X,Y)==y
    Q=r.mul(U,V)
    checks['inverse_parameter_solves_curve']=not curve(Q,x,y)
    # Swap U,V corresponds to u -> q/u, hence to inversion modulo q^Z.
    swap=lambda p:{(j,i):c for (i,j),c in p.items()}
    checks['node_X_swap_invariant']=swap(X)==X
    checks['node_Y_swap_negation']=swap(Y)==r.scale(r.add(X,Y),-1)
    if not all(checks.values()):
        raise AssertionError(json.dumps(checks,indent=2))
    return {
        'arithmetic':'exact integers; Python standard library only',
        'modulus':f'(x,y)^{n+1}: coefficients of total degree 0 through {n}',
        'degree':n,
        'monomials_per_identity':(n+1)*(n+2)//2,
        'checks':checks,
        'number_of_identity_checks':len(checks),
        'total_coefficient_equalities':len(checks)*(n+1)*(n+2)//2,
        'seconds':round(perf_counter()-start,3),
        'node_X_degree4':pretty(X,('U','V')),
        'node_Y_degree4':pretty(Y,('U','V')),
        'inverse_U_degree4':pretty(U),
        'inverse_V_degree4':pretty(V),
        'inverse_Q_degree4':pretty(Q),
        'inverse_U_terms':serial(U),
        'inverse_V_terms':serial(V),
        'inverse_Q_terms':serial(Q),
        'limitations':'Finite polynomial checks only. Not a formal proof of the infinite identities, Hahn summability, surjectivity, value-rank statements, or research novelty.'
    }

def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--degree',type=int,default=12)
    parser.add_argument('--output',type=Path,default=Path('verification.json'))
    args=parser.parse_args()
    result=run(args.degree)
    args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    for key,value in result['checks'].items():
        print(f'PASS {key}')
    print(result['inverse_U_degree4'])
    print(result['inverse_V_degree4'])
    print(result['inverse_Q_degree4'])
    print(f"{result['total_coefficient_equalities']} exact coefficient equalities; {result['seconds']} seconds.")
    print(f'Results: {args.output.resolve()}')

if __name__=='__main__':
    main()
