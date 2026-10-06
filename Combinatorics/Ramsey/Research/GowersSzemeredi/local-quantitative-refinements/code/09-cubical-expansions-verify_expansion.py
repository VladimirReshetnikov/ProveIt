#!/usr/bin/env python3
"""Exact finite checks for Arithmetic Circuit Expansions for Cubical Counts.
Python 3.10+, standard library only. Run from any directory; writes results.json
beside this script. These checks supplement, and do not replace, the proofs.
"""
from __future__ import annotations
import itertools as it
import json
import math
from fractions import Fraction as F
from pathlib import Path

class Group:
    def __init__(self, moduli: tuple[int, ...]):
        if any(n < 1 for n in moduli):
            raise ValueError('Moduli must be positive.')
        self.moduli = moduli
        self.elts = list(it.product(*(range(n) for n in moduli)))
        self.n = len(self.elts)
        self.index = {x: i for i, x in enumerate(self.elts)}
        self.add = [[self.index[tuple((a+b)%n for a,b,n in zip(x,y,moduli))]
                     for y in self.elts] for x in self.elts]
        self.neg = [self.index[tuple((-a)%n for a,n in zip(x,moduli))]
                    for x in self.elts]
        self.zero = 0
    def mul(self, k: int, x: int) -> int:
        return self.index[tuple((k*a)%n for a,n in zip(self.elts[x],self.moduli))]
    def sub(self, x: int, y: int) -> int:
        return self.add[x][self.neg[y]]

def conv(g: Group, a: list, b: list) -> list:
    out = [0]*g.n
    for i in range(g.n):
        for j in range(g.n):
            out[g.add[i][j]] += a[i]*b[j]
    return out

def energy4(g: Group, f: list) -> F:
    c = conv(g,f,f)
    return F(sum(x*x for x in c),g.n**3)

def moment5(g: Group, f: list) -> F:
    c3 = conv(g,conv(g,f,f),f)
    return F(sum(f[x]*c3[s]*f[g.sub(s,g.mul(2,x))]
                 for x in range(g.n) for s in range(g.n)),g.n**4)

def quotient_average(g: Group, f: list, r: int) -> tuple[Group,list]:
    q = Group(tuple(math.gcd(n,r) for n in g.moduli))
    sums = [0]*q.n
    for i,x in enumerate(g.elts):
        qi = q.index[tuple(a%n for a,n in zip(x,q.moduli))]
        sums[qi] += f[i]
    return q,[F(a,g.n//q.n) for a in sums]

def torsion2(g: Group, f: list) -> F:
    q,a = quotient_average(g,f,2)
    return energy4(q,a)

def torsion35(g: Group, f: list) -> F:
    q,a = quotient_average(g,f,3)
    a4 = conv(q,conv(q,conv(q,a,a),a),a)
    return F(sum(x*y for x,y in zip(a4,a)),q.n**4)

def coeffs(d: int) -> tuple[int,int,int,int]:
    return ((6**d-2*4**d+2**d)//8,
            (8**d-3*6**d+3*4**d-2**d)//24,
            (8**d-3*6**d+3*4**d-2**d)//6,
            (10**d-4*8**d+6*6**d-4*4**d+2**d)//24)

def cube_coefficients(g: Group, d: int, f: list[int], upto: int=5) -> list[F]:
    m=2**d
    total=[0]*(upto+1)
    for hs in it.product(range(g.n), repeat=d):
        offsets=[g.zero]
        for h in hs:
            offsets += [g.add[z][h] for z in offsets]
        for x in range(g.n):
            e=[1]+[0]*upto
            for j,z in enumerate(offsets):
                y=f[g.add[x][z]]
                for s in range(min(j+1,upto),0,-1):
                    e[s] += y*e[s-1]
            total=[a+b for a,b in zip(total,e)]
    return [F(a,g.n**(d+1)) for a in total]

def run_case(moduli: tuple[int,...],d: int,seed: int) -> dict:
    g=Group(moduli)
    raw=[((i+1)**3+seed*(i+1)**2+3*seed)%17-8 for i in range(g.n)]
    f=[g.n*x-sum(raw) for x in raw]
    assert sum(f)==0
    actual=cube_coefficients(g,d,f,min(5,2**d))
    P,T,Q,S=coeffs(d)
    expected=[F(1),F(0),F(0),F(0),P*energy4(g,f)+T*torsion2(g,f)]
    if d>=3:
        expected.append(Q*moment5(g,f)+S*torsion35(g,f))
    assert actual==expected,(moduli,d,actual,expected)
    return {'moduli':moduli,'d':d,'seed':seed,'f':f,
            'coefficients':[str(a) for a in actual], 'pass':True}

def exact_two_frequency() -> dict:
    vertices=list(it.product((0,1),repeat=3))
    pos=[tuple(i for i,v in enumerate(vertices) if v[k]) for k in range(3)]
    totals={1:[0]*9,-1:[0]*9}
    for a in it.product(range(-2,3),repeat=8):
        if sum(a) or any(sum(a[i] for i in p) for p in pos):
            continue
        degree=sum(v!=0 for v in a)
        parity=sum(abs(v)==2 for v in a)%2
        totals[1][degree]+=1
        totals[-1][degree]+=(-1)**parity
    coeff={s:[F(n,2**j) for j,n in enumerate(a)] for s,a in totals.items()}
    for sign in (1,-1):
        assert coeff[sign]==[F(1),F(0),F(0),F(0),F(3),F(sign,2),F(3,2),F(0),F(1,4)]
    return {str(s):[str(a) for a in v] for s,v in coeff.items()}

def stirling(n: int,k: int) -> int:
    a=[1]+[0]*k
    for _ in range(n):
        a=[0]+[j*a[j]+a[j-1] for j in range(1,k+1)]
    return a[k]

def main() -> None:
    cases=[]
    specs=[((n,),3) for n in range(2,10)]
    specs += [((n,),4) for n in range(2,7)]
    specs += [((2,2),3),((2,3),3),((3,3),3),((2,2),4),((2,3),4)]
    specs += [((n,),2) for n in (2,3,4,5,6,7)]
    for i,(moduli,d) in enumerate(specs):
        cases.append(run_case(moduli,d,i+1))
    for d in range(2,15):
        P,T,Q,S=coeffs(d)
        assert (P,T,Q,S)==(2**(d-2)*stirling(d+1,3),2**(d-2)*stirling(d+1,4),
                          2**d*stirling(d+1,4),2**d*stirling(d+1,5))
        m=2**d
        assert P+T==m*(m-1)*(m-2)//24
    out={'arithmetic':'exact Python integers and fractions.Fraction',
         'cube_cases':cases,'case_count':len(cases),
         'coefficient_formula_checks':'d=2,...,14',
         'two_frequency_U3_polynomial':exact_two_frequency(),
         'all_passed':True}
    path=Path(__file__).with_name('results.json')
    path.write_text(json.dumps(out,indent=2)+'\n')
    print(f'{len(cases)} exact cube cases passed; coefficient identities and two-frequency polynomial passed.')
    print(path)

if __name__=='__main__':
    main()
