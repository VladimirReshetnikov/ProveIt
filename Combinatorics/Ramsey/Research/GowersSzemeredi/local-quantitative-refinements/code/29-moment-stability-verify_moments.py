#!/usr/bin/env python3
"""Independent exact finite checks for the autocorrelation norm bounds.

Only Python's standard library is required. All pass/fail arithmetic is
integer or Fraction. Cube powers are evaluated from vertex products,
independently of the derivative/Jensen and Fourier-monomial proof.
These finite diagnostics do not replace the written general proof.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
from math import comb, prod
from pathlib import Path
from random import Random
import json


class Group:
    def __init__(self, moduli):
        self.moduli = tuple(moduli)
        self.points = tuple(product(*(range(n) for n in moduli)))
        self.n = len(self.points)
        lookup = {x: i for i, x in enumerate(self.points)}
        self.add = tuple(tuple(lookup[tuple((x+y) % n for x,y,n in
                                           zip(a,b,self.moduli))]
                               for b in self.points) for a in self.points)
        self.neg = tuple(lookup[tuple(-x % n for x,n in zip(a,self.moduli))]
                         for a in self.points)
        self.double_image = tuple(sorted({self.add[x][x] for x in range(self.n)}))


def autocorrelation(g, f):
    return tuple(F(sum(f[x]*f[g.add[x][h]] for x in range(g.n)), g.n)
                 for h in range(g.n))


def u2_power(g, f):
    return sum((c*c for c in autocorrelation(g, f)), F(0))/g.n


def cube_power_direct(g, f, d):
    total = 0
    for increments in product(range(g.n), repeat=d):
        offsets = [0]
        for h in increments:
            offsets += [g.add[a][h] for a in offsets]
        for x in range(g.n):
            total += prod(f[g.add[x][a]] for a in offsets)
    return F(total, g.n**(d+1))


def torsion_projection(g, f):
    h = g.double_image
    return tuple(sum((F(f[g.add[x][t]]) for t in h), F(0))/len(h)
                 for x in range(g.n))


def profile_bound(m, st, sp):
    return sum((F(comb(2*m, 2*k)*comb(2*k,k))*st**(m-k)*(sp/2)**k
                for k in range(m+1)), F(0))


def convolution(g, a, b):
    out = defaultdict(F)
    for x, u in a.items():
        for y, v in b.items():
            out[g.add[x][y]] += u*v
    return dict(out)


def fourier_moment(g, lam, r):
    acc = {0: F(1)}
    for _ in range(r):
        acc = convolution(g, acc, lam)
    return acc.get(0, F(0))


def norm_checks():
    rng = Random(20261006)
    rows = []
    # Odd, mixed-torsion, and pure two-torsion groups are all represented.
    for mods in ((3,), (4,), (5,), (7,), (2,2), (2,3), (3,3)):
        g = Group(mods)
        for trial in range(3):
            raw = [rng.randrange(-2,3) for _ in range(g.n)]
            f = tuple(g.n*x-sum(raw) for x in raw)
            if not any(f):
                f = tuple(g.n*(x==0)-1 for x in range(g.n))
            S = u2_power(g, f)
            st = u2_power(g, torsion_projection(g, f))
            assert 0 <= st <= S
            c = autocorrelation(g, f)
            for d in (2,3,4):
                m = 2**(d-2)
                full = cube_power_direct(g, f, d)
                moment = sum((x**(2*m) for x in c), F(0))/g.n
                bound = profile_bound(m, st, S-st)
                assert full >= moment >= bound, (mods,trial,d,full,moment,bound)
                if g.n % 2:
                    assert st == 0
                    assert moment >= F(comb(2*m,m),2**m)*S**m
                rows.append({'group': list(mods), 'trial': trial, 'd':d,
                             'S': str(S), 'torsion_ratio': str(st/S),
                             'full_over_moment': str(full/moment),
                             'moment_over_profile':str(moment/bound)})
        if len(g.double_image)>1 and g.n%2==0:
            # Remove the entire self-inverse spectrum, not only the mean.
            raw = tuple(rng.randrange(-3,4) for _ in range(g.n))
            projection = torsion_projection(g,raw)
            f = tuple(len(g.double_image)*(F(x)-y) for x,y in zip(raw,projection))
            if any(f):
                assert all(x==0 for x in torsion_projection(g,f))
                S = u2_power(g,f)
                d=4;m=4
                full=cube_power_direct(g,f,d)
                assert full >= F(35,8)*S**4
                rows.append({'group':list(mods),'d':d,'case':'self_inverse_spectrum_removed',
                             'U4_sixteenth_over_S_fourth':str(full/S**4)})
    return rows


def sharp_moment_checks():
    rows=[]
    for m in (1,2,4,8,16):
        p=2*m+1  # Primality is unnecessary; order exceeds every exponent.
        g=Group((2,p))
        involution=p
        pos=1
        neg=p-1
        for a,b in ((0,1),(1,0),(1,1),(2,1),(1,3)):
            lam={x:F(v) for x,v in ((involution,a),(pos,b),(neg,b)) if v}
            S=F(a*a+2*b*b)
            st=F(a*a)
            actual=fourier_moment(g,lam,2*m)
            expected=profile_bound(m,st,S-st)
            assert actual==expected,(m,a,b,actual,expected)
            rows.append({'m':m,'group':[2,p],'involution_weight':a,'pair_weight':b,
                         'torsion_ratio':str(st/S),'exact_moment':str(actual)})
    return rows


def spectrum_checks():
    rng=Random(20261007)
    count=0
    for mods in ((3,), (5,), (7,), (9,), (2,2), (2,3), (2,5), (3,3)):
        g=Group(mods)
        for _ in range(10):
            lam={}
            for x in range(1,g.n):
                if x not in lam:
                    lam[x]=lam[g.neg[x]]=F(rng.randrange(4))
            S=sum((a*a for a in lam.values()),F(0))
            st=sum((a*a for x,a in lam.items() if g.neg[x]==x),F(0))
            for m in (1,2,3,4,5,8):
                actual=fourier_moment(g,lam,2*m)
                assert actual>=profile_bound(m,st,S-st)
                count+=1
    return count


def lower_family_checks():
    rows=[]
    for n in range(1,51):
        N=2*n+1
        g=Group((N,))
        f=(0,)+(1,)*n+(-1,)*n
        c=autocorrelation(g,f)
        assert sum(f)==0 and max(map(abs,f))==1
        assert c[0]==F(N-1,N)
        for h in range(1,n+1):
            assert c[h]==c[N-h]==F(N-4*h,N)
        S=u2_power(g,f)
        assert S==F(1,3)-F(4,3*N*N)+F(1,N**3)
        rows.append({'N':N,'U2_fourth_power':str(S)})
    return rows


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result={'status':'PASS','arithmetic':'integer/Fraction only',
            'scope':'Finite diagnostics; general theorems require the written proofs.',
            'direct_norm_cases':norm_checks(),
            'exact_sharp_autocorrelation_cases':sharp_moment_checks(),
            'additional_fourier_profile_checks':spectrum_checks(),
            'odd_cyclic_lower_family':lower_family_checks()}
    result['direct_norm_case_count']=len(result['direct_norm_cases'])
    result['exact_sharp_autocorrelation_case_count']=len(result['exact_sharp_autocorrelation_cases'])
    result['odd_cyclic_lower_family_case_count']=len(result['odd_cyclic_lower_family'])
    content=json.dumps(result,indent=2)+'\n'
    if args.output:
        args.output.write_text(content)
    print(json.dumps({k:v for k,v in result.items() if not isinstance(v,list)},indent=2))


if __name__=='__main__':
    main()
