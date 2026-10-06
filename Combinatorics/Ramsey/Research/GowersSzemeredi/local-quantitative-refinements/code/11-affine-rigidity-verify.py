#!/usr/bin/env python3
"""Exact finite checks for the accompanying article. Python 3, standard library.
These checks supplement, not replace, the proofs. No floating-point comparisons.
"""
from __future__ import annotations
from collections import Counter
from fractions import Fraction
from itertools import product, combinations
from pathlib import Path
import argparse
import json
import random


def group_table(p: int, n: int = 1):
    pts = list(product(range(p), repeat=n))
    idx = {x: i for i, x in enumerate(pts)}
    add = [[idx[tuple((a+b) % p for a,b in zip(x,y))] for y in pts] for x in pts]
    return pts, add


def energy(f, add, modulus):
    """Graph additive energy via derivative collision counts."""
    total = 0
    for row in add:
        freq = Counter((f[row[x]] - f[x]) % modulus for x in range(len(f)))
        total += sum(c*c for c in freq.values())
    return total


def set_energy(support, add):
    S = set(support)
    return sum(sum(x in S and row[x] in S for x in range(len(add))) ** 2 for row in add)


def closest_affine(f, pts, p):
    n = len(pts[0]); N = len(pts)
    return min(sum(f[i] != (sum(a*b for a,b in zip(coeff,x))+c) % p
                   for i,x in enumerate(pts))
               for coeff in product(range(p), repeat=n) for c in range(p))


def exhaustive_normal_forms(p, n):
    pts, add = group_table(p,n); N = len(pts)
    fixed = {0}
    for j in range(n):
        e = tuple(int(i==j) for i in range(n)); fixed.add(pts.index(e))
    free = [i for i in range(N) if i not in fixed]
    maximum = -1; extremizers = 0; count = 0; histogram = Counter()
    kappa = int(p == 2)
    target = N**3-4*N*N+(10+2*kappa)*N-(6+2*kappa)
    for values in product(range(p), repeat=len(free)):
        f = [0]*N
        for i,v in zip(free,values): f[i] = v
        E = energy(f,add,p); histogram[E] += 1; count += 1
        if any(f):
            assert E <= target, (p,n,f,E,target)
            if E > maximum: maximum=E; extremizers=1
            elif E == maximum: extremizers+=1
            if E == target: assert closest_affine(f,pts,p) == 1, (p,n,f)
        else:
            assert E == N**3
    return dict(p=p, dimension=n, N=N, normal_forms=count,
                affine_orbit_size=p**(n+1), total_maps_represented=p**N,
                nonaffine_maximum=maximum, predicted_maximum=target,
                extremal_normal_forms=extremizers,
                extremal_maps=extremizers*p**(n+1),
                energy_histogram_normal_forms=dict(sorted(histogram.items())))


def monochromatization_check(f, add, q):
    N=len(f); S=[i for i,v in enumerate(f) if v]; s=len(S)
    if not s: return
    assert 7*s < N
    mono=[int(i in S) for i in range(N)]
    E=energy(f,add,q); Em=energy(mono,add,q); Es=set_energy(S,add)
    counts=Counter(v for v in f if v)
    A=s*s-sum(c*c for c in counts.values())
    assert Em-E >= 2*(N-7*s)*A, (N,q,f,Em-E,2*(N-7*s)*A)
    expected_defect=4*s*N*N-10*s*s*N+12*s**3-6*Es
    assert N**3-Em == expected_defect
    lower=4*s*N*N-10*s*s*N+6*s**3
    lower+=6*(s**3-Es)+2*(N-7*s)*A
    assert N**3-E >= lower


def sparse_checks(seed=20261006):
    count=0
    # Exhaust all nonzero labelings of all two-point supports on Z/17Z into Z/5Z.
    pts,add=group_table(17)
    for S in combinations(range(17),2):
        for vals in product(range(1,5),repeat=2):
            f=[0]*17
            for i,v in zip(S,vals): f[i]=v
            monochromatization_check(f,add,5); count+=1
    # Seeded, exact-arithmetic examples across odd/even domain orders and vector groups.
    rng=random.Random(seed)
    for p,n,q in [(23,1,3),(29,1,5),(41,1,7),(3,3,5),(5,2,3),(2,5,9)]:
        pts,add=group_table(p,n); N=len(pts)
        for _ in range(300):
            s=rng.randint(1,(N-1)//7)
            S=rng.sample(range(N),s); f=[0]*N
            for i in S: f[i]=rng.randrange(1,q)
            monochromatization_check(f,add,q); count+=1
    return dict(seed=seed, sparse_cases=count, exhaustive_two_point_cases=2176,
                random_cases=1800)


def equality_checks():
    results=[]
    for p,n in [(3,3),(5,2),(11,2)]:
        pts,add=group_table(p,n); N=len(pts)
        # A subgroup of codimension 2 has density <1/7 in all these cases.
        S=[i for i,x in enumerate(pts) if x[0]==0 and x[1]==0]
        f=[int(i in S) for i in range(N)]
        E=energy(f,add,p); s=len(S)
        assert N**3-E == 4*s*N*N-10*s*s*N+6*s**3
        monochromatization_check(f,add,p)
        results.append(dict(p=p,n=n,N=N,s=s,energy=E,defect=str(Fraction(N**3-E,N**3))))
    # Characteristic-two target deliberately has a different sharp one-point value.
    pts,add=group_table(17); f=[1]+[0]*16
    E2=energy(f,add,2)
    assert E2==17**3-4*17**2+12*17-8
    return dict(subgroup_cosets=results,two_torsion_target_counterexample=dict(N=17,energy=E2))



def two_torsion_checks(seed=20261007):
    rng=random.Random(seed); count=0
    for p,n,q in [(17,1,2),(23,1,4),(29,1,6),(2,5,8),(3,3,10)]:
        pts,add=group_table(p,n); N=len(pts)
        for _ in range(200):
            s=rng.randint(1,(N-1)//3); S=rng.sample(range(N),s)
            f=[0]*N
            for i in S: f[i]=rng.randrange(1,q)
            mono=[q//2 if i in S else 0 for i in range(N)]
            counts=Counter(v for v in f if v)
            M=sum(v*v for v in counts.values())
            C=sum(v*counts.get((-b)%q,0) for b,v in counts.items())
            A=s*s-M; J=M-C
            assert J>=0
            E=energy(f,add,q); Em=energy(mono,add,q); Es=set_energy(S,add)
            assert Em-E >= 6*(N-3*s)*A+2*(N-2*s)*J
            assert N**3-Em == 4*s*N*N-12*s*s*N+16*s**3-8*Es
            count+=1
    return dict(seed=seed,cases=count)

def inverse_coefficients(terms=8):
    from math import comb
    coeff=[]
    for n in range(1,terms+1):
        s=sum(Fraction(comb(n+j-1,j)*comb(2*n-j-2,n-1-j))*Fraction(3,2)**(n-1-j)
              for j in range(n))
        coeff.append(s/(n*4**n))
    # Independently substitute into 4d-10d^2+6d^3, truncated exactly.
    d=[Fraction(0)]+coeff
    def mul(a,b):
        out=[Fraction(0)]*(terms+1)
        for i,x in enumerate(a):
            for j,y in enumerate(b):
                if i+j<=terms: out[i+j]+=x*y
        return out
    d2=mul(d,d);d3=mul(d2,d)
    assert [4*d[i]-10*d2[i]+6*d3[i] for i in range(terms+1)] == [0,1]+[0]*(terms-1)
    return [str(x) for x in coeff]


def main():
    if not __debug__:
        raise RuntimeError('Run without -O: the checks require Python assertions.')
    ap=argparse.ArgumentParser(); ap.add_argument('--output',type=Path,default=Path('verification_results.json'))
    args=ap.parse_args()
    results=dict(exhaustive=[exhaustive_normal_forms(p,n) for p,n in [(2,2),(2,3),(3,1),(5,1),(7,1),(3,2)]],
                 sparse=sparse_checks(),two_torsion=two_torsion_checks(),equality=equality_checks(),inverse_coefficients=inverse_coefficients(),
                 status='All exact assertions passed.')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results,indent=2)+'\n', encoding='utf-8')
    print(json.dumps({k:v for k,v in results.items() if k!='exhaustive'},indent=2))
    for x in results['exhaustive']:
        print({k:v for k,v in x.items() if k!='energy_histogram_normal_forms'})

if __name__=='__main__': main()
