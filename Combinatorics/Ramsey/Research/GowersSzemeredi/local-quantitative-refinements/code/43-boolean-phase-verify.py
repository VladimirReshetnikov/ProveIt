#!/usr/bin/env python3
"""Exact finite checks for Boolean Phase Integration.

Python 3 standard library only.  No floating-point arithmetic is used in the
mathematical checks.  These tests supplement, rather than replace, the proofs.
Run from any working directory: python3 checks/verify.py
"""
from __future__ import annotations

import itertools as it
import json
import math
from pathlib import Path
import random
import sys
import time
from fractions import Fraction

if not __debug__:
    raise RuntimeError("Run without -O: these exact checks require assertions.")

ROOT = Path(__file__).resolve().parents[1]
SEED = 20261006


def sign_quad(a: int, b: int) -> int:
    """Exact sign of a+b*sqrt(2)."""
    if a == 0:
        return (b > 0) - (b < 0)
    if b == 0:
        return (a > 0) - (a < 0)
    if (a > 0) == (b > 0):
        return 1 if a > 0 else -1
    c = (a*a > 2*b*b) - (a*a < 2*b*b)
    return c if a > 0 else -c


def binary_rank(rows: list[int], n: int) -> int:
    rows = rows[:]
    rank = 0
    for j in range(n):
        pivot = next((i for i in range(rank, len(rows)) if rows[i] >> j & 1), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        for i in range(len(rows)):
            if i != rank and rows[i] >> j & 1:
                rows[i] ^= rows[rank]
        rank += 1
    return rank


def tensor(n: int, coeff: dict[tuple[int, ...], int], hs: tuple[int, ...]) -> int:
    out = 0
    for inds, c in coeff.items():
        if c and all(h >> i & 1 for h, i in zip(hs, inds)):
            out ^= 1
    return out


def symmetric_tensor(n: int, d: int, mask: int) -> dict[tuple[int, ...], int]:
    orbits = list(it.combinations_with_replacement(range(n), d))
    vals = {inds: mask >> j & 1 for j, inds in enumerate(orbits)}
    return {inds: vals[tuple(sorted(inds))] for inds in it.product(range(n), repeat=d)}


def cube_coeffs(n: int, hs: tuple[int, ...], x: int) -> tuple[int, ...]:
    coeff = [0] * (1 << n)
    d = len(hs)
    for mask in range(1 << d):
        v = x
        for i, h in enumerate(hs):
            if mask >> i & 1:
                v ^= h
        coeff[v] += (-1) ** (d - mask.bit_count())
    return tuple(coeff)


def exact_cubic_census() -> dict:
    n, N = 2, 4
    tuples = list(it.product(range(N), repeat=3))
    cube_rows = [cube_coeffs(n, hs, x) for hs in tuples for x in range(N)]
    phase_exponents = []
    for tail in it.product(range(8), repeat=N-1):
        phase = (0,) + tail
        phase_exponents.append([sum(c*q for c, q in zip(row, phase)) % 8
                                for row in cube_rows])
    records = []
    checks = 0
    for mask in range(16):
        coeff = symmetric_tensor(n, 3, mask)
        signs = [4*tensor(n, coeff, hs) for hs in tuples for _ in range(N)]
        D = [sum((tensor(n, coeff, (1<<i, 1<<i, 1<<j)) ^
                  tensor(n, coeff, (1<<i, 1<<j, 1<<j))) << j for j in range(n))
             for i in range(n)]
        rank = binary_rank(D, n)
        target = Fraction(1, 1 << (rank//2))
        best = (-1, 0)
        attained = 0
        for exps in phase_exponents:
            hist = [0]*8
            for x, s in zip(exps, signs):
                hist[(x+s) % 8] += 1
            # Exact eighth-root sum, denominator 2*N^4.
            a = 2*(hist[0]-hist[4])
            b = hist[1]+hist[7]-hist[3]-hist[5]
            ia = 2*(hist[2]-hist[6])
            ib = hist[1]+hist[3]-hist[5]-hist[7]
            assert ia == ib == 0, (mask, hist)
            assert sign_quad(a, b) >= 0
            assert sign_quad(a*target.denominator-2*N**4*target.numerator,
                             b*target.denominator) <= 0
            if sign_quad(a-best[0], b-best[1]) > 0:
                best = (a, b)
                attained = 1
            elif (a, b) == best:
                attained += 1
            checks += 1
        assert best[1] == 0 and Fraction(best[0], 2*N**4) == target
        records.append({'tensor_mask': mask, 'defect_rank': rank,
                        'maximum_energy': str(target), 'maximizing_grid_phases': attained})
    return {'tensor_count': 16, 'phase_count_per_tensor': 512,
            'exact_energy_checks': checks, 'records': records}


def nonsymmetric_census() -> dict:
    n, N = 2, 4
    tuples = list(it.product(range(N), repeat=3))
    rows = [cube_coeffs(n, hs, x) for hs in tuples for x in range(N)]
    phases = []
    for tail in it.product(range(4), repeat=3):
        q = (0,)+tail
        phases.append([sum(a*b for a,b in zip(row,q)) % 4 for row in rows])
    nonsym, checks, largest = 0, 0, Fraction(0)
    for mask in range(256):
        inds = list(it.product(range(n), repeat=3))
        coeff = {v: mask >> i & 1 for i,v in enumerate(inds)}
        symmetric = all(coeff[v] == coeff[tuple(sorted(v))] for v in inds)
        if symmetric:
            continue
        nonsym += 1
        shifts = [2*tensor(n, coeff, hs) for hs in tuples for _ in range(N)]
        for exps in phases:
            hist = [0]*4
            for e,s in zip(exps,shifts):
                hist[(e+s)%4] += 1
            assert hist[1] == hist[3]
            E = Fraction(hist[0]-hist[2], N**4)
            assert 0 <= E <= Fraction(3,4)
            largest = max(largest,E)
            checks += 1
    assert nonsym == 240 and largest == Fraction(3,4)
    return {'nonsymmetric_tensors': nonsym, 'phase_count_per_tensor': 64,
            'exact_energy_checks': checks, 'maximum_energy': str(largest)}


def additive_derivative(values: tuple[int, ...], hs: tuple[int, ...], modulus: int) -> tuple[int, ...]:
    out = values
    for h in hs:
        out = tuple((out[x^h]-out[x]) % modulus for x in range(len(out)))
    return out


def integration_checks() -> dict:
    records = []
    for d in range(2,6):
        n, N, modulus = 2, 4, 1 << d
        supports = [S for S in range(1,1<<n) if S.bit_count() <= d]
        inputs = list(it.product(range(N), repeat=d))
        next_inputs = list(it.product(range(N), repeat=d+1))
        tested = 0
        for mask in range(1<<len(supports)):
            cs = {S: mask>>j & 1 for j,S in enumerate(supports)}
            values = tuple(sum(c*(1<<(S.bit_count()-1))
                               for S,c in cs.items() if x & S == S) % modulus
                           for x in range(N))
            coeff = {inds: cs[sum(1<<i for i in set(inds))]
                     for inds in it.product(range(n), repeat=d)}
            for hs in inputs:
                actual = additive_derivative(values,hs,modulus)
                expected = (modulus//2)*tensor(n,coeff,hs)
                assert all(x == expected for x in actual), (d,mask,hs)
                tested += N
            for hs in next_inputs:
                assert not any(additive_derivative(values,hs,modulus))
                tested += N
        records.append({'degree': d, 'integrable_tensors': 1<<len(supports),
                        'top_and_next_derivative_point_checks': tested})
    return {'records': records}


def support_and_endpoints() -> dict:
    records=[]
    for p in (2,3,5):
        for k in range(1,6):
            zeros=sum(math.prod(t)%p == 0 for t in it.product(range(p),repeat=k))
            E=Fraction(zeros,p**k)
            assert E == 1-Fraction(p-1,p)**k
            records.append({'prime':p,'k':k,'nonsymmetric_endpoint':str(E)})
    symmetric=[]
    for d in range(3,8):
        k=d-1
        zeros=0
        for hs in it.product(range(4),repeat=k):
            # C_d: one second-coordinate factor, all other factors first-coordinate.
            coeff_y=math.prod(h&1 for h in hs)
            coeff_x=sum(((hs[i]>>1)&1)*math.prod(hs[j]&1 for j in range(k) if j!=i)
                        for i in range(k))%2
            zeros += coeff_x == coeff_y == 0
        E=Fraction(zeros,4**k)
        expected=1-Fraction(d+1,1<<d)
        assert E == expected
        symmetric.append({'degree':d,'explicit_nonintegrable_energy':str(E),
                          'proved_profile_upper_bound':str(1-Fraction(1,1<<(d-2)))})
    return {'nonsymmetric_endpoints':records,'symmetric_lower_bounds':symmetric}


def mul(a: tuple[int,int],b: tuple[int,int]) -> tuple[int,int]:
    return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])


def conj(a: tuple[int,int]) -> tuple[int,int]:
    return (a[0],-a[1])


def mdiff(f: tuple[tuple[int,int],...],hs: tuple[int,...]) -> tuple[tuple[int,int],...]:
    out=f
    for h in hs:
        out=tuple(mul(out[x^h],conj(out[x])) for x in range(len(out)))
    return out


def shear_checks() -> dict:
    rng=random.Random(SEED)
    cases=0
    for d in (3,4):
        for trial in range(12):
            # Actual values are numerators / 2. Products on both sides have
            # the same denominator 2^(2^d), so compare integer numerators.
            f=tuple(rng.choice(((0,0),(1,0),(-1,0),(0,1),(1,1),(2,0))) for _ in range(4))
            for z in it.product(range(4),repeat=d-3):
                for a,b,w in it.product(range(4),repeat=3):
                    left=mdiff(f,(a,a^w,b)+z)
                    fw=tuple(mul(f[x],f[x^w]) for x in range(4))
                    right=tuple(conj(q) for q in mdiff(fw,(a,b)+z))
                    assert left == right
                    cases += 4
    return {'pointwise_gaussian_integer_checks':cases,
            'amplitudes_include_zero_and_nonunit_values':True}


def cubic_rank_and_subspaces() -> dict:
    records=[]
    for m in range(4):
        n=2*m
        N=1<<n
        zero=0
        for a,b in it.product(range(N),repeat=2):
            good=True
            for j in range(m):
                ax=(a>>(2*j))&1; ay=(a>>(2*j+1))&1
                bx=(b>>(2*j))&1; by=(b>>(2*j+1))&1
                if ax*bx or (ax*by+ay*bx)%2:
                    good=False;break
            zero += good
        E=Fraction(zero,N*N)
        assert E == Fraction(1,1<<m)
        records.append({'half_rank':m,'dimension':n,'maximum_attained_by_constant':str(E)})
    repairs=[]
    for n in range(1,5):
        subspaces={frozenset((0,))}
        frontier=set(subspaces)
        while frontier:
            new=set()
            for U in frontier:
                for v in range(1<<n):
                    W=U|frozenset(x^v for x in U)
                    if W not in subspaces:
                        new.add(W)
            subspaces |= new
            frontier=new
        for m in range(n//2+1):
            def D(a,b):
                return sum(((a>>(2*j)&1)*(b>>(2*j+1)&1)+
                            (a>>(2*j+1)&1)*(b>>(2*j)&1)) for j in range(m))%2
            largest=max(len(U) for U in subspaces if all(D(a,b)==0 for a in U for b in U))
            assert largest == 1<<(n-m)
            repairs.append({'dimension':n,'half_rank':m,'all_subspaces':len(subspaces),
                            'minimum_repair_codimension':m})
    return {'canonical_cubic_extremizers':records,'exhaustive_subspace_checks':repairs}


def composite_checks() -> dict:
    records=[]
    for modulus in (2,3,4,5,6,8,9,10,12,16,18):
        for s in range(modulus):
            g=math.gcd(modulus,s)
            radical=sum((s*a)%modulus == (s*b)%modulus == 0
                         for a,b in it.product(range(modulus),repeat=2))
            assert radical == g*g
            D=modulus//g
            assert modulus*modulus//radical == D*D
            E=Fraction(sum((s*a)%modulus==0 for a in range(modulus)),modulus)
            assert E == Fraction(1,D)
            records.append({'modulus':modulus,'coefficient':s,'radical_size':radical,
                            'representation_dimension':D,'constant_energy':str(E)})
    return {'canonical_composite_bilinear_cases':len(records),'records':records}



def root8_components(hist: list[int]) -> tuple[int,int,int,int]:
    """Sum roots has ((a+b sqrt2)+i(c+d sqrt2))/2."""
    return (2*(hist[0]-hist[4]), hist[1]+hist[7]-hist[3]-hist[5],
            2*(hist[2]-hist[6]), hist[1]+hist[3]-hist[5]-hist[7])


def mixed_correlations() -> dict:
    # Sharp triangle example: B(a,b)=a_1 b_2, g=1, k(x)=i^{x_1}.
    # h(b)=zeta_8^{-1} for b_2=0; zeta_8*(-1)^{b_1} otherwise.
    hist=[0]*8
    for a,b in it.product(range(4),repeat=2):
        h=7 if not (b>>1&1) else 1+4*(b&1)
        k=2*((a^b)&1)
        exponent=(h+k+4*(a&1)*(b>>1&1))%8
        hist[exponent]+=1
    re0,re1,im0,im1=root8_components(hist)
    assert (re0,re1,im0,im1)==(0,16,0,0)
    # Dividing by 2*16 gives sqrt(2)/2. Its fourth power is 1/4,
    # exactly the bias of B-B^t.
    rng=random.Random(SEED+1)
    checked=0
    for mask in range(16):
        coeff=symmetric_tensor(2,3,mask)
        D=[sum((tensor(2,coeff,(1<<i,1<<i,1<<j)) ^
                tensor(2,coeff,(1<<i,1<<j,1<<j)))<<j for j in range(2))
           for i in range(2)]
        half_rank=binary_rank(D,2)//2
        for trial in range(64):
            fs=[[rng.randrange(8) for _ in range(4)] for _ in range(7)]
            hist=[0]*8
            for x,y,z in it.product(range(4),repeat=3):
                arguments=(x,y,z,x^y,x^z,y^z,x^y^z)
                exp=sum(f[v] for f,v in zip(fs,arguments))+4*tensor(2,coeff,(x,y,z))
                hist[exp%8]+=1
            a,b,c,d=root8_components(hist)
            r=a*a+2*b*b+c*c+2*d*d
            s=2*(a*b+c*d)
            # squared correlation <= 2^{-half_rank}; denominator (2*64)^2.
            assert sign_quad((r<<half_rank)-128**2,s<<half_rank)<=0
            checked+=1
    return {'sharp_triangle_correlation':'sqrt(2)/2',
            'sharp_triangle_alternating_bias':'1/4',
            'exact_seven_function_inequality_checks':checked}


def quartic_checks() -> dict:
    from collections import Counter
    coeff=symmetric_tensor(2,4,2)
    tuples=list(it.product(range(4),repeat=4))
    poly=Counter()
    rows=[]; shifts=[]
    for hs in tuples:
        t=tensor(2,coeff,hs)
        for x in range(4):
            plus=[0]*4;minus=[0]*4
            for mask in range(16):
                v=x
                for i,h in enumerate(hs):
                    if mask>>i&1:v^=h
                (plus if mask.bit_count()%2==0 else minus)[v]+=1
            poly[(tuple(plus),tuple(minus))]+=(-1)**t
            rows.append(tuple(a-b for a,b in zip(plus,minus)))
            shifts.append(8*t)
    expected=Counter()
    for i,j in it.product(range(4),repeat=2):
        plus=[0]*4;minus=[0]*4
        plus[i]=8;minus[j]=8
        expected[(tuple(plus),tuple(minus))]+=1
    for i,j in it.combinations(range(4),2):
        v=tuple(4 if k in (i,j) else 0 for k in range(4))
        expected[(v,v)]+=28
    expected[((2,2,2,2),(2,2,2,2))]+=480
    for pair,c in (((0,1),12),((0,3),12),((0,2),-4)):
        plus=tuple(4 if k in pair else 0 for k in range(4))
        minus=tuple(4-v for v in plus)
        expected[(plus,minus)]+=c
        expected[(minus,plus)]+=c
    assert dict(poly)==dict(expected)
    assert sum(poly.values())==704
    best=Fraction(-1);count=0
    for tail in it.product(range(16),repeat=3):
        q=(0,)+tail;hist=[0]*16
        for row,shift in zip(rows,shifts):
            exp=(sum(a*b for a,b in zip(row,q))+shift)%16
            hist[exp]+=1
        assert all(c==0 for i,c in enumerate(hist) if i%4)
        assert hist[4]==hist[12]
        E=Fraction(hist[0]-hist[8],1024)
        assert E<=Fraction(11,16)
        if E>best:best=E;count=1
        elif E==best:count+=1
    assert best==Fraction(11,16)
    return {'cube_terms_checked':1024,'distinct_monomials':len(poly),
            'sixteenth_root_phase_checks':4096,'phase_grid_maximum':str(best),
            'maximizing_grid_phases':count,
            'monomial_certificate':[{'f_powers':u,'conjugate_powers':v,'coefficient':c}
                                    for (u,v),c in sorted(poly.items())]}

def main() -> None:
    start=time.monotonic()
    functions=[('cubic_census',exact_cubic_census),
               ('nonsymmetric_census',nonsymmetric_census),
               ('integration',integration_checks),
               ('shear',shear_checks),
               ('endpoints',support_and_endpoints),
               ('cubic_repairs',cubic_rank_and_subspaces),
               ('composite',composite_checks),
               ('mixed_correlations',mixed_correlations),
               ('quartic',quartic_checks)]
    result={'status':'passed','arithmetic':'exact integers, rational numbers, and Q(sqrt(2))',
            'seed':SEED,'python_version':sys.version.split()[0],
            'scope':'Finite supplementary tests, not a formal proof of the general theorems.'}
    for name,fn in functions:
        result[name]=fn()
        print(f'{name}: passed',flush=True)
    result['elapsed_seconds']=round(time.monotonic()-start,3)
    out=ROOT/'data'/'verification.json'
    out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(f'Wrote {out}')


if __name__=='__main__':
    main()
