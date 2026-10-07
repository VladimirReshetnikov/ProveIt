#!/usr/bin/env python3
"""Exact finite checks for Exact Odd-Order Cube Stability.

Python >=3.10; standard library only. No network, floating-point tests, or
external theorem prover. Run from any directory; outputs go beside this file.
The inequalities are proved in the article. These tests are independent checks.
"""
from __future__ import annotations
from collections import Counter
from fractions import Fraction as Q
from itertools import combinations, permutations, product
from math import comb, prod
from pathlib import Path
import argparse
import json
import random
import time

V = list(product(range(2), repeat=3))
ROWS = [(1,) + v for v in V]

def det(a: list[tuple[int, ...]]) -> int:
    n = len(a)
    return sum((-1) ** sum(p[i] > p[j] for i in range(n) for j in range(i+1,n))
               * prod(a[i][p[i]] for i in range(n)) for p in permutations(range(n)))

def mask_of(items) -> int:
    return sum(1 << j for j in items)

FOURS = {mask_of(s): abs(det([ROWS[i] for i in s])) for s in combinations(range(8),4)}
RECT = [s for s,d in FOURS.items() if d == 0]
FIVES = [mask_of(s) for s in combinations(range(8),5)]
P5 = [s for s in FIVES if any(p & s == p for p in RECT)]

def b(k: int) -> int:
    return comb(k-1,4) if k >= 5 else 0

def sigma(mask: int) -> int:
    return 48*b(mask.bit_count()) - 35*sum(s & mask == s for s in P5)

SIGMA = [sigma(mask) for mask in range(256)]

def group(mods: tuple[int,...]):
    points = list(product(*(range(m) for m in mods)))
    idx = {x:i for i,x in enumerate(points)}
    add = [[idx[tuple((a+b)%m for a,b,m in zip(x,y,mods))] for y in points] for x in points]
    chars = [[(-1)**sum(bit*(x[j]%2) for bit,j in zip(bits,even)) for x in points]
             for even in [[j for j,m in enumerate(mods) if m%2 == 0]]
             for bits in product(range(2),repeat=len(even))]
    return points,add,chars

def cube_vertices(add, x: int, a: int, b_: int, c: int) -> list[int]:
    # Corresponding exactly to lexicographic product(range(2), repeat=3).
    return [x,add[x][c],add[x][b_],add[add[x][b_]][c],
            add[x][a],add[add[x][a]][c],add[add[x][a]][b_],
            add[add[add[x][a]][b_]][c]]

def poly(h, r):
    return h**4-8*r*h**3+28*r*r*h*h-44*r**3*h+23*r**4

def pdelta(d):
    return 4*d-10*d*d+8*d**3

def bernstein_sigma(z):
    """Independent positional Bernoulli extension, even at coincident vertices."""
    return sum(SIGMA[m]*prod(z[i] if m>>i&1 else 1-z[i] for i in range(8))
               for m in range(256) if SIGMA[m])

def full_weighted_check(mods, f):
    points,add,chars = group(mods)
    h=len(points); r=sum(f)
    E=sum(f[x]*f[add[x][a]]*f[add[x][b_]]*f[add[add[x][a]][b_]]
          for x,a,b_ in product(range(h),repeat=3))
    C=Q(0); W48=Q(0); tail=Q(0)
    for x,a,b_,c in product(range(h),repeat=4):
        z=[f[i] for i in cube_vertices(add,x,a,b_,c)]
        C+=prod(1-t for t in z)
        W48+=bernstein_sigma(z)
        # Independent inclusion-exclusion polynomial, using elementary symmetric sums.
        es=[Q(1)]+[Q(0)]*8
        for v in z:
            for j in range(8,0,-1): es[j]+=v*es[j-1]
        tail+=sum((-1)**j*es[j] for j in range(5,9))
    W=W48/48
    B=sum(sum(t*ch for t,ch in zip(f,chi))**4 for chi in chars[1:])
    e=r**3-E
    assert W>=0 and e>=0
    assert tail == -35*r*E-W, (mods,f,'tail')
    assert C == poly(h,r)+2*B-(12*h-35*r)*e-W, (mods,f,'identity')
    if B==0 and 0<r<Q(12*h,35): assert C<=poly(h,r)
    return {'group':list(mods),'f':[str(x) for x in f], 'mass':str(r),
            'energy_defect':str(e),'parity':str(B),'remainder':str(W),
            'complement_cubes':str(C)}

def all_set_counts(mods):
    points,add,chars=group(mods); h=len(points)
    C=[0]*(1<<h); E=[0]*(1<<h)
    for x,a,b_ in product(range(h),repeat=3):
        base=[x,add[x][a],add[x][b_],add[add[x][a]][b_]]
        E[sum({1<<i for i in base})]+=1
        for c in range(h):
            mask=0
            for i in base: mask|=(1<<i)|(1<<add[i][c])
            C[mask]+=1
    for bit in range(h):
        for mask in range(1<<h):
            if mask>>bit&1:
                E[mask]+=E[mask^(1<<bit)]
                C[mask]+=C[mask^(1<<bit)]
    eq=0; small=0; max_ratio=None
    for mask in range(1<<h):
        r=mask.bit_count(); e=r**3-E[mask]
        B=sum(sum(chi[i] for i in range(h) if mask>>i&1)**4 for chi in chars[1:])
        # This rearranged W is only a consequence test, not the independent identity check.
        inferred_W=poly(h,r)+2*B-(12*h-35*r)*e-C[((1<<h)-1)^mask]
        assert inferred_W>=0, (mods,mask,'remainder-sign')
        assert C[mask]<=r*E[mask]<=r**4
        if B==0 and 0<r<Q(12*h,35):
            small+=1
            assert C[((1<<h)-1)^mask]<=poly(h,r)
            is_eq=C[((1<<h)-1)^mask]==poly(h,r)
            assert is_eq==(e==0)
            eq+=is_eq
        if e and r:
            ratio=Q(C[((1<<h)-1)^mask]-poly(h,r)-2*B+12*h*e,r*e)
            max_ratio=ratio if max_ratio is None else max(max_ratio,ratio)
    return {'group':list(mods),'subsets':1<<h,'small_parity_balanced_cases':small,
            'equalities':eq,'largest_observed_tail_ratio':str(max_ratio)}

def finite_certificate():
    assert Counter(FOURS.values()) == {0:12,1:56,2:2}
    assert len(P5)==48
    for k in (1,2,3):
        for ss in combinations(range(8),k):
            s=mask_of(ss)
            assert any(t&s==s and d==1 for t,d in FOURS.items())
    assert all(sum(p&s==p for p in RECT)<=1 for s in FIVES)
    # Every five-set has a unimodular basis.
    assert all(any(t&s==t and d==1 for t,d in FOURS.items()) for s in FIVES)
    # On each rectangle, any three vertices plus the outside point form such a basis.
    for s in P5:
        rect=next(p for p in RECT if p&s==p)
        extra=(s^rect).bit_length()-1
        verts=[i for i in range(8) if rect>>i&1]
        assert all(abs(det([ROWS[i] for i in (*triple,extra)]))==1
                   for triple in combinations(verts,3))
    assert min(SIGMA)==0
    assert all((SIGMA[m]==0)==(m.bit_count()<=4 or m==255) for m in range(256))
    census=Counter((m.bit_count(),sum(s&m==s for s in P5),SIGMA[m]) for m in range(256))
    # Verify cap affine relation up to cube symmetry.
    cap0=mask_of([V.index(v) for v in [(0,0,0),(1,0,0),(0,1,0),(0,0,1),(1,1,1)]])
    orbit=set()
    for perm in permutations(range(3)):
        for flip in product(range(2),repeat=3):
            orbit.add(mask_of(V.index(tuple(V[i][perm[j]]^flip[j] for j in range(3)))
                              for i in range(8) if cap0>>i&1))
    assert orbit==set(FIVES)-set(P5)
    return [{'vertices':k,'P5_count':p,'sigma':s,'multiplicity':v}
            for (k,p,s),v in sorted(census.items())]

# Minimal exact multivariate polynomial operations (no CAS dependency).
def padd(*ps):
    d=Counter()
    for p in ps:
        for m,c in p.items(): d[m]+=c
    return {m:c for m,c in d.items() if c}
def pscale(p,c): return {m:c*v for m,v in p.items() if c*v}
def pmul(p,q):
    d=Counter()
    for (a,b),c in p.items():
        for (u,v),e in q.items(): d[a+u,b+v]+=c*e
    return {m:c for m,c in d.items() if c}
def ppow(p,k):
    out={(0,0):1}
    for _ in range(k): out=pmul(out,p)
    return out

def polynomial_checks():
    one={(0,0):1}; d={(1,0):1}; y={(0,1):1}
    x=padd(d,pscale(y,-1)); v=padd(one,pscale(y,-1))
    F=padd(ppow(v,4),pscale(pmul(x,ppow(v,3)),-4),
           pscale(pmul(ppow(x,2),ppow(v,2)),10),pscale(pmul(ppow(x,3),v),-8),
           pscale(pmul(padd(one,x,pscale(y,-1)),ppow(y,3)),14),ppow(y,4))
    F0=padd(one,pscale(d,-4),pscale(ppow(d,2),10),pscale(ppow(d,3),-8))
    G={(1,0):-8,(0,1):4,(2,0):4,(1,1):4,(0,2):10,
       (3,0):8,(2,1):-14,(1,2):22,(0,3):-28}
    assert padd(F,pscale(F0,-1))==pmul(y,G)
    assert 4-18*Q(1,50)-30*Q(1,50)**2>Q(7,2)
    # Formal series reversion through degree six.
    cs=[Q(0),Q(1,4),Q(5,32),Q(21,128),Q(425,2048),Q(2371,8192),Q(28105,65536)]
    def mul(a,b):
        return [sum(a[j]*b[i-j] for j in range(i+1)) for i in range(7)]
    c2=mul(cs,cs);c3=mul(c2,cs)
    assert [4*cs[i]-10*c2[i]+8*c3[i] for i in range(7)]==[0,1,0,0,0,0,0]
    return {'mixed_difference':'exactly verified','inverse_coefficients':[str(c) for c in cs[1:]]}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--quick',action='store_true',help='omit exhaustive order 11--13 and some weighted cases')
    ap.add_argument('--output',type=Path,default=Path(__file__).resolve().parent/'results.json')
    args=ap.parse_args();start=time.monotonic()
    census=finite_certificate(); polynomials=polynomial_checks()
    mods_list=[(1,),(2,),(3,),(4,),(2,2),(5,),(6,),(7,),(8,),(2,4),(2,2,2),(9,),(3,3),(10,)]
    if not args.quick: mods_list += [(11,),(12,),(2,6),(13,)]
    exhaustive=[]
    for mods in mods_list:
        row=all_set_counts(mods);exhaustive.append(row)
        print('exhaustive',mods,row['subsets'],'OK',flush=True)
    weighted=[]
    weighted_cases=[((1,),[Q(1,3)]),((2,),[Q(1,3),Q(2,3)]),
                    ((3,),[Q(1),Q(0),Q(0)]),((3,),[Q(1,2),Q(1,3),Q(1,4)]),
                    ((4,),[Q(1),Q(0),Q(0),Q(0)]),
                    ((4,),[Q(1,2),Q(1,4),Q(0),Q(1,4)]),
                    ((2,2),[Q(1,4)]*4),
                    ((5,),[Q(1),Q(1),Q(0),Q(0),Q(0)])]
    if not args.quick:
        rng=random.Random(20261007)
        for mods in [(5,),(6,),(2,3),(3,3)]:
            weighted_cases.append((mods,[Q(rng.randrange(5),4) for _ in range(prod(mods))]))
    for mods,f in weighted_cases:
        weighted.append(full_weighted_check(mods,f));print('independent weighted',mods,'OK',flush=True)
    # Sparse base-B examples: elementary count, not numerical floating point.
    sparse=[]
    for m in range(1,7):
        A=[10**i for i in range(m)]; counts=Counter(a+b_ for a in A for b_ in A)
        E=sum(c*c for c in counts.values()); assert E==2*m*m-m
        cap=sum(a+b_+c==d+2*e for a,b_,c,d,e in product(A,repeat=5))
        assert cap==3*m*m-2*m
        sparse.append({'m':m,'energy':E,'cap_solutions':cap})
    report={'status':'all exact checks passed','proof_status':'Finite tests; not a kernel-checked theorem.',
            'boolean_patterns':256,'four_subset_determinants':dict(Counter(FOURS.values())),
            'five_subsets':56,'P5_count':48,'pattern_census':census,
            'exhaustive_groups':exhaustive,'total_subsets':sum(r['subsets'] for r in exhaustive),
            'independent_weighted_identity_tests':weighted,'polynomial_checks':polynomials,
            'sparse_examples':sparse,'elapsed_seconds':round(time.monotonic()-start,3)}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    certdir=Path(__file__).resolve().parents[1]/'certificates';certdir.mkdir(exist_ok=True)
    (certdir/'boolean_patterns.json').write_text(json.dumps([
        {'mask':m,'vertices':[list(V[i]) for i in range(8) if m>>i&1],
         'P5_count':sum(s&m==s for s in P5),'sigma':SIGMA[m]} for m in range(256)],indent=2)+'\n')
    print('ALL CHECKS PASSED:',report['total_subsets'],'subsets;',len(weighted),'independent weighted cases',flush=True)

if __name__=='__main__': main()
