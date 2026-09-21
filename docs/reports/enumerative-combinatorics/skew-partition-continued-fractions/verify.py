#!/usr/bin/env python3
"""Exact independent checks for the A225114 article (Python standard library only).

Run: python verify.py --limit 500
The proof is in article.tex/article.pdf; finite checks are regression tests,
not a substitute for its all-orders combinatorial argument.
"""
from __future__ import annotations
import argparse
import csv
import hashlib
import itertools
import json
import math
import random
import time
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parent
OEIS_A = [1,1,3,9,28,87,272,850,2659,8318,26025,81427,254777,
          797175,2494307,7804529,24419909,76408475,239077739,748060606,
          2340639096,7323726778,22915525377,71701378526,224349545236,
          701976998795,2196446204672,6872555567553,21503836486190,
          67284284442622,210528708959146]
OEIS_P = [0,1,2,4,9,20,46,105,242,557,1285,2964,6842,15793,36463,
          84187,194388,448847,1036426,2393208,5526198,12760671,
          29466050,68041019,157115917,362802072,837759792,1934502740,
          4467033943,10314998977,23818760154,55000815222,127004500762]


def divide(num: list[int], den: list[int], n: int) -> list[int]:
    """Power-series division through q**n for a denominator with constant 1."""
    if not den or den[0] != 1:
        raise ValueError('The denominator must have constant term 1.')
    out = [0]*(n+1)
    for k in range(n+1):
        out[k] = (num[k] if k < len(num) else 0) - sum(
            den[j]*out[k-j] for j in range(1, min(k,len(den)-1)+1))
    return out


def multiply(a: list[int], b: list[int], n: int) -> list[int]:
    out=[0]*(n+1)
    for i,x in enumerate(a[:n+1]):
        if x:
            for j,y in enumerate(b[:n+1-i]):
                out[i+j] += x*y
    return out


def continuants(n: int, depth: int | None = None) -> tuple[list[int],list[int]]:
    """S^(depth)=U/V. Each loop processes two partial numerators q**j."""
    m=math.isqrt(n) if depth is None else depth
    if n < 0 or m < 0:
        raise ValueError('Nonnegative limit and depth required.')
    U=[1]+[0]*n
    V=U.copy()
    for j in range(m,0,-1):
        newU=V.copy()
        newV=V.copy()
        for k in range(j,n+1):
            newU[k] -= U[k-j]
            newV[k] -= U[k-j]+V[k-j]
        U,V=newU,newV
    return U,V


def continued_fraction(n: int, depth: int | None = None) -> tuple[list[int],list[int]]:
    U,V=continuants(n,depth)
    S=divide(U,V,n)
    A=divide(V,[2*v-u for u,v in zip(U,V)],n)
    P=S.copy(); P[0]-=1
    return A,P


def row_dp(n: int, zero_overlap: int) -> list[int]:
    """Weighted compositions: transition min(i,j)+zero_overlap.

    zero_overlap=0 counts connected shapes, and 1 counts all nonempty
    normalized shapes. Prefix sums give O(n**2) integer operations.
    """
    f=[[0]*(k+1) for k in range(n+1)]
    for j in range(1,n+1):
        f[j][j]=1
    totals=[0]*(n+1)
    for m in range(1,n+1):
        total=sum(f[m]); totals[m]=total
        prefix=weighted=0
        for j in range(1,n-m+1):
            if j <= m:
                prefix+=f[m][j]
                weighted+=j*f[m][j]
            f[m+j][j] += weighted+j*(total-prefix)+zero_overlap*total
    if zero_overlap == 1:
        totals[0]=1
    return totals


def q_series(n: int) -> tuple[list[int],list[int],list[int]]:
    """Return D=H(q,1), N=H(q,q), A=D/(2D-N), using exact integers."""
    D=[0]*(n+1); N=[0]*(n+1)
    product=[1]+[0]*n
    k=0
    while k*(k+1)//2 <= n:
        if k:
            # Multiply by (1-q**k)^(-2) without rational arithmetic.
            for _ in range(2):
                for j in range(k,n+1):
                    product[j] += product[j-k]
        shift=k*(k+1)//2
        sign=(-1)**k
        for j in range(n-shift+1):
            D[j+shift] += sign*product[j]
        if shift+k <= n:
            for j in range(n-shift-k+1):
                N[j+shift+k] += sign*product[j]
        k+=1
    return D,N,divide(D,[2*d-v for d,v in zip(D,N)],n)


def refined_cf(n: int, s: int, t: int, u: int) -> list[int]:
    """Four-variable formula specialized at integer row/column/component weights."""
    U=[1]+[0]*n
    V=U.copy()
    for j in range(math.isqrt(n),0,-1):
        newU=V.copy(); newV=V.copy()
        for k in range(j,n+1):
            newU[k] -= t*U[k-j]
            newV[k] -= s*V[k-j]+t*U[k-j]
        U,V=newU,newV
    return divide(V,[(1+u*t)*v-u*t*a for a,v in zip(U,V)],n)


def refined_rows(n: int,s: int,t: int,u: int) -> list[int]:
    """Independent row-placement DP, including zero-overlap component weights."""
    f=[[0]*(n+1) for _ in range(n+1)]
    for j in range(1,n+1):
        f[j][j]=u*s*t**j
    for size in range(1,n+1):
        for old in range(1,size+1):
            if not f[size][old]: continue
            for new in range(1,n-size+1):
                placements=u*t**new+sum(t**(new-o)
                                         for o in range(1,min(old,new)+1))
                f[size+new][new] += f[size][old]*s*placements
    return [1]+[sum(f[size]) for size in range(1,n+1)]


def compositions(n: int):
    if n == 0:
        yield ()
    else:
        for first in range(1,n+1):
            for tail in compositions(n-first):
                yield (first,)+tail


def component_polynomials(n: int) -> list[list[int]]:
    """Directly sum u*product(min(l_i,l_(i+1))+u), for n small."""
    rows=[[1]]
    for size in range(1,n+1):
        ans=[0]*(size+1)
        for lengths in compositions(size):
            poly=[0,1]
            for a,b in zip(lengths,lengths[1:]):
                v=min(a,b)
                new=[0]*(len(poly)+1)
                for j,c in enumerate(poly):
                    new[j]+=v*c
                    new[j+1]+=c
                poly=new
            for k,c in enumerate(poly):
                ans[k]+=c
        rows.append(ans)
    return rows


def boundary_counts(max_semiperimeter: int) -> dict[tuple[int,int,int],int]:
    """Enumerate boundary-path pairs; keys are (area,height,width).

    North=1, East=0. The upper path starts N and ends E, the lower
    starts E and ends N, and all interior vertical separations are positive.
    """
    counts={}
    for length in range(2,max_semiperimeter+1):
        for h in range(1,length):
            w=length-h
            interiors=[]
            for positions in itertools.combinations(range(length-2),h-1):
                bits=[0]*(length-2)
                for j in positions: bits[j]=1
                interiors.append(bits)
            for ubits in interiors:
                for lbits in interiors:
                    U=[1]+ubits+[0]
                    L=[0]+lbits+[1]
                    d=area=0
                    ok=True
                    for j,(a,b) in enumerate(zip(U,L)):
                        d+=a-b
                        if j < length-1:
                            if d <= 0:
                                ok=False; break
                            area+=d
                    if ok:
                        assert d == 0
                        key=(area,h,w)
                        counts[key]=counts.get(key,0)+1
    return counts


def dimension_formula(h: int,w: int,k: int) -> int:
    if k < 1 or h < k or w < k: return 0
    L=h+w-k
    top=k*math.comb(L,h)*math.comb(L,w)
    assert top % L == 0
    return top//L


def exact_root_certificate() -> dict:
    """Certify a 20-decimal interval using a finite row transfer matrix.

    P_H is evaluated by its inverse tridiagonal matrix. An explicit norm
    bound bounds P-P_H from above. No floating-point decision is used.
    """
    lo=Fraction('0.31959671805938746551')
    hi=Fraction('0.31959671805938746552')
    H=55
    def bounded(q: Fraction) -> Fraction:
        value=1/(1-q**H)
        for j in range(H-1,0,-1):
            value=1/(2-q**j-value)
        return value-1
    def error(q: Fraction) -> Fraction:
        norm=q/(1-q)**2
        tau=q**(H+1)/(1-q)
        delta=q**(H+1)*((H+1)-H*q)/(1-q)**2
        return tau/(1-norm)+(q/(1-q))*delta/(1-norm)**2
    plo,phi=bounded(lo),bounded(hi)
    elo=error(lo)
    assert plo+elo < 1, 'Lower endpoint not certified.'
    assert phi > 1, 'Upper endpoint not certified.'
    return {'lower':'0.31959671805938746551',
            'upper':'0.31959671805938746552','max_row_length':H,
            'lower_P_H_plus_error_below_one':True,
            'upper_P_H_above_one':True,
            'lower_error_bound_approx':float(elo)}


def main() -> None:
    if not __debug__:
        raise RuntimeError('Run without -O: assertions are required for verification.')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--limit',type=int,default=500)
    args=ap.parse_args()
    n=args.limit
    if n < 40: ap.error('--limit must be at least 40')
    start=time.perf_counter()
    tests={}
    record=json.loads((ROOT/'selection.json').read_text(encoding='utf-8'))
    candidates=json.loads((ROOT/'candidates.json').read_text(encoding='utf-8'))
    digest=hashlib.sha256((ROOT/'candidates.json').read_bytes()).hexdigest()
    assert digest==record['candidate_list_sha256']
    i=random.Random(int(record['seed_decimal'])).randrange(len(candidates))
    assert i==record['zero_based_index'] and candidates[i]['id']=='A225114'
    tests['random_selection_replay']='passed'

    A,P=continued_fraction(n)
    assert A[:len(OEIS_A)]==OEIS_A
    assert P[:len(OEIS_P)]==OEIS_P
    tests['published_A225114_terms']=len(OEIS_A)
    tests['published_A006958_positive_terms']=len(OEIS_P)-1
    assert row_dp(n,1)==A
    assert row_dp(n,0)==P
    tests['independent_row_dynamic_programming_through']=n
    D,N,Aq=q_series(n)
    assert Aq==A
    assert divide(N,D,n)==[p+(j==0) for j,p in enumerate(P)]
    tests['q_series_identity_through']=n
    assert divide([1],[1]+[-x for x in P[1:]],n)==A
    tests['component_sequence_identity_through']=n

    for m in range(13):
        cutoff=(m+1)**2
        full,_=continued_fraction(cutoff+2)
        truncated,_=continued_fraction(cutoff+2,m)
        assert full[:cutoff]==truncated[:cutoff]
        assert full[cutoff]-truncated[cutoff]==1
    tests['sharp_truncation_depths_checked']=list(range(13))

    cp=component_polynomials(13)
    power=[1]+[0]*13
    for k in range(14):
        for size in range(k,14):
            assert cp[size][k]==power[size]
        power=multiply(power,P,13)
    tests['component_polynomials_through']=13
    for s,t,u in itertools.product(range(3),repeat=3):
        assert refined_cf(20,s,t,u)==refined_rows(20,s,t,u)
    tests['four_variable_refinement']='area <= 20 at all (s,t,u) in {0,1,2}^3'

    boundaries=boundary_counts(11)
    for size in range(1,11):
        assert sum(c for (a,h,w),c in boundaries.items() if a==size)==P[size]
    tests['independent_boundary_enumeration_area_through']=10

    # First confirm connected fixed-dimension coefficients by path enumeration.
    for h in range(1,6):
        for w in range(1,6):
            actual=sum(c for (a,r,s),c in boundaries.items() if r==h and s==w)
            assert actual==dimension_formula(h,w,1)
    # Then concatenate k such diagrams and check the closed form for every k.
    H=W=5
    counts=[[0]*(W+1) for _ in range(H+1)]
    for (a,h,w),c in boundaries.items():
        if h<=H and w<=W: counts[h][w]+=c
    power=[[0]*(W+1) for _ in range(H+1)]
    power[0][0]=1
    for k in range(1,6):
        new=[[0]*(W+1) for _ in range(H+1)]
        for h in range(1,H+1):
            for w in range(1,W+1):
                new[h][w]=sum(counts[i][j]*power[h-i][w-j]
                              for i in range(1,h+1) for j in range(1,w+1))
                assert new[h][w]==dimension_formula(h,w,k)
        power=new
    tests['fixed_height_width_components_formula']='h,w <= 5; k <= 5'

    tests['root_certificate']=exact_root_certificate()
    # A sufficient finite lower bound for P(1/3)>1 used in the proof.
    assert sum(Fraction(P[j],3**j) for j in range(1,8))>1
    tests['seven_term_P_one_third_lower_bound']=str(
        sum(Fraction(P[j],3**j) for j in range(1,8)))
    tests['elapsed_seconds']=round(time.perf_counter()-start,3)
    tests['status']='ALL EXACT CHECKS PASSED'
    (ROOT/'verification_results.json').write_text(json.dumps(tests,indent=2)+'\n')
    with (ROOT/'coefficients.csv').open('w',newline='') as stream:
        writer=csv.writer(stream)
        writer.writerow(['n','A225114','connected_A006958'])
        writer.writerows((j,A[j],P[j]) for j in range(n+1))
    with (ROOT/'components.csv').open('w',newline='') as stream:
        writer=csv.writer(stream)
        writer.writerow(['n','k','number'])
        for size,row in enumerate(cp):
            writer.writerows((size,k,c) for k,c in enumerate(row) if c)
    print(json.dumps(tests,indent=2))

if __name__=='__main__':
    main()
