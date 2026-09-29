#!/usr/bin/env python3
"""Exact independent checks for the parallel-three-edge-path family.

Standard library only. The all-m proof is in article.tex; Sturm computations
below are finite checks, not the basis of that proof.
"""
from __future__ import annotations
from fractions import Fraction as F
from math import comb
from pathlib import Path
import json
from verify import check, pm_polynomial, gamma_to_h, direct_h, derivative, evaluate

ROOT=Path(__file__).resolve().parents[1]

def theta_neighbors(m: int) -> list[int]:
    check(m>=1, 'm must be positive')
    # A=(a_1,...,a_m,d), B=(b_0,b_1,...,b_m).
    return [(1<<m)-1]+[(1<<i)|(1<<m) for i in range(m)]

def theta_polynomial(m: int) -> list[int]:
    if m==1: return [1,3,1]
    a=[0]*(m+2)
    q=[1,2*m+3,m*m+m+3,1]
    for i in range(m-1):
        for j,c in enumerate(q): a[i+j]+=comb(m-2,i)*c
    a[1]-=1
    return a

def clean(a):
    while len(a)>1 and not a[-1]: a.pop()
    return a

def remainder(a,b):
    a=list(map(F,a)); b=clean(list(map(F,b)))
    while len(a)>=len(b) and any(a):
        d=len(a)-len(b); c=a[-1]/b[-1]
        for i,v in enumerate(b): a[d+i]-=c*v
        clean(a)
    return a

def sturm(a):
    seq=[list(map(F,a)),list(map(F,derivative(a)))]
    while any(seq[-1]):
        rem=[-x for x in remainder(seq[-2],seq[-1])]
        if not any(rem): break
        # Positive normalization controls coefficient growth without sign changes.
        c=abs(rem[-1]); seq.append([x/c for x in rem])
    return seq

def variations(seq,neg_inf: bool):
    signs=[]
    for a in seq:
        s=1 if a[-1]>0 else -1
        if neg_inf and (len(a)-1)%2: s=-s
        signs.append(s)
    return sum(x!=y for x,y in zip(signs,signs[1:]))

def run():
    rows=[]
    for m in range(1,21):
        p=theta_polynomial(m); seq=sturm(p)
        real=variations(seq,True)-variations(seq,False)
        expected=m+1 if m<=2 else (1 if m%2==0 else 2)
        check(real==expected, f'Sturm root count failed at m={m}')
        if m<=9:
            check(pm_polynomial(m+1,theta_neighbors(m))==p,
                  f'Matching support formula failed at m={m}')
        h=gamma_to_h(p,2*m+2)
        if m<=4:
            check(direct_h(m+1,theta_neighbors(m))==h,
                  f'Direct lattice count failed at m={m}')
        rows.append({'m':m,'gamma':p,'h':h,'real_gamma_roots':real,
                     'real_h_roots':2*real,'nonreal_h_roots':2*m+2-2*real,
                     'sturm_variations_minus_infinity':variations(seq,True),
                     'sturm_variations_plus_infinity':variations(seq,False)})
    p=theta_polynomial(3); x=F(-1,4)
    vals=[evaluate(p,x),evaluate(derivative(p),x),evaluate(derivative(derivative(p)),x)]
    defect=vals[1]**2-vals[0]*vals[2]
    check(vals==[F(1,256),F(-1,16),F(99,4)] and defect==F(-95,1024),
          'Eight-element certificate mismatch')
    out={'rows':rows,'eight_element':{'neighbors':theta_neighbors(3),
         'evaluation_at_minus_one_quarter':list(map(str,vals)),
         'laguerre_defect':str(defect),'lattice_points':sum(rows[2]['h'])},
         'all_tests_passed':True}
    (ROOT/'data'/'theta_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'all_tests_passed':True,'tested_m':list(range(1,21)),
                      'eight_element':out['eight_element']},indent=2))
if __name__=='__main__': run()
