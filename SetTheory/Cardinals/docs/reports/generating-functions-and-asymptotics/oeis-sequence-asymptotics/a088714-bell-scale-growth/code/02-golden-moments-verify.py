#!/usr/bin/env python3
"""Exact finite audits for A088714/A088713. The article proves the all-index results.
Uses Python 3.10+ standard library only. Run from any directory.
"""
from __future__ import annotations
import argparse
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations
from math import comb, log
from pathlib import Path
import json
import sys
import time

ROOT = Path(__file__).resolve().parents[1]

def coefficients(nmax: int) -> list[int]:
    """Composition-iterate triangular recurrence, O(N^3) integer products."""
    if type(nmax) is not int or nmax < 0:
        raise ValueError('nmax must be a nonnegative integer')
    rows = [[1] * (nmax + 2)]
    out = [1]
    for n in range(1, nmax + 1):
        row = [0] * (nmax - n + 2)
        for k in range(1, len(row)):
            row[k] = row[k-1] + sum(rows[i][k] * rows[n-1-i][k+1]
                                    for i in range(n))
        rows.append(row)
        out.append(row[1])
    return out

def mul(a, b, N):
    out = [0] * (N+1)
    for i, x in enumerate(a[:N+1]):
        for j, y in enumerate(b[:N+1-i]):
            out[i+j] += x*y
    return out

def compose(a, b, N):
    if b[0] != 0:
        raise ValueError('formal inner series must have zero constant coefficient')
    out = [0] * (N+1)
    for x in reversed(a[:N+1]):
        out = mul(out, b, N)
        out[0] += x
    return out

def renewal(a):
    c = [1]
    for n in range(1, len(a)):
        c.append(sum(a[j]*c[n-1-j] for j in range(n)))
    return c

def nc_moments(c):
    """First-block noncrossing recurrence M=C(z M), coefficient-by-coefficient."""
    N = len(c)-1
    m = [1]+[0]*N
    for n in range(1, N+1):
        power = [1]+[0]*N
        v = 0
        for k in range(1,n+1):
            power = mul(power,m,N)
            v += c[k]*power[n-k]
        m[n] = v
    return m

def bareiss(mat):
    """Exact integer determinant with pivoting; no floating-point decisions."""
    a = [list(row) for row in mat]
    n = len(a)
    if n == 0: return 1
    sign, previous = 1, 1
    for k in range(n-1):
        if not a[k][k]:
            p = next((p for p in range(k+1,n) if a[p][k]),None)
            if p is None: return 0
            a[k],a[p]=a[p],a[k]; sign = -sign
        pivot = a[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                value = a[i][j]*pivot-a[i][k]*a[k][j]
                quotient, remainder = divmod(value,previous)
                if remainder: raise ArithmeticError('Bareiss exact division failed')
                a[i][j]=quotient
        for i in range(k+1,n): a[i][k]=0
        previous=pivot
    return sign*a[-1][-1]

def fock_check(N=10):
    """Direct full-Fock operator on words for rho=(delta_1+delta_3)/2.
    Functions on {1,3} use their values as coordinates, weighted inner product.
    Exact rationals; only word lengths <=N can occur.
    """
    v={():Q(1)}
    moments=[Q(1)]
    for _ in range(N):
        w=defaultdict(Q)
        for word, amp in v.items():
            w[word]+=2*amp                      # c_1 times the identity
            for t in (1,3): w[(t,)+word]+=t*amp # creation by t
            if word:
                t=word[0]
                w[word]+=t*amp                 # gauge T
                w[word[1:]]+=Q(t,2)*amp        # annihilation by t
        v=dict(w); moments.append(v.get((),Q(0)))
    c=[Q(1)]+[Q(1+3**k,2) for k in range(1,N+1)]
    assert moments==nc_moments(c)
    return [str(x) for x in moments]

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--n',type=int,default=401)
    p.add_argument('--output',type=Path,default=ROOT/'data')
    args=p.parse_args()
    if args.n < 100: p.error('--n must be at least 100 for all audits')
    if hasattr(sys,'set_int_max_str_digits'): sys.set_int_max_str_digits(0)
    args.output.mkdir(parents=True,exist_ok=True)
    start=time.perf_counter()
    a=coefficients(args.n); c=renewal(a)
    known_a=[1,1,3,13,69,419,2809,20353,157199,1281993,10963825,
             97828031,907177801,8716049417,86553001779,886573220093,
             9351927111901,101447092428243,1130357986741545,
             12923637003161409,151479552582252239]
    known_c=[1,1,2,6,24,118,674,4308,30062,225266,1791964,15009118,131566314,1201452248,11389283418,111761444078,1132680800640,11834071103246,127261591139010,1406778021294220,15967144849210158,185897394076705298]
    assert a[:len(known_a)]==known_a
    assert c[:len(known_c)]==known_c
    report={'max_n':args.n,'known_OEIS_a_terms':len(known_a),
            'known_OEIS_c_terms':len(known_c)}
    N=30; ap=a[:N+1]; bp=[0]+ap[:N]
    assert [1]+mul(mul(ap,ap,N),compose(ap,bp,N),N)[:N]==ap
    assert nc_moments(c[:N+1])==ap
    report['independent_functional_and_NC_check_degree']=N
    N=16; b=[1]+[0]*N; histories=[]
    for r in range(1,N+1):
        b=nc_moments(renewal(b))
        assert b[:r+1]==a[:r+1]
        histories.append({'r':r,'prefix':b[:8]})
    report['compact_iteration_stabilization_through_stage']=N
    report['iteration_prefixes']=histories[:6]
    report['direct_Fock_moments']=fock_check()
    minors=0
    leading={}
    for label,seq in [('A088714',a),('A088713',c)]:
        leading[label]={}
        for shift in (0,1):
            ds=[]
            for k in range(1,11):
                d=bareiss([[seq[i+j+shift] for j in range(k)] for i in range(k)])
                assert d>0; ds.append(str(d))
            leading[label][str(shift)]=ds
        for k in range(1,5):
            inds=list(combinations(range(8),k))
            for rows in inds:
                for cols in inds:
                    d=bareiss([[seq[i+j] for j in cols] for i in rows])
                    assert d>0
                    minors+=1
    report['positive_generalized_Hankel_minors_checked']=minors
    report['leading_Hankel_determinants']=leading
    for k in range(10):
        assert leading['A088713']['1'][k]==leading['A088714']['0'][k]
        expected='1' if k==0 else leading['A088714']['1'][k-1]
        assert leading['A088713']['0'][k]==expected
    report['renewal_determinant_identities_checked']=20
    lcount=0
    for seq in (a[:101],c[:101]):
        for r in range(1,7):
            seq=[seq[i]*seq[i+2]-seq[i+1]**2 for i in range(len(seq)-2)]
            assert all(x>0 for x in seq)
            lcount+=len(seq)
    report['positive_iterated_logconvex_values_checked']=lcount
    report['logconvex_iterations']=6
    with (args.output/'coefficients.csv').open('w') as out:
        out.write('n,A088714,A088713\n')
        for n,(x,y) in enumerate(zip(a,c)): out.write(f'{n},{x},{y}\n')
    diagnostics=[]
    for n in (20,50,100,200,400):
        if n>=len(a)-1: continue
        diagnostics.append({'n':n,'A088714_ratio_scaled':(a[n+1]/a[n])*log(n)/n,
                            'A088713_ratio_scaled':(c[n+1]/c[n])*log(n)/n,
                            'A088714_root_log_error':log(a[n])/n-log(n)+log(log(n))+1})
    report['diagnostics']=diagnostics
    report['wall_seconds']=round(time.perf_counter()-start,3)
    report['status']='PASS (finite audits only; not a formal proof)'
    (args.output/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
    text=[report['status'],f'Coefficients generated independently: n=0..{args.n}',
          f'Functional equation and NC transform checked through degree 30',
          f'Stabilization checked through stage 16; direct Fock operator through moment 10',
          f'Positive generalized Hankel minors: {minors}',
          f'Leading and shifted Hankel determinants: 40 (orders 1..10, both sequences)',
          f'Positive iterated log-convexity values: {lcount} (6 iterations)',
          f'Wall time: {report["wall_seconds"]} seconds']
    (args.output/'verification.txt').write_text('\n'.join(text)+'\n')
    print('\n'.join(text)); print('Initial companion coefficients:',c[:15])
    print(json.dumps(diagnostics,indent=2))

if __name__=='__main__': main()
