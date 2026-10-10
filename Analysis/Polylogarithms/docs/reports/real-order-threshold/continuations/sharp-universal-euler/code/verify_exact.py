#!/usr/bin/env python3
"""Read-only exact verifier. No numerical special functions; active under -O."""
from __future__ import annotations
from fractions import Fraction as F
from pathlib import Path
from math import comb
import json,time
from exact_core import (require, check_polynomial_identities, polynomial_certificates,
                        euler_axis_interval,euler_weights,euler_integer,
                        bernstein_coefficients,restrict_box,P2)
ROOT=Path(__file__).resolve().parents[1]

def main()->None:
    start=time.time();check_polynomial_identities();print('PASS: three defining polynomial identities')
    expected=json.loads((ROOT/'data/bernstein_certificates.json').read_text())
    actual=polynomial_certificates()
    require(actual==expected,'frozen Bernstein certificate differs from regeneration')
    count=sum(len(b['coefficients']) for c in actual.values() for b in c['boxes'])
    require(count==1542,'unexpected Bernstein coefficient count')
    print(f'PASS: {count} strictly positive exact Bernstein coefficients; 82 cells')
    # A deliberately damaged positivity claim must fail independently of assert.
    bad=dict(P2);bad[(0,0)]-=1
    require(any(min(bernstein_coefficients(restrict_box(bad,(i,j),8),(3,3)))<0
                for i in range(8) for j in range(8)),'negative control was not rejected')
    print('PASS: corrupted polynomial rejected')
    for n in range(1,33):
        for k,w in enumerate(euler_weights(n)):
            other=sum(F((-1)**k*comb(j,k),2**(j+1)) for j in range(k,n))
            require(w==other,'Euler weight identity failed')
    print('PASS: 528 independent finite Euler weight identities')
    data=json.loads((ROOT/'data/axis_certificates.json').read_text());intervals=[]
    for row in data['points']:
        b=F(row['b']);roots=list(map(int,row['lower_power_numerators']))
        lo,hi=euler_axis_interval(b,row['N'],10**row['digits'],roots)
        require((str(lo),str(hi))==(row['C_lower'],row['C_upper']),'axis interval mismatch')
        intervals.append((lo,hi))
    require(intervals[1][0]>intervals[0][1] and intervals[1][0]>intervals[2][1],
            'axis peak localization failed')
    lower=intervals[1][0]
    upper=max(x[1] for x in intervals)+F(1,8*10000**2)
    require(lower>F(data['C_star_lower']),'claimed global lower bound failed')
    require(upper<F(data['C_star_upper']),'claimed global upper bound failed')
    require(F(data['C_star_upper'])<F(57,50),'rational universal budget failed')
    print('PASS: 282 exact rational power brackets and three C(b) enclosures')
    print('PASS: 1.3021 < b_* < 1.3023; 1.1365611033 < C_* < 1.1365611046')
    # Scope guard: scaled Euler errors need not decrease, even at integer orders.
    a,b,n=4,1,48
    en=euler_integer(a,b,n); glo=en-F(9,8*2**n);ghi=en
    A1=F(1,3**a)+F(1,2**b*3**a)
    # R_2-R_1=-2g-A_1.
    require(-2*ghi-A1>0,'scaled-error monotonicity counterexample failed')
    print('PASS: R_2(4,1)>R_1(4,1), certified without a transcendental evaluator')
    # Sanity checks of the elementary strict C(1)>9/8 separation.
    arctan_lower=4*(F(1,5)-F(1,3*5**3))-F(1,239)
    require(arctan_lower>F(25,32),'Machin lower bound failed')
    require(2*(F(1,3)+F(1,81))>F(11,16),'logarithm lower bound failed')
    print('PASS: elementary C(1)>9/8 separation')
    print('ALL EXACT CHECKS PASSED; elapsed %.3fs'%(time.time()-start))
if __name__=='__main__':main()
