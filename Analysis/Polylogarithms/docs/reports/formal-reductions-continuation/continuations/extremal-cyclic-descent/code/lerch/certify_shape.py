#!/usr/bin/env python3
"""Exact interval certificates for the index-two derivative-order shape theorem.

All acceptance uses fractions and outward intervals from exact_engine.py.
The engine is copied, with provenance, from the incoming Lerch boundary report.
"""
from fractions import Fraction as Q
from math import factorial
from pathlib import Path
import json
from exact_engine import I, outward, logq, horner, polynomial, bernoulli
from exact_engine import em_remainder, endpoint, pack, fracstr


def log_interval(x):
    return I(logq(x.lo).lo, logq(x.hi).hi)


def fi(n,k,x):
    return outward(factorial(k)*horner(polynomial(n,k),-log_interval(x))/x**(k+1))


def endpoint_interval(n,k,a,N=32,p=8):
    b=a+N
    v=I.point(0)
    for m in range(N):
        v=outward(v+fi(n,k,a+m))
    v=outward(v+fi(n,k-1,b)+fi(n,k,b)/2)
    for r in range(1,p+1):
        v=outward(v+Q(bernoulli(2*r),factorial(2*r))*fi(n,k+2*r-1,b))
    R=em_remainder(n,k,b.lo,p)
    return outward(v+I(-R,R))


def main():
    separator,_=endpoint(2,1,Q(13,10))
    assert separator.sign==-1
    rows=[]
    for k,lo,expected in [(2,'1.29982837988436',1),(3,'1.77628448580819',-1)]:
        left=Q(lo);right=left+Q(1,10**14);a=I(left,right)
        Fleft,Rl=endpoint(2,k,left);Fright,Rr=endpoint(2,k,right)
        assert Fleft.sign==1 and Fright.sign==-1
        Fa=-endpoint_interval(2,k+1,a)
        C=outward(k*endpoint_interval(2,k-1,a)+2*endpoint_interval(1,k-1,a))
        assert Fa.sign==-1 and C.sign==expected
        velocity=outward(-C/Fa)
        assert velocity.sign==expected
        # At the root F=0, so C is exactly F_rho(1,a).
        row={'k':k,'root_interval':{'left':fracstr(left),'right':fracstr(right)},
             'F_left':pack(Fleft),'F_right':pack(Fright),
             'F_a_on_root_interval':pack(Fa),
             'C_on_root_interval':pack(C),'endpoint_root_velocity':pack(velocity),
             'N':32,'p':8}
        rows.append(row)
        print(f'k={k}: endpoint velocity in [{pack(velocity)["lower_decimal"]}, {pack(velocity)["upper_decimal"]}]',flush=True)
    out={'arithmetic':'exact rational outward intervals; no floating point acceptance',
         'engine_source':'incoming proveit_lerch_boundary_research/polylog_lerch_boundary/verification/certify.py',
         'root_completeness':'inherited all-k index-two two-simple-zero theorem; each + to - crossing is the lower zero',
         'uniform_count_separator_F21_at_13_over_10':pack(separator),
         'certificates':rows}
    result_dir=Path(__file__).resolve().parents[2]/'results'/'lerch'
    result_dir.mkdir(parents=True,exist_ok=True)
    (result_dir/'shape_certificates.json').write_text(json.dumps(out,indent=2)+'\n')
    print('PASS: two complete endpoint derivative signs, with exact root isolation.')


if __name__=='__main__':
    main()
