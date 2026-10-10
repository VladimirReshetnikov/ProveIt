#!/usr/bin/env python3
"""Rational certificates for the Lerch zero-splitting sign table.

Only Python's standard library is used. The all-index theorem is analytic;
this script certifies the displayed finite table by enclosing log(2).
"""
import json
from fractions import Fraction as F
from pathlib import Path


def derivative_polynomial(n, k):
    # Ascending coefficients of R_(n,k), where
    # (d/da)^k(log(a)^n/a)=a^(-k-1)*R_(n,k)(log(a)).
    c=[0]*n+[1]
    for j in range(1,k+1):
        d=[(i+1)*c[i+1] if i+1<len(c) else 0 for i in range(len(c))]
        c=[x-j*y for x,y in zip(d,c)]
    return c


def mul(A,B):
    vals=[a*b for a in A for b in B]
    return min(vals),max(vals)


def evaluate_interval(c,x):
    y=(F(0),F(0))
    for a in reversed(c):
        lo,hi=mul(y,x)
        y=lo+a,hi+a
    return y


def endpoints(x):
    return [{'numerator':str(v.numerator),'denominator':str(v.denominator)} for v in x]


def run():
    T=90; u=F(1,3)
    lower=2*sum((u**(2*j+1)/F(2*j+1) for j in range(T)),F(0))
    error=2*u**(2*T+1)/((2*T+1)*(1-u*u))
    log2=(lower,lower+error)
    rows=[]
    for n in range(2,17):
        for k in range(1,n):
            c=derivative_polynomial(n,k)
            value=tuple(v/F(2**(k+1)) for v in evaluate_interval(c,log2))
            sign=1 if value[0]>0 else -1 if value[1]<0 else 0
            assert sign, (n,k,'increase precision')
            r=n-k
            count=k+1 if r%2 else k+(2 if sign<0 else 0)
            rows.append({'n':n,'k':k,'r':r,'polynomial_ascending':c,
                         'h_at_2_interval':endpoints(value),'sign':sign,
                         'small_positive_rho_zero_count':count})
    out={'meaning':'Exact rational sign certificates; analytic zero-count theorem required.',
         'log2_terms':T,'log2_interval':endpoints(log2),'records':rows}
    dest=Path(__file__).with_name('lerch_splitting_certificates.json')
    dest.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'status':'PASS','rational_sign_certificates':len(rows),
                      'n_range':[2,16],'output':dest.name}))

if __name__=='__main__':run()
