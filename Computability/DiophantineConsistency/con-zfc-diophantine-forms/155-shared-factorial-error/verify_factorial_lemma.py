#!/usr/bin/env python3
"""Exact rational sanity checks; the unbounded proof is in the report."""
from fractions import Fraction
from math import factorial,comb
import json

def need(ok,msg):
    if not ok:raise ValueError(msg)

def main():
    cases=0;canonical=0
    for t in range(16,33):
        n=factorial(t)
        need(Fraction(2*t*(t-1),n)<Fraction(1,32),"Factorial error margin")
        need(Fraction(2**t,3**(t+1)-1)<Fraction(1,32),"Zero-branch digit margin")
        values=set(range(1,41))|{t,t+1,n//2,n-2,n-1,n,n+1,n+2}
        for f in sorted(values):
            b=comb(f*f+t,t);v=(f*f+1)**t
            ratio=Fraction(v,b)
            near=abs(Fraction(f)-ratio)<Fraction(1,2)
            need(near==(f==n),"Nearest factorial sample")
            if f==n:
                need(0<Fraction(f)-ratio<Fraction(1,32),"Canonical budget")
                canonical+=1
            cases+=1
    print(json.dumps({"status":"PASS","exact_rational_samples":cases,
                      "canonical_cases":canonical,
                      "scope":"Finite exact-arithmetic sanity checks, not a replacement for the unbounded proof."}))

if __name__=="__main__":main()
