#!/usr/bin/env python3
"""Finite exact regression tests; these supplement, not replace, the proofs."""
from fractions import Fraction as F
from itertools import product
from math import factorial
from pathlib import Path
import json
from certify import I, SCALE, bernoulli, rising_coeff, log_rational, certify_F


def run():
    counts={'interval_operations':0,'elementary_derivative_recurrences':0,
            'bernoulli_values':0,'logarithm_identities':0,'certificate_replays':0}
    def contained(iv,q):
        assert F(iv.lo,SCALE)<=q<=F(iv.hi,SCALE),(iv,q)
    values=[F(-7,3),F(-1),F(-1,7),F(0),F(2,9),F(1),F(11,4)]
    intervals=[(x,y) for x in values for y in values if x<=y]
    for (a,b),(c,d) in product(intervals,repeat=2):
        A=I.bounds(a,b);B=I.bounds(c,d)
        for x,y in product([a,b],[c,d]):
            contained(A+B,x+y);contained(A-B,x-y);contained(A*B,x*y)
            counts['interval_operations']+=3
            if c*d>0:
                contained(A/B,x/y);counts['interval_operations']+=1
    # g_{n,k}(L) is the numerator of F^0_{n,k}(a), L=log(a).
    def g(n,k):
        co=rising_coeff(k,n)
        return [F(factorial(n)*co[n-r]*(-1)**r,factorial(r)) for r in range(n+1)]
    for n in range(13):
        for k in range(1,13):
            p=g(n,k);q=g(n,k+1)
            got=[(k+1)*p[r]-(r+1)*p[r+1] if r<n else (k+1)*p[r] for r in range(n+1)]
            assert got==q;counts['elementary_derivative_recurrences']+=1
    for n,val in {0:F(1),1:F(-1,2),2:F(1,6),4:F(-1,30),6:F(1,42),8:F(-1,30),10:F(5,66),12:F(-691,2730)}.items():
        assert bernoulli(n)==val;counts['bernoulli_values']+=1
    for e in range(-10,11):
        a=log_rational(F(2)**e);b=e*log_rational(F(2))
        assert max(a.lo,b.lo)<=min(a.hi,b.hi)
        counts['logarithm_identities']+=1
    assert log_rational(F(1)).lo<=0<=log_rational(F(1)).hi
    cert=Path(__file__).resolve().parents[1]/'certificates/sign_certificates.json'
    data=json.loads(cert.read_text())
    for rec in data['records']:
        den=int(rec['a']['denominator'])
        A=I.bounds(F(int(rec['a']['lo_numerator']),den),F(int(rec['a']['hi_numerator']),den))
        val,rem=certify_F(rec['n'],rec['k'],A)
        assert val.sign()==rec['expected_sign']
        assert val.json()==rec['value']
        counts['certificate_replays']+=1
    out={'status':'all assertions passed','counts':counts,'total_counted_assertions':sum(counts.values())}
    path=Path(__file__).resolve().parents[1]/'certificates/exact_test_report.json'
    path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

if __name__=='__main__':run()
