#!/usr/bin/env python3
"""Independent exact-rational spot audit, not a formal proof checker.

Reference functions use Fraction polynomials with substantially smaller tails,
not the production dyadic recurrences. Final comparisons are exact integers
or fractions. Runtime is intentionally for audit samples, not production.
"""
from fractions import Fraction as F
from pathlib import Path
import importlib.util
import json
import math
import sys
import csv

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('robin_certificates', ROOT/'code'/'robin_certificates.py')
mod = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = mod
spec.loader.exec_module(mod)

K = 80
R = 1 << 112


def exact_log(q):
    q = F(q)
    assert q > 0
    if q < 1:
        lo, hi = exact_log(1/q)
        return -hi, -lo
    e = 0
    while q >= 2:
        q /= 2
        e += 1
    def atom(x):
        z = (x-1)/(x+1)
        value = sum((2*z**(2*j+1)/F(2*j+1) for j in range(K)), F(0))
        tail = 2*z**(2*K+1)/((2*K+1)*(1-z*z))
        return value, value+tail
    a,b = atom(q)
    c,d = atom(F(2))
    return a+e*c, b+e*d


def round_ref(pair):
    lo,hi = pair
    return F((lo.numerator*R)//lo.denominator,R), F(-((-hi.numerator*R)//hi.denominator),R)


def exact_exp01(q):
    q=F(q)
    assert 0 <= q <= 1
    value=sum((q**j/F(math.factorial(j)) for j in range(61)),F(0))
    return value,value+F(2,math.factorial(61))


def exact_mul(a,b):
    products=[x*y for x in a for y in b]
    return min(products),max(products)


def inside(iv,ref,S):
    return F(iv.lo,S) <= ref[0] <= ref[1] <= F(iv.hi,S)


def factor_sigma(n):
    result=1
    p=2
    while p*p<=n:
        geometric=1
        power=1
        while n%p==0:
            n//=p
            power*=p
            geometric+=power
        result*=geometric
        p+=1
    if n>1:
        result*=1+n
    return result


def main():
    prod=mod.ExactIntervals()
    qs=[F(1),F(2),F(1,2),F(1,3),F(1,1000),F(999,1000),F(1001,1000),F(3,2),F(7,3),F(4096),F(1,4096),F(5041),F(10**50+1)]
    qs += [F(j,j+7) for j in range(1,65)]
    qs += [F(j+7,j) for j in range(1,65)]
    for q in qs:
        assert inside(prod.log_ratio(q.numerator,q.denominator),exact_log(q),prod.S),str(q)
    gamma_m=8192
    H=sum((F(1,j) for j in range(1,gamma_m+1)),F(0))
    loglo,loghi=exact_log(F(gamma_m))
    gamma=(H-loghi-F(1,2*gamma_m),H-loglo-F(1,2*gamma_m)+F(1,12*gamma_m**2))
    assert inside(prod.gamma,gamma,prod.S)
    gl,gh=round_ref(gamma)
    eg=(exact_exp01(gl)[0],exact_exp01(gh)[1])
    assert inside(prod.exp_gamma,eg,prod.S)
    samples=[(0,0),(0,prod.S),(prod.S,prod.S),(1,1),(prod.S-1,prod.S),(prod.S//3,2*prod.S//3),(1,prod.S//2)]
    for a,b in samples:
        ref=(exact_exp01(F(a,prod.S))[0],exact_exp01(F(b,prod.S))[1])
        assert inside(prod.exp01(mod.Interval(a,b)),ref,prod.S),(a,b)
    signed=[(-3*prod.S,-2*prod.S),(-prod.S,prod.S),(-1,0),(0,0),(0,1),(prod.S//3,2*prod.S//3),(2*prod.S,3*prod.S)]
    for a in signed:
        for b in signed:
            ref=exact_mul(tuple(F(x,prod.S) for x in a),tuple(F(x,prod.S) for x in b))
            assert inside(prod.mul(mod.Interval(*a),mod.Interval(*b)),ref,prod.S),(a,b)
    ns=[2,3,4,5,6,7,10,12,60,120,720,840,2520,5040,5041,10080,55440,100000,10**30+1]
    for n in ns:
        l,u=round_ref(exact_log(F(n)))
        ll=(exact_log(l)[0],exact_log(u)[1])
        ref=exact_mul(eg,ll)
        assert inside(prod.robin_bound(n),ref,prod.S),n
    path=ROOT/'certificates'/'finite_robin_certificates.csv'
    rows=0
    bad=[]
    with path.open(newline='') as stream:
        for row in csv.DictReader(stream):
            rows+=1
            n,s,lo,hi,bits=[int(row[k]) for k in ['n','sigma','bound_lo_numerator','bound_hi_numerator','scale_power_of_two']]
            assert n==rows+1
            assert s==factor_sigma(n),n
            S=1<<bits
            sign='holds' if n*lo>s*S else 'fails' if n*hi<s*S else 'undetermined'
            assert sign==row['sign'] and sign!='undetermined',n
            if sign=='fails': bad.append(n)
    summary=json.loads((path.parent/'summary.json').read_text())
    assert rows==summary['integers_checked']==summary['limit_inclusive']-1
    assert bad==mod.EXPECTED_EXCEPTIONS
    result={'all_passed':True,'logarithm_reference_cases':len(qs),'reference_log_terms':K,'reference_gamma_m':gamma_m,'exp_reference_cases':len(samples),'signed_product_cases':len(signed)**2,'robin_bound_reference_cases':len(ns),'sigma_factorization_and_sign_rows':rows,'exceptions':bad,'checks_use_only':'integer and fractions.Fraction arithmetic','scope':'Independent finite arithmetic audit, not a universal theorem or Lean/iPRA proof'}
    out=ROOT/'verification'/'independent_arithmetic_audit.json'
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
