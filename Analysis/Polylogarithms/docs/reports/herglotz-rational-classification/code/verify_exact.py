#!/usr/bin/env python3
"""Independent exact finite regressions for the theorems in article.tex.

All classifications and group-ring checks use integer arithmetic. The
symbolic analytic cancellations use SymPy rational expressions. None of
these finite tests replaces the all-parameter proofs in the article.
"""
from __future__ import annotations
import argparse
import csv
import json
import platform
from collections import defaultdict
from math import gcd
from pathlib import Path
import sympy as s
from classify import classify, recurrence_pairs, count_pairs

ROOT = Path(__file__).resolve().parents[1]


def clean(d):
    return {k: v for k, v in d.items() if v}


def add(*terms):
    out = defaultdict(int)
    for scale, vector in terms:
        for key, value in vector.items():
            out[key] += scale * value
    return clean(out)


def rep(a, q):
    a %= q
    return min(a, (-a) % q)


def atom(a, q):
    return {rep(a, q): 1}


def skew(a, q):
    if q <= 2:
        return {}
    return add((1, atom(a, q)), (-1, atom(pow(a, -1, q), q)))


def wedge(u, v):
    d = defaultdict(int)
    for a, x in u.items():
        for b, y in v.items():
            if a < b:
                d[a, b] += x * y
            elif a > b:
                d[b, a] -= x * y
    return clean(d)


def free_beta(a, q):
    d = {}
    for k in range(1, q):
        d = add((1, d), (1, wedge(atom(a*k, q), atom(k, q))))
    return d


def exact_checks(bound):
    stats = {}
    # A. First and second dyadic differences checked directly in Q[G_q].
    count_first = count_second = 0
    for q in range(3, bound + 1, 2):
        inv2 = pow(2, -1, q)
        for a in range(1, q):
            if gcd(a, q) != 1:
                continue
            d1 = add((1, skew(a, q)), (-1, skew(a*inv2 % q, q)))
            assert (not d1) == (q in (3, 5)), (q, a, "first")
            d2 = add((1, skew(2*a % q, q)), (-2, skew(a, q)),
                     (1, skew(a*inv2 % q, q)))
            assert (not d2) == (pow(a, 2, q) in {1, q-1}), (q,a,"second")
            count_first += 1
            count_second += 1
    stats['first_difference_cases'] = count_first
    stats['second_difference_cases'] = count_second
    # B. New dyadic layer: (a-a^-1)(1-h), computed without characters/logs.
    top_cases = 0
    for p in range(4, bound+1, 2):
        Q, h = 2*p, 1+p
        for a in range(1, Q):
            if gcd(a, Q) != 1:
                continue
            ai = pow(a, -1, Q)
            witness = add((1,atom(a,Q)),(-1,atom(a*h,Q)),
                          (-1,atom(ai,Q)),(1,atom(ai*h,Q)))
            assert (not witness) == (a*a % Q in {1,Q-1})
            top_cases += 1
    stats['new_layer_cases'] = top_cases
    # C. Odd conductor doubling, free exterior algebra before unit relations.
    doubling_cases = 0
    for q in range(3, min(bound,101)+1,2):
        inv2 = pow(2,-1,q)
        for a in range(1,q):
            if gcd(a,q) != 1:
                continue
            transformed = free_beta(a,q)
            for k in range(1,q):
                u=add((1,atom(2*a*k,q)),(-1,atom(a*k,q)))
                v=add((1,atom(2*k,q)),(-1,atom(k,q)))
                transformed=add((1,transformed),(1,wedge(u,v)))
            rhs=add((3,free_beta(a,q)),(-1,free_beta(2*a,q)),
                    (-1,free_beta(a*inv2%q,q)))
            assert transformed == rhs
            doubling_cases += 1
    stats['free_exterior_doubling_cases'] = doubling_cases
    # D. Brute arithmetic classification versus independently generated recurrences.
    pairs = recurrence_pairs(bound)
    checked = 0
    brute=set()
    rational_extra=[]
    for q in range(1,bound+1):
        for p in range(1,q):
            if gcd(p,q)!=1:
                continue
            checked += 1
            result=classify(p,q)
            if result['formal_logarithmic']:
                brute.add((p,q))
            elif result['formal_rational_dilogarithmic']:
                rational_extra.append((p,q))
    assert brute == set(pairs)
    assert rational_extra == [(1,3),(1,5),(3,5)]
    assert len(brute)==count_pairs(bound)
    stats['coprime_unordered_pairs_checked']=checked
    stats['logarithmic_pairs_at_bound']=len(brute)
    stats['unordered_rational_dilog_exceptions']=rational_extra
    for B in range(1,bound+1):
        assert count_pairs(B)==sum(b<=B for a,b in brute)
    stats['count_regressions']=bound
    # E. Literal finite-field cocycle counterexample, p=7,n=2.
    defect=add((1,skew(2,7)),(-1,skew(3,7)),(-1,skew(2*pow(3,-1,7)%7,7)))
    assert defect==add((3,skew(2,7))) and defect
    stats['cocycle_defect_p7_n2']={str(k):v for k,v in defect.items()}
    # F. Exact symbolic algebra for the two analytic theorem proofs.
    n=s.symbols('n', positive=True)
    A=(2*n+1)/(2*n+2); B=2*n/(2*n+1)
    assert s.cancel(A*B-n/(n+1))==0
    assert s.cancel(A*(1-B)/(1-A*B)-s.Rational(1,2))==0
    assert s.cancel(B*(1-A)/(1-A*B)-n/(2*n+1))==0
    assert s.cancel((1+n/(n+1)-(n+1)/n)-(n*n-n-1)/(n*(n+1)))==0
    # J(3/5) after the exact Rogers five-term row.
    a,b,c,d,P,L13,L15,Li13,Li15=s.symbols('a b c d P L13 L15 Li13 Li15')
    expr=L13-L15/2+d*d+a*(b-c)/2+a*a/2-7*P/180
    expr=expr.subs({L13:Li13-a*b/2+b*b/2,
                   L15:Li15-a*c+c*c/2})
    desired=Li13-Li15/2+a*a/2+b*b/2-c*c/4+d*d-7*P/180
    assert s.expand(expr-desired)==0
    x,y=s.Rational(1,2),s.Rational(3,4)
    assert (x*y,x*(1-y)/(1-x*y),y*(1-x)/(1-x*y)) == (s.Rational(3,8),s.Rational(1,5),s.Rational(3,5))
    stats['symbolic_analytic_cancellations']='PASS'
    # G. Polynomial coefficients behind the all-fixed-order height expansion.
    z=s.symbols('z')
    polynomial_checks=0
    for sign in (-1,1):
        previous,current=s.Poly(1,z),s.Poly(z,z)
        for r in range(2,33):
            previous,current=current,s.Poly(z*current.as_expr()+sign*previous.as_expr(),z)
            assert current.degree()==r and current.LC()==1
            assert current.nth(r-1)==0
            assert current.nth(r-2)==sign*(r-1)
            polynomial_checks+=1
    stats['recurrence_polynomial_coefficient_checks']=polynomial_checks
    # Frozen representative regressions, including the strengthened modulus 2e.
    assert classify(3,5)['formal_rational_dilogarithmic']
    assert not classify(3,5)['formal_logarithmic']
    assert classify(4,3)['formal_logarithmic']
    assert not classify(8,3)['formal_rational_dilogarithmic']
    assert classify(12,5)['formal_logarithmic']
    assert classify(4,15)['formal_logarithmic']
    assert not classify(7,1)['formal_rational_dilogarithmic']
    assert classify(6,3)['formal_logarithmic'] # reduction to 2/1
    return stats, pairs


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--bound',type=int,default=500)
    args=ap.parse_args()
    if args.bound<5:
        ap.error('--bound must be at least 5')
    stats,pairs=exact_checks(args.bound)
    out={'status':'PASS','bound':args.bound,'python':platform.python_version(),
         'sympy':s.__version__,'checks':stats,
         'scope':'finite exact regressions; all-parameter results have ordinary proofs'}
    (ROOT/'data'/'exact_results.json').write_text(json.dumps(out,indent=2)+'\n')
    with (ROOT/'data'/'logarithmic_pairs.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['smaller','larger','recurrence_witnesses'])
        for (p,q),r in sorted(pairs.items(), key=lambda item:(item[0][1],item[0][0])):
            w.writerow([p,q,json.dumps(r,sort_keys=True)])
    with (ROOT/'data'/'counts.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['height_bound','unordered_log_pairs','ordered_log_rationals','ordered_rational_dilog_rationals'])
        for B in [10,30,100,300,1000,10000,100000,1000000,100000000,10000000000]:
            N=count_pairs(B);w.writerow([B,N,2*N+1,2*N+7])
    print(json.dumps(out,indent=2))

if __name__=='__main__':
    main()
