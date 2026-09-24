#!/usr/bin/env python3
"""Exact, standard-library checks for the two-coin entropy counterexamples.

Run from any directory: python code/verify_exact.py
Writes results/exact_checks.json. No floating-point arithmetic is used.
These checks supplement, and do not replace, the all-real-order proof.
"""
from __future__ import annotations
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]

def pmf(parameters: tuple[F, ...]) -> tuple[F, ...]:
    if any(p < 0 or p > 1 for p in parameters):
        raise ValueError('Bernoulli parameters must be in [0, 1].')
    out = [F(1)]
    for p in parameters:
        new = [F(0)] * (len(out) + 1)
        for k, value in enumerate(out):
            new[k] += (1-p)*value
            new[k+1] += p*value
        out = new
    return tuple(out)

def enumerate_pmf(parameters: tuple[F, ...]) -> tuple[F, ...]:
    """Independent implementation: enumerate every outcome, not convolution."""
    out = [F(0)] * (len(parameters)+1)
    for outcome in product((0, 1), repeat=len(parameters)):
        weight = F(1)
        for bit, p in zip(outcome, parameters):
            weight *= p if bit else 1-p
        out[sum(outcome)] += weight
    return tuple(out)

def power_sum(parameters: tuple[F, ...], q: int) -> F:
    if q < 1:
        raise ValueError('The exact power-sum routine needs a positive integer order.')
    return sum((v**q for v in pmf(parameters)), F(0))

def check(condition: bool, message: str) -> None:
    # Deliberately not assert: checks still run under python -O.
    if not condition:
        raise AssertionError(message)

def main() -> None:
    count = 0
    center = (F(1,10), F(1,10))
    endpoint = (F(3,20), F(1,20))
    fc, fe = pmf(center), pmf(endpoint)
    check(fc == (F(81,100), F(18,100), F(1,100)), 'Center PMF')
    check(fe == (F(323,400), F(74,400), F(3,400)), 'Endpoint PMF')
    check(pmf(endpoint[::-1]) == fe, 'Swap symmetry')
    c0, c1 = power_sum(center, 2), power_sum(endpoint, 2)
    check(c0 == F(55088,80000), 'Center collision probability')
    check(c1 == F(54907,80000), 'Endpoint collision probability')
    check(c0-c1 == F(181,80000), 'Exact Jensen gap')
    count += 6
    independent_cases = 0
    for n in range(1, 9):
        for offset in (0, 3, 11):
            pars = tuple(F((7*i+offset) % 21,20) for i in range(n))
            check(pmf(pars) == enumerate_pmf(pars), 'Convolution versus enumeration')
            check(sum(pmf(pars)) == 1, 'Normalization')
            independent_cases += 1
            count += 2
    polynomial_cases = 0
    for i in range(21):
        for j in range(21):
            a,b = F(i,20),F(j,20)
            s,r = a+b,a*b
            formula = 1-2*s+2*s*s+(2-6*s)*r+6*r*r
            check(power_sum((a,b),2) == formula, 'Collision polynomial')
            polynomial_cases += 1
            count += 1
    all_integer_orders = 0
    for q in range(2, 13):
        for denominator in range(20, 201):
            p = F(1,denominator)
            c = (p,p)
            e = (3*p/2,p/2)
            check(power_sum(c,q) > power_sum(e,q), 'Integer-order strict witness')
            all_integer_orders += 1
            count += 1
    # Exact sufficient-condition certificates for noninteger orders.
    # With a=q-1=A/B and p=2^-m, condition (1-2p)^a>2(2p)^a
    # is equivalent to (2^m-2)^A > 2^(A+B).
    orders = [F(1001,1000),F(101,100),F(21,20),F(11,10),F(5,4),
              F(4,3),F(3,2),F(7,4),F(2),F(5,2),F(3),F(7,2),
              F(4),F(5),F(10),F(100)]
    rational_certificates = []
    for q in orders:
        a=q-1; A,B=a.numerator,a.denominator
        m=3+(B+A-1)//A
        lhs=(2**m-2)**A
        rhs=2**(A+B)
        check(lhs > rhs, 'Rational-order sufficient condition')
        rational_certificates.append({'q':str(q),'m':m,'p':str(F(1,2**m)),
            'condition':'(2^m-2)^A > 2^(A+B)', 'A':A,'B':B,
            'left_bit_length':lhs.bit_length(),'right_bit_length':rhs.bit_length(),
            'verified_exactly':True})
        count += 1
    higher_dimensional_cases = []
    for n in range(2,13):
        p=F(1,100*n)
        center_n=(p,)*n
        endpoint_n=(3*p/2,p/2)+(p,)*(n-2)
        gap=power_sum(center_n,2)-power_sum(endpoint_n,2)
        check(gap>0,'Interior higher-dimensional collision witness')
        higher_dimensional_cases.append({'n':n,'p':str(p),'positive_gap':str(gap)})
        count += 1
    # Exact order-two optimizers: vertices or stationary point, with clamping.
    optimization_cases = 0
    for k in range(1,100):
        s=F(k,100)
        rstar=max(F(0),min(s*s/4,(3*s-1)/6))
        Q=lambda r: 1-2*s+2*s*s+(2-6*s)*r+6*r*r
        for j in range(101):
            r=s*s*F(j,400)
            check(Q(rstar)<=Q(r),'Fixed-mean optimizer')
            optimization_cases += 1
            count += 1
    result={'status':'PASS','exact_checks':count,
        'q2_certificate':{'center_parameters':list(map(str,center)),
          'endpoint_parameters':list(map(str,endpoint)),
          'center_pmf':list(map(str,fc)),'endpoint_pmf':list(map(str,fe)),
          'center_collision':str(c0),'endpoint_collision':str(c1),
          'tsallis_jensen_gap':str(c0-c1),'renyi_jensen_gap':'log(55088/54907)'},
        'independent_enumeration_cases':independent_cases,
        'collision_polynomial_cases':polynomial_cases,
        'integer_order_jensen_cases':all_integer_orders,
        'rational_order_certificates':rational_certificates,
        'higher_dimensional_cases':higher_dimensional_cases,
        'optimizer_comparisons':optimization_cases,
        'scope':'Finite exact checks; general theorems are proved in article.tex.'}
    out=ROOT/'results'/'exact_checks.json';out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(f'PASS: {count} exact checks; written {out}')
    print('Order-two Jensen gap: 181/80000 (Tsallis); log(55088/54907) (Renyi).')

if __name__=='__main__':
    main()
