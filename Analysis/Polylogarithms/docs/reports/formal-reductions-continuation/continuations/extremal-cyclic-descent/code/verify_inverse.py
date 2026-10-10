#!/usr/bin/env python3
"""Substitute the generalized inverse into its defining equation exactly.

Exponents are encoded by positive rational bases q, meaning x**log_2(q).
This retains all multiplicative collisions, such as (3/2)*2 == 3.
The finite check is separate from the all-order analytic theorem.
"""
from fractions import Fraction as Q
from itertools import product
from math import factorial
from pathlib import Path
import json
import sympy as s

CUTOFF = Q(4)  # Retain exponents strictly below 2.
L3, L5, L7 = s.symbols('log2_3 log2_5 log2_7')
PRIME_LOGS = {2:s.Integer(1), 3:L3, 5:L5, 7:L7}


def exponent(q):
    q = Q(q)
    result = s.Integer(0)
    for p, e in s.factorint(q.numerator).items():
        result += e * PRIME_LOGS[p]
    for p, e in s.factorint(q.denominator).items():
        result -= e * PRIME_LOGS[p]
    return result


def add(a, b):
    out = dict(a)
    for q, c in b.items():
        out[q] = s.expand(out.get(q, 0) + c)
    return {q:c for q,c in out.items() if c != 0}


def scale(a, c):
    return {q:s.expand(v*c) for q,v in a.items() if v*c != 0}


def mul(a, b):
    out = {}
    for q, c in a.items():
        for r, d in b.items():
            if q*r < CUTOFF:
                out[q*r] = s.expand(out.get(q*r, 0) + c*d)
    return {q:c for q,c in out.items() if c != 0}


def formal_exp(a):
    assert Q(1) not in a
    out, term = {Q(1):s.Integer(1)}, {Q(1):s.Integer(1)}
    j = 0
    while term:
        j += 1
        term = scale(mul(term, a), s.Rational(1,j))
        out = add(out, term)
    return out


def main():
    indices = list(range(3,8))
    eps = {n:1 if n%4 in (1,2) else -1 for n in indices}
    U = {}
    multiindices = 0
    for k in product(range(4), repeat=len(indices)):
        K = sum(k)
        if K == 0:
            continue
        base = Q(1)
        sign = (-1)**(K+1)
        denominator = 1
        for n,j in zip(indices,k):
            base *= Q(n,2)**j
            sign *= eps[n]**j
            denominator *= factorial(j)
        if base >= CUTOFF:
            continue
        lam = exponent(base)
        coefficient = s.Rational(sign,denominator)*s.rf(lam+1,K-1)
        U[base] = s.expand(U.get(base,0) + coefficient)
        multiindices += 1
    # t=exp(-U); t + sum eps_n*x^lambda_n*t^(1+lambda_n) must equal 1.
    residual = formal_exp(scale(U,-1))
    for n in indices:
        term = mul({Q(n,2):s.Integer(eps[n])},
                   formal_exp(scale(U,-1-exponent(Q(n,2)))))
        residual = add(residual,term)
    residual = add(residual,{Q(1):s.Integer(-1)})
    assert not residual, residual
    rows=[{'base':str(q),'exponent':str(exponent(q)),
           'coefficient_for_log2_times_correction':str(s.factor(c))}
          for q,c in sorted(U.items())]
    result={'arithmetic':'exact rational exponent bases and symbolic coefficients',
            'cutoff_exponent':2,'retained_multiindices':multiindices,
            'distinct_nonzero_terms':len(rows),'coefficients':rows,
            'defining_equation_residual':{},'passed':True}
    out=Path(__file__).resolve().parents[1]/'results'/'inverse_exact_check.json'
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
