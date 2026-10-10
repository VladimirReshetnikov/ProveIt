#!/usr/bin/env python3
"""Replay exact rational-function certificates for three golden ladders.

This verifier does not run an integer-relation search and does not trust the
numerical checks as proofs.  It independently factors every 1-f over Q(t),
retains every rational constant prime, and checks the full tensor equations
at weights 2, 3, 4, and 5.  The input rows use the alphabet t, 1-t, 1+t.

Requires Python 3.10+, SymPy, and mpmath. Run from any working directory.
"""
from __future__ import annotations
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations_with_replacement
import json
from pathlib import Path
import sympy as sp
import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT / 'data' / 'golden_rational_certificates.json'
OUTPUT = ROOT / 'data' / 'golden_certificate_verification.json'
t = sp.Symbol('t')
BASE_KEYS = [('polynomial', (1, 0)),
             ('polynomial', (1, -1)),
             ('polynomial', (1, 1))]

def require(condition, message):
    if not condition:
        raise AssertionError(message)

def rational_prime_factors(number):
    number = Q(str(number))
    result = defaultdict(int)
    for prime, exponent in sp.factorint(abs(number.numerator)).items():
        result[('prime', int(prime))] += int(exponent)
    for prime, exponent in sp.factorint(number.denominator).items():
        result[('prime', int(prime))] -= int(exponent)
    return result

def factor_vector(expression):
    """Multiplicative vector modulo signs, with rational contents retained."""
    numerator, denominator = sp.fraction(sp.cancel(expression))
    answer = defaultdict(int)
    for polynomial, polarity in [(numerator, 1), (denominator, -1)]:
        content, factors = sp.factor_list(polynomial, t)
        for key, value in rational_prime_factors(content).items():
            answer[key] += polarity * value
        for factor, multiplicity in factors:
            poly = sp.Poly(factor, t, domain=sp.QQ)
            denominator_scale, integral = poly.clear_denoms(convert=True)
            integer_content, primitive = integral.primitive()
            if primitive.LC() < 0:
                integer_content = -integer_content
                primitive = -primitive
            scalar = sp.Rational(integer_content, denominator_scale)
            for key, value in rational_prime_factors(scalar).items():
                answer[key] += polarity * int(multiplicity) * value
            key = ('polynomial', tuple(int(x) for x in primitive.all_coeffs()))
            answer[key] += polarity * int(multiplicity)
    return {key: value for key, value in answer.items() if value}

def endpoint_value(n, sign):
    return Q(1) if sign > 0 else -1 + Q(1, 2 ** (n-1))

def R(n, x):
    if x == 0:
        return mp.mpf(0)
    if x == 1:
        return mp.zeta(n)
    L = mp.log(abs(x))
    value = mp.fsum((-L)**r / mp.factorial(r) * mp.re(mp.polylog(n-r, x))
                    for r in range(n-1))
    return value + (-1)**(n-1) * (n-1) / mp.factorial(n) * L**(n-1) * (-mp.log(abs(1-x)))

def check_case(case):
    scale = Q(case['scale'])
    target = {int(k): Q(v) for k, v in case['target'].items()}
    data = []
    all_keys = set(BASE_KEYS)
    for coefficient, sign, a, b, c in case['rows']:
        f = sign * t**a * (1-t)**b * (1+t)**c
        u = {key: exponent for key, exponent in zip(BASE_KEYS, (a,b,c)) if exponent}
        require(factor_vector(f) == u, f'Argument factorization failed: {f}')
        v = factor_vector(1-f)
        all_keys.update(v)
        data.append((Q(coefficient), sign, (a,b,c), a+2*b-c, f, u, v))
    keys = sorted(all_keys, key=str)
    indices = {key: i for i, key in enumerate(keys)}
    receipts = {}
    for n in range(2, 6):
        tensor = defaultdict(Q)
        endpoint = Q(0)
        inversion = Q(0)
        image = defaultdict(Q)
        for coefficient, sign, e, k, f, u, v in data:
            weighted = coefficient * k**(5-n)
            # The first n-2 slots are symmetric; all repeated-index rows are checked.
            for prefix in combinations_with_replacement(range(3), n-2):
                scalar = weighted
                for position in prefix:
                    scalar *= e[position]
                for ku, eu in u.items():
                    for kv, ev in v.items():
                        iu, iv = indices[ku], indices[kv]
                        if iu != iv:
                            tensor[prefix + (min(iu,iv), max(iu,iv))] += scalar * eu * ev * (1 if iu < iv else -1)
            if e[0] == 0:
                endpoint += weighted * endpoint_value(n, sign)
            coefficient_at_power = weighted
            if k < 0 and n % 2 == 0:
                inversion += 2 * weighted * endpoint_value(n, sign)
                coefficient_at_power = -weighted
            power = abs(k)
            if sign > 0:
                image[power] += coefficient_at_power
            else:
                image[power] -= coefficient_at_power
                image[2*power] += coefficient_at_power / 2**(n-1)
        nonzero = {str(key): str(value) for key, value in tensor.items() if value}
        require(not nonzero, f'{case["label"]}: weight {n} tensor failed: {nonzero}')
        zero_power = image.pop(0, Q(0))
        image = {k: value * scale for k, value in image.items() if value}
        expected_image = {k: value * k**(5-n) for k, value in target.items() if k}
        require(image == expected_image, f'{case["label"]}: weight {n} image mismatch')
        constant = scale * (endpoint-inversion-zero_power)
        require(constant == Q(case['expected_constants'][str(n)]), 'Wrong endpoint constant')
        receipts[str(n)] = {'exact_tensor_zero': True,
                            'tensor_coordinates_tested': len(tensor),
                            'endpoint_before_scaling': str(endpoint),
                            'inversion_before_scaling': str(inversion),
                            'zero_power_before_scaling': str(zero_power),
                            'golden_R_constant': str(constant)}
    return receipts, keys, data

# Exact elementary factorizations needed for the weight-one companion.
FACTORS = {
    2: (1,0,{ }), 4: (1,1,{5:Q(1,2)}), 6: (4,0,{2:Q(2)}),
    8: (3,1,{3:Q(1),5:Q(1,2)}), 10: (11,0,{11:Q(1)}),
    12: (8,1,{2:Q(3),5:Q(1,2)}),
    20: (55,1,{5:Q(3,2),11:Q(1)}),
    24: (144,1,{2:Q(4),3:Q(2),5:Q(1,2)})}


def check_weight_one(target):
    prime_logs = defaultdict(Q)
    lambda_coefficient = Q(0)
    for power, coefficient in target.items():
        if power == 0:
            continue
        rational, radical_power, valuations = FACTORS[power]
        rhs = rational * (2*t+1)**radical_power * t**(power//2)
        require(sp.rem(1-t**power-rhs, t*t+t-1, t) == 0,
                f'Golden factorization failed at {power}')
        weight = coefficient * power**4
        lambda_coefficient -= weight * Q(power,2)
        for prime, valuation in valuations.items():
            prime_logs[prime] -= weight * valuation
    require(all(value == 0 for value in prime_logs.values()), 'Prime logarithms did not cancel')
    return lambda_coefficient


def numeric_checks(case, receipts, data, a):
    mp.mp.dps = 85
    x = mp.mpf(37)/100
    errors = {}
    for n in range(2,6):
        lhs = mp.fsum(mp.mpf(str(co)) * k**(5-n) * R(n, sign*x**e[0]*(1-x)**e[1]*(1+x)**e[2])
                     for co, sign, e, k, f, u, v in data)
        rhs = mp.mpf(receipts[str(n)]['endpoint_before_scaling']) * mp.zeta(n)
        errors[f'functional_weight_{n}'] = mp.nstr(abs(lhs-rhs), 8)
        require(abs(lhs-rhs) < mp.mpf('1e-70'), 'Numerical R identity mismatch')
    rho=(mp.sqrt(5)-1)/2
    lam=mp.log(rho)
    target = {int(k):Q(v) for k,v in case['target'].items() if int(k)}
    for n in range(1,6):
        lhs=mp.fsum(mp.mpf(str(co))*k**(5-n)*mp.polylog(n,rho**k) for k,co in target.items())
        rhs=mp.mpf(str(a))*lam**n/mp.factorial(n)
        for j in range(2,n+1):
            rhs += mp.mpf(receipts[str(j)]['golden_R_constant'])*mp.zeta(j)*lam**(n-j)/mp.factorial(n-j)
        errors[f'ordinary_weight_{n}']=mp.nstr(abs(lhs-rhs),8)
        require(abs(lhs-rhs)<mp.mpf('1e-65'), 'Numerical ordinary ladder mismatch')
    return errors


def main():
    source=json.loads(INPUT.read_text())
    output={'status':'all exact checks passed',
            'proof_basis':'rational polynomial factorization and generalized Rogers derivative identity',
            'constant_prime_coordinates_retained':True,
            'numerics_role':'independent diagnostic only', 'cases':{}}
    for case in source['certificates']:
        receipts,keys,data=check_case(case)
        target={int(k):Q(v) for k,v in case['target'].items()}
        a=check_weight_one(target)
        numerical=numeric_checks(case,receipts,data,a)
        output['cases'][case['label']]={'rows':len(case['rows']),
            'alphabet_size':len(keys),
            'constant_primes':[key[1] for key in keys if key[0]=='prime'],
            'weight_one_lambda_coefficient':str(a),
            'weights':receipts,'numerical_diagnostics':numerical}
    OUTPUT.write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({'status':output['status'],
          'row_counts':{key:value['rows'] for key,value in output['cases'].items()},
          'output':str(OUTPUT)},indent=2))

if __name__=='__main__':
    main()
