#!/usr/bin/env python3
"""Bounded audit of replacing the positive auxiliary root f by F=f^2.

This is an exploration, not a universality or operation-bound claim.  The
modular counterexamples establish their periods by direct exact powering;
probable-prime tests are only a search heuristic and are not proof inputs.
"""
from __future__ import annotations

import argparse
import json
from math import gcd, isqrt, lcm
from pathlib import Path

import sympy as sp


def pell_power(a: int, exponent: int, modulus: int | None = None):
    """Return chi_a(exponent), psi_a(exponent), with optional reduction."""
    D = a*a-1

    def times(z, w):
        x, y = z
        xx, yy = w
        value = (x*xx+D*y*yy, x*yy+y*xx)
        return tuple(v % modulus for v in value) if modulus else value

    result, base = (1, 0), (a, 1)
    while exponent:
        if exponent & 1:
            result = times(result, base)
        exponent >>= 1
        if exponent:
            base = times(base, base)
    return result


def normalized_odd_root_mod(R: int, s: int, modulus: int):
    assert s % 2 == 1
    chi, _ = pell_power(R, s, R*modulus)
    assert chi % R == 0
    return chi//R


def try_counterexample(A: int, p: int, J: int, multiplier: int, small_primes):
    d, c = pell_power(A, p)
    D = A*A-1
    R = multiplier*D*c*c
    F = 1+D*multiplier*multiplier*c**4
    remainder, factors = F, {}
    for prime in small_primes:
        while remainder % prime == 0:
            factors[prime] = factors.get(prime, 0)+1
            remainder //= prime
    if remainder != 1:
        if not sp.isprime(remainder):
            return None
        factors[remainder] = 1
    # A candidate period based on the heuristically found factors.  The
    # direct powering assertion below is the actual certificate of a period.
    period = 1
    for prime, exponent in factors.items():
        if prime == 2:
            bound = 3*2**exponent
        elif D % prime == 0:
            bound = 2*prime**exponent
        else:
            bound = (prime-int(sp.jacobi_symbol(D, prime)))*prime**(exponent-1)
        period = lcm(period, bound)
    if pell_power(A, period, F) != (1, 0):
        return None
    common = gcd(4*period, c)
    if (J-p) % common:
        return None
    reduced_modulus = c//common
    multiple = ((J-p)//common)*pow(4*period//common, -1, reduced_modulus)
    multiple %= reduced_modulus
    if not multiple:
        multiple += reduced_modulus
    s = p+4*multiple*period
    if p % 4 != 1:
        # Only p=1 mod 4 is used: the normalized odd polynomial has sign +.
        return None
    assert R*R == D*(F-1)
    assert R % (c*c) == 0 and R % 2 == 0 and F % 2 == 1
    assert isqrt(F)**2 != F
    assert 1 < J < A and J % 2 == 1 and J != p
    assert p >= 66
    assert c > A*D*D and 0 < 2*p <= c and p >= (J+3)//2
    assert s > p and s % 4 == 1
    assert normalized_odd_root_mod(R, s, F) == c % F
    assert normalized_odd_root_mod(R, s, c) == J
    assert R > A and (2*R-1)**(p-1) > c
    return {
        'status': 'EXACT_AUXILIARY_COUNTEREXAMPLE',
        'scope': 'altered auxiliary lemma only; not a solution of the full packed system',
        'A': A, 'p': p, 'J': J, 'D': D, 'c': c, 'd': d,
        'multiplier': multiplier, 'i': multiplier*D, 'R': R, 'F': F,
        'candidate_factorization': {str(a): b for a, b in factors.items()},
        'period': period, 'period_verified_by_exact_pell_power': True,
        'period_shift_multiplier': multiple, 'auxiliary_index': s,
        'gcd_four_period_c': common,
        'u_mod_F': c % F, 'u_mod_c': J,
        'definitions': {
            'u': 'chi_R(s)/R', 'y': 'psi_R(s)',
            'o': '(u-c)/F', 'j': '(u-J)/c',
        },
        'verified_hypotheses': [
            'R=i*c^2', 'R^2=D*(F-1)', 'F odd and not square',
            'R even', 'A>J>1', 'J odd', 'c>A*D^2', '0<2p<=c',
            'p>=66',
            'p>=(J+3)/2', 'p!=J', 'u=c mod F', 'u=J mod c',
            's=1 mod 4', 'u>c>J by the explicit Pell growth bound',
        ],
    }


def search(A=8, p=69, J=7, limit=1000):
    # p=69 is at least 66 and 1 mod 4, retaining the positive sign.
    small_primes = list(sp.primerange(2, 10000))
    for multiplier in range(2, limit+1, 2):
        result = try_counterexample(A, p, J, multiplier, small_primes)
        if result:
            return result
    raise RuntimeError('No example in the stated bounded search')


def altered_arithmetic_check():
    """Check the cheaper but unproved source system, not universality."""
    import round36_1980_product_bound_certificate as previous
    import round4_1980_operation_count as baseline
    from round13_1980_certificate import verify_primitives

    schedule = []
    for row in previous.SCHEDULE:
        if row[0] == 'L16':
            assert row == ('L16', '*', 'f', 'f')
            continue
        if row[0] == 'f_square_minus_one':
            assert row == ('f_square_minus_one', '-', 'L16', 1)
            row = ('f_square_minus_one', '-', 'f', 1)
        schedule.append(row)
    # In this altered system the input named f means F, with no square
    # constraint.  The linear auxiliary equation u=c+o*f means u=c+o*F.
    env, s = dict(previous.SYM), previous.SYM
    baseline.run_schedule(schedule, env)
    source = list(previous.source_residuals())
    D = (s['a']+4)**2-1
    gap = (2*s['r']+1+s['j']*s['c'])**2-s['y_aux']**2
    source[15] = (s['i']*s['c']**2)**2-D*(s['f']-1)
    source[16] = D*(s['f']-1)*gap-(1-s['y_aux']**2)
    B, A = s['H']+s['b']+4, s['a']+4
    corrections = {
        2: -s['la']*source[3],
        16: source[15]*gap,
        17: source[3]*(s['ka']+s['rho']*(source[3]-2*(A-B))),
    }
    for index, ((left, right), residual) in enumerate(zip(previous.EQUALITIES, source)):
        actual = sp.expand(env[left]-env[right])
        correction = corrections.get(index, 0)
        assert (sp.expand(actual-residual-correction) == 0 or
                correction == 0 and sp.expand(actual+residual) == 0)
    primitives, counts = verify_primitives(schedule, env)
    assert len(primitives) == 90 and counts == {'+': 42, '*': 48}
    return {
        'altered_system_arithmetic_verified': True,
        'operations': 90, 'multiplications': 48, 'additions': 42,
        'source_equations_checked': len(source),
        'universality_status': 'NOT_ESTABLISHED; the proposed replacement auxiliary lemma is false',
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--limit', type=int, default=1000)
    parser.add_argument('--A', type=int, default=8)
    parser.add_argument('--p', type=int, default=69)
    parser.add_argument('--J', type=int, default=7)
    args = parser.parse_args()
    result = search(A=args.A, p=args.p, J=args.J, limit=args.limit)
    result['altered_arithmetic'] = altered_arithmetic_check()
    output = Path(__file__).with_suffix('.json')
    output.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(result['status'], flush=True)
    print('A,p,J,multiplier =', result['A'], result['p'], result['J'], result['multiplier'], flush=True)
    print('F digits =', len(str(result['F'])), '; period digits =', len(str(result['period'])), flush=True)
