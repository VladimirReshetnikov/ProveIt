#!/usr/bin/env python3
"""Exact all-integer nonvanishing certificates for offsets 1,...,16.

Standard library only. Reconstructs each diagonal polynomial with rational
arithmetic; factors its prescribed linear factors; checks that the remaining
primitive integer polynomial has no root modulo the supplied prime.
Unlike the finite-row check, each certificate proves a statement for every
integer value of the row index, for its fixed offset.

Run: python3 verify_diagonals.py --output-dir data
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from functools import reduce
import json
import math
from pathlib import Path

PRIMES = [2,3,2,5,3,7,5,11,7,11,13,13,11,23,19,17]
Poly = list[F]  # coefficients in ascending degree

def trim(a: Poly) -> Poly:
    while len(a) > 1 and not a[-1]:
        a.pop()
    return a

def add(a: Poly, b: Poly) -> Poly:
    c = [F(0)]*max(len(a), len(b))
    for i, v in enumerate(a): c[i] += v
    for i, v in enumerate(b): c[i] += v
    return trim(c)

def scale(a: Poly, c: F) -> Poly:
    return trim([c*v for v in a])

def mul(a: Poly, b: Poly) -> Poly:
    c = [F(0)]*(len(a)+len(b)-1)
    for i, v in enumerate(a):
        for j, w in enumerate(b): c[i+j] += v*w
    return trim(c)

def divide_linear(a: Poly, root: int) -> Poly:
    if len(a) < 2:
        raise AssertionError('polynomial degree too small')
    q = [F(0)]*(len(a)-1)
    q[-1] = a[-1]
    for j in range(len(q)-2, -1, -1):
        q[j] = a[j+1]+root*q[j+1]
    if a[0]+root*q[0]:
        raise AssertionError(f'{root} is not a root')
    return trim(q)

def primitive(a: Poly) -> tuple[list[int], F]:
    denominator = math.lcm(*(v.denominator for v in a))
    integer = [int(v*denominator) for v in a]
    divisor = reduce(math.gcd, (abs(v) for v in integer))
    if integer[-1] < 0: divisor = -divisor
    p = [v//divisor for v in integer]
    return p, F(divisor, denominator)

def evaluate_mod(a: list[int], x: int, p: int) -> int:
    value = 0
    for v in reversed(a): value = (value*x+v) % p
    return value

def derive() -> list[dict]:
    D = len(PRIMES)
    # h=H-1, H=(1+z)log(1+z)/z.
    h = [F(0)]+[F((-1)**(j-1), j*(j+1)) for j in range(1, D+1)]
    powers = [[F(int(j==0)) for j in range(D+1)]]
    for ell in range(1, D+1):
        powers.append([sum((powers[-1][d-j]*h[j] for j in range(1,d+1)), F(0))
                       for d in range(D+1)])
    certificates = []
    for d, p in enumerate(PRIMES, 1):
        # S_d(X)=[z^d] H(z)^(X-d).
        S: Poly = [F(0)]
        falling: Poly = [F(1)]
        for ell in range(1, d+1):
            falling = mul(falling, [F(-(d+ell-1)), F(1)])
            S = add(S, scale(falling, powers[ell][d]/math.factorial(ell)))
        roots = [d]
        if d >= 3 and d % 2: roots.append(2*d-1)
        if d == 3: roots.append(8)
        Q = S[:]
        for root in roots: Q = divide_linear(Q, root)
        residual, scalar = primitive(Q)
        reconstructed = scale([F(v) for v in residual], scalar)
        for root in roots: reconstructed = mul(reconstructed, [F(-root), F(1)])
        if reconstructed != S:
            raise AssertionError(f'factorization failed at offset {d}')
        residues = [evaluate_mod(residual, x, p) for x in range(p)]
        if not all(residues):
            raise AssertionError(f'modular certificate failed at offset {d}')
        certificates.append({
            'offset': d,
            'definition': 'S_d(X) = [z^d] (((1+z)*log(1+z))/z)^(X-d)',
            'S_coefficients_ascending': [[v.numerator, v.denominator] for v in S],
            'factored_roots': roots,
            'scalar': [scalar.numerator, scalar.denominator],
            'primitive_residual_coefficients_ascending': residual,
            'certifying_prime': p,
            'residual_values_at_0_through_p_minus_1_mod_p': residues,
            'valid_integer_zeros_for_m_greater_than_d': roots[1:]})
    return certificates

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=Path('data'))
    parser.add_argument('--check-only', action='store_true',
                        help='require the existing JSON certificates to match; do not write')
    args = parser.parse_args()
    certificates = derive()
    target = args.output_dir/'diagonal_certificates.json'
    if args.check_only:
        if json.loads(target.read_text()) != certificates:
            raise AssertionError('saved certificates differ from exact reconstruction')
    else:
        args.output_dir.mkdir(parents=True, exist_ok=True)
        target.write_text(json.dumps(certificates, indent=2)+'\n')
    print('PASS: exact polynomial identities and root-free residue tables for offsets 1..16.')
    print('These certify all integer row indices for those fixed offsets, not all offsets.')

if __name__ == '__main__':
    main()
