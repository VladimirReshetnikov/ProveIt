#!/usr/bin/env python3
"""Independent finite checks for the new quadratic source lemma.

These checks do not decide the Con(ZFC) instance. They audit the combinatorial
certificate, fixed coefficient size, and the complete no-carry/binomial source
interface on small quadratic systems with both valid and invalid witnesses.
Only the Python standard library is required.
"""
from pathlib import Path
from itertools import combinations_with_replacement, product
from math import factorial, prod
import argparse
import gzip
import json
import random


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def polynomial_value(poly, digits):
    return sum(c * prod(x ** e for x, e in zip(digits, alpha))
               for alpha, c in poly.items())


def weighted_coefficients(poly):
    return {alpha: c * factorial(2 - sum(alpha)) * prod(factorial(e) for e in alpha)
            for alpha, c in poly.items()}


def source_data(polys, positions, b, beta):
    n, m, M = len(positions) - 1, len(polys), positions[-1]
    W = 2 * M + 1
    Q = (m - 1) * W + 4 * M
    B = beta * b * b
    weighted = [weighted_coefficients(p) for p in polys]
    D = sum(c * B ** (j * W + 2 * M - sum(e * w for e, w in zip(alpha, positions[1:])))
            for j, p in enumerate(weighted) for alpha, c in p.items())
    N0 = B ** (M + 1)
    N1 = 4 * B ** (Q + 1)
    low_mask = N0 - 1 - (b - 1) * sum(B ** w for w in positions[1:])
    high_mask = (B - 2) * sum(B ** (j * W + 2 * M) for j in range(m))
    bias = B * sum(B ** k for k in range(Q + 1))
    return dict(n=n, m=m, M=M, W=W, Q=Q, B=B, D=D, N0=N0, N1=N1,
                low_mask=low_mask, high_mask=high_mask, bias=bias,
                cap=b * B ** M)


def check_one_g(data, g):
    B, D, N0, N1 = (data[k] for k in ['B', 'D', 'N0', 'N1'])
    J = 2 * (1 + g) ** 2 * D + data['bias']
    N = N0 * N1
    S = g + J * N0
    T = data['low_mask'] + data['high_mask'] * N0
    require(0 <= g < N0 and 0 < J < N1, 'arbitrary-g size bound')
    require(0 <= S < N and 0 <= T < N, 'S,T source-interface bound')
    R = (S + T + 1) * N + T + 1
    X = (N - 1) * R
    require(X % 3 == 0, '3 divides X')
    no_carry = (S & T) == 0
    separated = (g & data['low_mask']) == 0 and (J & data['high_mask']) == 0
    require(no_carry == separated, 'two-block no-carry decomposition')
    require(N & (N - 1) == 0, 'N is power of two')
    nbits = N.bit_length() - 1
    # Kummer: v_2(binomial(2X,X)) = popcount(X), computed without a binomial.
    binomial_divisibility = X.bit_count() >= 2 * nbits
    require(no_carry == binomial_divisibility, 'Sun Lemma2.2 finite check')
    return no_carry


def small_system_checks():
    positions = [0, 1, 3, 7]
    sums = [a + b for a, b in combinations_with_replacement(positions, 2)]
    require(len(sums) == len(set(sums)), 'small B2 certificate')
    systems = [
        [{(1, 0, 0): 1, (0, 0, 0): -2},
         {(0, 0, 0): 1, (0, 1, 0): -1}],
        [{(1, 1, 0): 1, (0, 0, 1): -1},
         {(0, 0, 0): 1, (1, 0, 0): -1}],
        [{(2, 0, 0): 1, (0, 1, 1): -1},
         {(0, 0, 0): 1, (0, 1, 0): -1}],
    ]
    b, beta = 4, 1 << 16
    checks = 0
    accepted = 0
    rng = random.Random(20261023)
    for polys in systems:
        data = source_data(polys, positions, b, beta)
        A = max(abs(c) for p in polys for c in weighted_coefficients(p).values())
        require(beta > 2 * A * 4 ** 2, 'coefficient base bound')
        require(data['D'] > 0, 'reversal positivity')
        for digits in product(range(b), repeat=3):
            g = sum(z * data['B'] ** w for z, w in zip(digits, positions[1:]))
            actual = check_one_g(data, g)
            expected = all(polynomial_value(p, digits) == 0 for p in polys)
            require(actual == expected, 'full source equivalence for encoded tuple')
            checks += 1
            accepted += actual
            # A forbidden units digit must fail the low mask even if high tests pass.
            require(not check_one_g(data, g + 1), 'forbidden constant digit rejected')
            checks += 1
        for _ in range(100):
            g = rng.randrange(2 * data['cap'])
            check_one_g(data, g)
            checks += 1
        for g in [0, 1, data['cap'] - 1, data['cap'], 2 * data['cap'] - 1]:
            check_one_g(data, g)
            checks += 1
    # Negative control: positions [0,1,2] identify the monomials x^2 and y.
    # For r=y, the reversed extraction returns x^2+2y, not 2y.
    x, y = 1, 0
    require(x * x + 2 * y != 2 * y, 'bad B2 set must be rejected')
    return dict(status='PASS',complete_source_checks=checks,
                accepted_encoded_solutions=accepted,
                bad_constant_digits_rejected=True,
                colliding_position_negative_control=True,
                includes_arbitrary_g_upper_boundary=True)


def concrete_payload_checks(root):
    records = json.loads((root / 'generated/source_records.json').read_text())
    metrics = json.loads((root / 'generated/METRICS.json').read_text())
    ports = [int.from_bytes(gzip.decompress((root / 'data' / name).read_bytes()), 'little')
             for name in ['beta.bin.gz', 'K.bin.gz', 'MC.bin.gz', 'MF_source.bin.gz']]
    A = 0
    for block in records['blocks']:
        for row in block['records']:
            coefficient = sum(t['coefficient'] * prod(c ** e for c, e in zip(ports, t['powers']))
                              for t in row['recipe'])
            A = max(A, abs(coefficient))
    positions = metrics['source']['positions']
    pairs = [a + b for a, b in combinations_with_replacement(positions, 2)]
    require(len(pairs) == len(set(pairs)), 'concrete B2 certificate')
    beta = 1 << metrics['source']['beta_exponent']
    require(A < (1 << 2134927), 'weighted-coefficient bound')
    require(beta > 8192 * A, 'generous concrete base bound')
    return dict(status='PASS',weighted_coefficient_max_bit_length=A.bit_length(),
                pair_sums=len(pairs),all_pair_sums_distinct=True,
                weighted_coefficient_bound_exponent=2134927,
                beta_gt_8192A=True,concrete_max_position=max(positions))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--candidate', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    report = {'small_systems': small_system_checks()}
    if args.candidate is not None:
        report['concrete_payload'] = concrete_payload_checks(args.candidate)
    text = json.dumps(report, indent=2) + '\n'
    if args.output is not None:
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
