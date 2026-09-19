#!/usr/bin/env python3
"""Reproduce all exact numerical checks and the CSV/JSON research artifacts."""
from __future__ import annotations
import argparse
from collections import Counter
import csv
import json
from math import comb
from pathlib import Path
import platform
import random
import time
import rueppel as r


def check(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-size', type=int, default=64)
    parser.add_argument('--large-size', type=int, default=128)
    parser.add_argument('--digital-bits', type=int, default=16)
    parser.add_argument('--out', type=Path, default=Path(__file__).resolve().parents[1] / 'data')
    args = parser.parse_args()
    if args.max_size < 4 or args.large_size < args.max_size or not 1 <= args.digital_bits <= 22:
        parser.error('Require 4 <= max-size <= large-size and 1 <= digital-bits <= 22.')
    args.out.mkdir(parents=True, exist_ok=True)
    start = time.perf_counter()
    limit = 2 * args.large_size + 8
    moments = [r.rueppel(j) for j in range(limit)]
    exact_checks = 0
    arrays = {}

    def compare(name, seq, formula, shift=0, extra=True):
        nonlocal exact_checks
        sizes = list(range(args.max_size + 1))
        if extra:
            sizes = sorted(set(sizes + [args.max_size + 1, args.large_size - 1, args.large_size]))
        values = {}
        for n in sizes:
            actual = r.hankel(seq, n, shift)
            expected = formula(n)
            check(actual == expected, f'{name}, n={n}: {actual} != {expected}')
            values[n] = actual
            exact_checks += 1
        arrays[name] = values
        print(f'{name}: checked {len(sizes)} exact determinants', flush=True)

    compare('D', moments, r.D)
    compare('E', moments, r.E, shift=1)
    compare('T', moments, r.T, shift=2)
    compare('B', moments, r.B, shift=-1)
    for t in (-2, 0, 1, 2):
        compare(f'F_t={t}', r.parameter_moments(limit, t), lambda n, t=t: r.parameter_hankel(n, t), extra=t == 1)
    for u, v in [(1, -1), (2, 3)]:
        compare(f'P_u={u}_v={v}', r.periodic_moments(limit, u, v), lambda n, u=u, v=v: r.periodic_hankel(n, u, v), extra=v == -1)
    for u, v in [(1, -1), (1, 1), (2, -1)]:
        compare(f'L_u={u}_v={v}', r.linear_moments(limit, u, v), lambda n, u=u, v=v: r.linear_hankel(n, u, v), extra=False)
    for v in (-1, 1, 2):
        q = r.reciprocal_coefficients(r.linear_moments(limit, 1, v))
        compare(f'Q_v={v}', q, lambda n, v=v: r.reciprocal_hankel(n, v), extra=v == 1)

    C = [r.hankel([1 - x for x in moments], n) for n in range(args.max_size + 2)]
    diff = [moments[j + 1] - moments[j] for j in range(limit - 1)]
    J = [r.hankel(diff, n) for n in range(args.max_size + 1)]
    exact_checks += len(C) + len(J)
    for n in range(args.max_size + 1):
        check(J[n] ** 2 == r.D(n) * C[n] + r.D(n + 1) * C[n + 1], f'signed identity at {n}')
    first_failure = next(n for n in range(1, args.max_size + 1)
                         if abs(C[n + 1]) - abs(C[n]) != J[n] ** 2)
    check(first_failure == 3, 'Expected first counterexample at matrix size 3.')

    general_checks = 0
    rng = random.Random(20260919)
    for _ in range(100):
        a = [rng.randrange(-3, 4) for _ in range(15)]
        for n in range(1, 6):
            d, d_next = r.hankel(a, n), r.hankel(a, n + 1)
            c, c_next = r.hankel([1 - x for x in a], n), r.hankel([1 - x for x in a], n + 1)
            j = r.hankel([a[k + 1] - a[k] for k in range(len(a) - 1)], n)
            check(j * j == r.sign(n) * (d * c_next + d_next * c), 'general square identity')
            general_checks += 1

    for n in range(args.max_size):
        qn = arrays['Q_v=1'][n + 1]
        check(abs(r.D(n) - qn) // 2 == r.one_runs(n) % 2, f'Conjecture 8 at {n}')
        expression = (1 + r.sign(n) * arrays['D'][n + 1] * arrays['E'][n + 1]) // 2
        check(expression == r.one_runs(n + 1) % 2, f'Conjecture 23 at {n}')
        check(abs(arrays['F_t=1'][n + 1]) == r.binary_runs(n + 1), f'Conjecture 13 at {n}')
        check(arrays['P_u=1_v=-1'][n + 1] == (1, -1, -1, 0)[n % 4], f'Conjecture 10 at {n}')

    digital_limit = 1 << args.digital_bits
    for n in range(digital_limit):
        check(r.E(n) == r.E_by_recursion(n), f'E recurrence at {n}')
    random_large_indices = [rng.getrandbits(256) for _ in range(1000)]
    for n in random_large_indices:
        check(r.E(n) == r.E_by_recursion(n), 'large-index E recurrence')
    distribution = Counter(r.gray_statistics(n) for n in range(1, digital_limit))
    for a in range(args.digital_bits):
        for b in (0, 1):
            expected = comb(args.digital_bits - 1, a) - int(a == 0 and b == 0)
            check(distribution[a, b] == expected, 'dyadic coefficient distribution')
    signed_sum_checks = []
    for N in range(1, args.digital_bits + 1):
        # Complex powers here are implemented with exact pairs of integers.
        def real_power(k):
            x, y = 1, 0
            for _ in range(k):
                x, y = x - y, x + y
            return x
        for t in (0, 1, 2):
            actual = sum(r.parameter_hankel(n, t) for n in range(1, 1 << N))
            expected = real_power(N) if N == 1 else real_power(N) - 2 * (N - 1) * t * t * real_power(N - 2)
            check(actual == expected, 'signed dyadic sum')
            absolute = sum(abs(r.parameter_hankel(n, t)) for n in range(1, 1 << N))
            check(absolute == 2 ** (N - 1) * (1 + (N - 1) * t * t), 'absolute dyadic sum')
            signed_sum_checks.append({'N': N, 't': t, 'signed_sum': actual, 'absolute_sum': absolute})

    with (args.out / 'exact_determinants.csv').open('w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['size', 'D', 'E', 'T', 'B', 'F_t0', 'F_t1', 'F_t2', 'Q_v1', 'P_u1_v_minus1', 'complement', 'difference'])
        for n in range(args.max_size + 1):
            writer.writerow([n, arrays['D'][n], arrays['E'][n], arrays['T'][n], arrays['B'][n],
                             arrays['F_t=0'][n], arrays['F_t=1'][n], arrays['F_t=2'][n],
                             arrays['Q_v=1'][n], arrays['P_u=1_v=-1'][n], C[n], J[n]])
    with (args.out / 'polynomial_coefficients.csv').open('w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['size', 'binary', 'gray', 'runs', 'one_runs', 'a', 'b', 'constant', 't_squared_coefficient'])
        for n in range(1, 1025):
            a, b = r.gray_statistics(n)
            c0, c2 = r.parameter_coefficients(n)
            writer.writerow([n, bin(n)[2:], bin(n ^ (n >> 1))[2:], r.binary_runs(n), r.one_runs(n), a, b, c0, c2])
    with (args.out / 'dyadic_distribution.csv').open('w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['N', 'a', 'b', 'multiplicity'])
        for (a, b), count in sorted(distribution.items()):
            writer.writerow([args.digital_bits, a, b, count])
    with (args.out / 'dyadic_sums.json').open('w') as f:
        json.dump(signed_sum_checks, f, indent=2)
        f.write('\n')
    huge = 10 ** 100
    report = {
        'status': 'PASS', 'python': platform.python_version(),
        'max_consecutive_matrix_size': args.max_size, 'selected_larger_size': args.large_size,
        'exact_rueppel_determinants_computed': exact_checks,
        'general_moment_square_identity_checks': general_checks,
        'digital_indices_checked': digital_limit,
        'random_256_bit_indices_checked': len(random_large_indices),
        'dyadic_distribution_N': args.digital_bits,
        'source_conjectures_proved_in_manuscript': [8, 10, 13, 23],
        'source_conjecture_22_counterexample': {
            'source_index': first_failure - 1, 'matrix_size': first_failure,
            'C_size_3': C[3], 'C_size_4': C[4], 'difference_det_size_3': J[3],
            'squared_left_side': J[3] ** 2, 'printed_right_side_radicand': abs(C[4]) - abs(C[3])},
        'large_example': {'index': str(huge), 'runs': r.binary_runs(huge),
                          'one_runs': r.one_runs(huge),
                          'polynomial_coefficients': r.parameter_coefficients(huge)},
        'elapsed_seconds': round(time.perf_counter() - start, 3),
        'scope_note': 'Finite checks audit the implementation; the manuscript supplies all-index proofs. No proof assistant was used.'
    }
    (args.out / 'verification_summary.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
