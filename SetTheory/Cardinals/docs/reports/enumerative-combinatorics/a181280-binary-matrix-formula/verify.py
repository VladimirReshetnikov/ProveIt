#!/usr/bin/env python3
"""Exact certificates for A181280 and its universal recurrence.

Python >= 3.10, standard library only. Run `python verify.py --out results`.
No internet, floating point, guessed recurrences, or input sequence data is used.
The all-n inference is proved in article.tex; this program certifies the finite
arithmetic and performs independent brute-force/Fourier cross-checks.
Polynomial coefficient arrays are in ASCENDING powers throughout.
"""
from __future__ import annotations

import argparse
import csv
import json
import platform
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
from math import comb
from pathlib import Path
from time import perf_counter

Matrix = list[list[int]]


def require(condition: bool, message: str) -> None:
    """Checks are not disabled by Python's -O option."""
    if not condition:
        raise AssertionError(message)


def parity_sign(value: int) -> int:
    return 1 - 2 * (value.bit_count() & 1)


def poly_mul(a: list[int], b: list[int]) -> list[int]:
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i + j] += x * y
    return c


def polynomial_from_roots(roots: list[int]) -> list[int]:
    p = [1]
    for r in roots:
        p = poly_mul(p, [-r, 1])
    return p


def poly_eval(p: list[int], x: int) -> int:
    y = 0
    for c in reversed(p):
        y = y * x + c
    return y


def universal_roots(m: int, include_zero: bool = True) -> list[int]:
    if m < 1:
        raise ValueError('m must be positive')
    roots = [0] * m if include_zero else []
    for j in range(1, m + 1):
        mu = min(j, m - j)
        roots.extend([1 << j] * (mu + 1))
        roots.extend([-(1 << j)] * mu)
    return roots


@dataclass(frozen=True)
class Automaton:
    m: int
    pairs: tuple[tuple[int, int], ...]
    gram_masks: tuple[int, ...]
    # Each item is (new order-state, Gram xor mask, column integer).
    transitions: tuple[tuple[tuple[int, int, int], ...], ...]
    accepting: tuple[int, ...]

    @property
    def gram_size(self) -> int:
        return 1 << len(self.pairs)

    @property
    def state_size(self) -> int:
        return 1 << (self.m - 1)


def gram_rows(g: int, m: int, pairs: tuple[tuple[int, int], ...]) -> tuple[int, ...]:
    """Rows read left-to-right as binary integers; top row is row 0."""
    rows = [0] * m
    for h, (i, j) in enumerate(pairs):
        if (g >> h) & 1:
            rows[i] |= 1 << (m - 1 - j)
            rows[j] |= 1 << (m - 1 - i)
    return tuple(rows)


def make_automaton(m: int) -> Automaton:
    if not 1 <= m <= 5:
        raise ValueError('This enumerative implementation supports 1 <= m <= 5')
    pairs = tuple((i, j) for i in range(m) for j in range(i, m))
    gram_masks = tuple(sum((((v >> i) & 1) * ((v >> j) & 1)) << h
                           for h, (i, j) in enumerate(pairs))
                       for v in range(1 << m))
    transitions = []
    for state in range(1 << (m - 1)):
        edges = []
        for v in range(1 << m):
            new_state = state
            for i in range(m - 1):
                if not ((state >> i) & 1):
                    upper = (v >> i) & 1
                    lower = (v >> (i + 1)) & 1
                    if upper > lower:
                        break
                    if upper < lower:
                        new_state |= 1 << i
            else:
                edges.append((new_state, gram_masks[v], v))
        transitions.append(tuple(edges))
    accepting = []
    for g in range(1 << len(pairs)):
        rows = gram_rows(g, m, pairs)
        if all(rows[i] > rows[i + 1] for i in range(m - 1)):
            accepting.append(g)
    return Automaton(m, pairs, gram_masks, tuple(transitions), tuple(accepting))


def count_by_gram(auto: Automaton, limit: int) -> list[list[int]]:
    """F[n][g] counts increasing-row matrices with specified Gram mask g."""
    if limit < 0:
        raise ValueError('limit must be nonnegative')
    tab = [[0] * auto.gram_size for _ in range(auto.state_size)]
    tab[0][0] = 1
    history = []
    for n in range(limit + 1):
        history.append(tab[-1][:])
        require(sum(tab[-1]) == comb(1 << n, auto.m),
                f'Unrestricted sorted-row count failed: m={auto.m}, n={n}')
        if n == limit:
            break
        nxt = [[0] * auto.gram_size for _ in range(auto.state_size)]
        for state, edges in enumerate(auto.transitions):
            source = tab[state]
            for new_state, delta, _ in edges:
                dest = nxt[new_state]
                for gram, value in enumerate(source):
                    if value:
                        dest[gram ^ delta] += value
        tab = nxt
    return history


def conjectured_formula(n: int) -> Fraction:
    """The six exponential-polynomial terms, evaluated with exact rationals.

    This expression agrees with the counting sequence only for n >= 4.
    Evaluation below 4 is intentional, to check the exceptional prefix.
    """
    if n < 0:
        raise ValueError('n must be nonnegative')
    return (Fraction(16 ** n, 512)
            + Fraction((288 * n - 3473) * 8 ** n, 147456)
            - Fraction(113 * (-8) ** n, 49152)
            + Fraction((6 * n * n - 219 * n + 820) * 4 ** n, 6144)
            - Fraction((13 * n - 164) * (-4) ** n, 6144)
            - Fraction((3 * n + 32) * 2 ** n, 288))


def brute_force(m: int, n: int) -> tuple[int, int]:
    """Independent row-set enumeration; does not use the prefix automaton.

    Returns (number with decreasing Gram rows, number with zero Gram).
    """
    good = zero = 0
    for rows in combinations(range(1 << n), m):
        g_rows = tuple(sum((((r & s).bit_count() & 1) << (m - 1 - j))
                           for j, s in enumerate(rows)) for r in rows)
        good += all(g_rows[i] > g_rows[i + 1] for i in range(m - 1))
        zero += not any(g_rows)
    return good, zero


def weighted_matrix(auto: Automaton, q: int) -> Matrix:
    t = [[0] * auto.state_size for _ in range(auto.state_size)]
    for state, edges in enumerate(auto.transitions):
        for new_state, delta, _ in edges:
            t[state][new_state] += parity_sign(q & delta)
    return t


def mat_mul(a: Matrix, b: Matrix) -> Matrix:
    n = len(a)
    c = [[0] * n for _ in range(n)]
    for i, row in enumerate(a):
        for k, value in enumerate(row):
            if value:
                for j, bj in enumerate(b[k]):
                    if bj:
                        c[i][j] += value * bj
    return c


def check_matrix_annihilator(t: Matrix, roots: list[int]) -> None:
    n = len(t)
    product = [[int(i == j) for j in range(n)] for i in range(n)]
    for root in roots:
        factor = [row[:] for row in t]
        for i in range(n):
            factor[i][i] -= root
        product = mat_mul(product, factor)
    require(not any(map(any, product)), 'A matrix annihilator failed')


def fourier_audit(auto: Automaton, limit: int) -> tuple[list[int], dict]:
    roots = universal_roots(auto.m)
    sums = [0] * (limit + 1)
    weights = Counter()
    spectra = {k: set() for k in range(1, auto.m + 1)}
    for q in range(auto.gram_size):
        t = weighted_matrix(auto, q)
        check_matrix_annihilator(t, roots)
        for state in range(auto.state_size):
            spectra[state.bit_count() + 1].add(t[state][state])
            if q:
                require(abs(t[state][state]) <= (1 << (auto.m - 1)),
                        'Nonzero-character spectral bound failed')
        weight = sum(parity_sign(q & g) for g in auto.accepting)
        weights[weight] += 1
        vector = [1] + [0] * (auto.state_size - 1)
        for n in range(limit + 1):
            sums[n] += weight * vector[-1]
            vector = [sum(vector[i] * t[i][j] for i in range(auto.state_size))
                      for j in range(auto.state_size)]
    require(all(value % auto.gram_size == 0 for value in sums),
            'Fourier inversion did not produce integers')
    result = [value // auto.gram_size for value in sums]
    audit = {
        'characters_checked': auto.gram_size,
        'matrices_checked': auto.gram_size,
        'matrix_size': auto.state_size,
        'annihilator_degree': len(roots),
        'observed_level_spectra': {str(k): sorted(v) for k, v in spectra.items()},
        'fourier_weight_histogram': {str(k): v for k, v in sorted(weights.items())},
    }
    return result, audit


def recurrence_residual(poly: list[int], values: list[int], start: int) -> int:
    return sum(c * values[start + j] for j, c in enumerate(poly))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--limit', type=int, default=100,
                        help='Extra exact DP checks through n (default 100)')
    parser.add_argument('--brute-max', type=int, default=6,
                        help='Brute-force cross-check through n; allowed 0..6')
    parser.add_argument('--out', type=Path, default=Path('results'),
                        help='Directory for generated data and audit log')
    args = parser.parse_args()
    if not 16 <= args.limit <= 10000:
        parser.error('--limit must be between 16 and 10000')
    if not 0 <= args.brute_max <= 6:
        parser.error('--brute-max must be between 0 and 6')
    args.out.mkdir(parents=True, exist_ok=True)
    started = perf_counter()
    lines = []

    def report(text: str) -> None:
        print(text)
        lines.append(text)

    auto = make_automaton(4)
    history = count_by_gram(auto, args.limit)
    counts = [sum(row[g] for g in auto.accepting) for row in history]
    zero_gram = [row[0] for row in history]
    require(counts[:4] == [0, 0, 0, 0], 'Initial terms differ')
    require(len(auto.accepting) == 48, 'Expected 48 accepting Gram matrices')
    first_rows = Counter(gram_rows(g, 4, auto.pairs)[0] for g in auto.accepting)
    require(dict(first_rows) == {8: 9, 12: 14, 14: 18, 15: 7},
            'First-row classification differs')
    report('PASS: 48 accepting symmetric Gram matrices (9 + 14 + 18 + 7).')
    for n in range(4, args.limit + 1):
        require(conjectured_formula(n) == counts[n], f'Formula failed at n={n}')
    report(f'PASS: exact definition-based DP equals formula for n=4..{args.limit}.')
    report(f'PASS: unrestricted count equals binomial(2^n,4) for n=0..{args.limit}.')

    p = polynomial_from_roots(universal_roots(4, include_zero=False))
    q_roots = [16, 8, 8, -8, 4, 4, 4, -4, -4, 2, 2]
    q = polynomial_from_roots(q_roots)
    require(p == poly_mul(q, [2, 1]), 'P != (x+2) Q')
    for start in range(4, args.limit - 11 + 1):
        require(recurrence_residual(q, counts, start) == 0,
                f'Q recurrence failed at {start}')
    for start in range(4, args.limit - 12 + 1):
        require(recurrence_residual(p, counts, start) == 0,
                f'P recurrence failed at {start}')
    report('PASS: exact constant-coefficient recurrence checks.')

    fourier, audit = fourier_audit(auto, 15)
    require(fourier == counts[:16], 'Fourier and direct DP disagree')
    report('PASS: all 1024 weighted 8x8 matrices satisfy U(T)=0 (degree 16).')
    report('PASS: Fourier inversion and direct Gram-state DP agree for n=0..15.')
    report('PASS: all nonzero-character spectral radii are at most 8.')

    brute_results = []
    for n in range(args.brute_max + 1):
        b, z = brute_force(4, n)
        require((b, z) == (counts[n], zero_gram[n]), f'Brute force failed at {n}')
        brute_results.append({'n': n, 'row_sets': comb(1 << n, 4),
                              'a_n': b, 'zero_gram': z})
    report(f'PASS: independent row-set brute force for n=0..{args.brute_max}.')

    small_m = []
    for m in (1, 2, 3):
        am = make_automaton(m)
        hm = count_by_gram(am, 20)
        um = polynomial_from_roots(universal_roots(m))
        for g in range(am.gram_size):
            values = [row[g] for row in hm]
            for n in range(len(values) - len(um) + 1):
                require(recurrence_residual(um, values, n) == 0,
                        f'General theorem finite test failed: m={m}, g={g}, n={n}')
        small_m.append({'m': m, 'gram_targets': am.gram_size,
                        'degree_U': len(um) - 1, 'tested_through_n': 20})
    report('PASS: general universal recurrence tested for every Gram target, m=1,2,3.')

    # The generating function for b(n)=a(n+4) is B(z)/D(z).
    denominator = list(reversed(q))
    numerator = [58, -227, -9052, 68976, -16960, -1025408,
                 3055104, -3796992, 2834432, -2490368, 2097152]
    shifted = counts[4:]
    for n in range(len(shifted)):
        coefficient = sum(denominator[j] * shifted[n - j]
                          for j in range(min(n, 11) + 1))
        expected = numerator[n] if n < len(numerator) else 0
        require(coefficient == expected, f'Generating-function check failed at {n}')
    report('PASS: displayed rational generating function and numerator.')

    residual_zero = recurrence_residual(q, zero_gram, 4)
    require(residual_zero == 136857600, 'Zero-Gram residual differs')
    negative_two_coefficient = Fraction(residual_zero, 16 * poly_eval(q, -2))
    require(negative_two_coefficient == Fraction(11, 192), 'Unexpected -2 mode')
    report('PASS: zero-Gram target has (-2)^n coefficient 11/192; universal P is sharp.')

    with (args.out / 'counts.csv').open('w', newline='') as stream:
        writer = csv.writer(stream)
        writer.writerow(['n', 'A181280', 'zero_Gram', 'formula_numerator',
                         'formula_denominator', 'formula_equals_count'])
        for n, a in enumerate(counts):
            value = conjectured_formula(n)
            writer.writerow([n, a, zero_gram[n], value.numerator, value.denominator,
                             int(value == a)])

    certificate = {
        'description': 'Exact arithmetic certificate; see article for the all-n proof.',
        'python_version': platform.python_version(),
        'proof_initial_indices': [4, 15],
        'proof_initial_counts': counts[4:16],
        'proof_initial_formula_values': [str(conjectured_formula(n)) for n in range(4, 16)],
        'exceptional_formula_values_n0_to_n3': [str(conjectured_formula(n)) for n in range(4)],
        'pairs_zero_based': auto.pairs,
        'accepting_Gram_masks': auto.accepting,
        'accepting_first_row_histogram': dict(sorted(first_rows.items())),
        'universal_P_ascending': p,
        'minimal_Q_ascending': q,
        'shifted_GF_numerator_ascending': numerator,
        'GF_denominator_ascending': denominator,
        'Q_recurrence_residuals_n0_to_n3': [recurrence_residual(q, counts, n) for n in range(4)],
        'zero_Gram_counts_n4_to_n15': zero_gram[4:16],
        'Q_of_shift_zero_Gram_at_n4': residual_zero,
        'Q_at_minus_two': poly_eval(q, -2),
        'zero_Gram_minus_two_mode_coefficient': str(negative_two_coefficient),
        'fourier_audit': audit,
        'brute_force': brute_results,
        'general_small_m_checks': small_m,
        'extra_DP_check_through_n': args.limit,
    }
    (args.out / 'certificate.json').write_text(json.dumps(certificate, indent=2) + '\n')
    report('PASS: proof certificate consists of twelve values, n=4..15, not extrapolation.')
    report(f'All checks passed. Python {platform.python_version()}; elapsed {perf_counter()-started:.3f} s.')
    (args.out / 'verification.txt').write_text('\n'.join(lines) + '\n')


if __name__ == '__main__':
    main()
