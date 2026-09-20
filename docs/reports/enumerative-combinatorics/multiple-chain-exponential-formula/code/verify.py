#!/usr/bin/env python3
"""Exact, independent checks of the multiple-chain exponential formula.

Python 3.10+ standard library only. Run from any directory:
    python code/verify.py [--output DIRECTORY]
Outputs deterministic JSON/CSV files in ../results (or the given directory).

This file runs TWO SEPARATE SUITES, inherited from the two merged research
packages. They are deliberately not fused: their methods and parameter ranges
are different and neither is a subset of the other.

  Suite 1 (rectangular): coordinate DP, subset-walk DP and the exponential
  recurrence over 1<=d<=5, 0<=c<=6, 0<=n<=8, plus exhaustive array visits,
  rectangular duality, gamma path expansions and exact rational variances.
  The subset-walk DP is the only computational witness of the two-subset
  encoding used by the first proof, and this is the only data with c != d.

  Suite 2 (diagonal, deeper): block-weight slack DP, coordinate enumeration,
  the recurrence, the endpoint-refined factorization, the gamma transform,
  fixed-support finite differences and the mixed-block-size recursion over
  1<=d<=8, 0<=n<=12.  The endpoint and mixed-size checks have no analogue in
  Suite 1, and this is the only data reaching d = 8 and n = 12.

No floating-point operation occurs anywhere in this file.  Polynomial
coefficient arrays are stored in increasing degree order.  Checks are raised
through require(), not through assert, so they remain active under
python -O.  The finite checks corroborate the article's proofs; they are not
a proof of the all-parameter identities.
"""
from __future__ import annotations

import argparse
import csv
import itertools
import json
import platform
from collections import defaultdict
from fractions import Fraction
from functools import lru_cache
from math import comb, factorial
from pathlib import Path
from typing import Iterable

Poly = tuple[int, ...]                 # coefficients in increasing t-degree


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)


# --------------------------------------------------------------------------
# Shared exact polynomial arithmetic
# --------------------------------------------------------------------------

def trim(p: Iterable[int]) -> Poly:
    a = list(p)
    while len(a) > 1 and not a[-1]:
        a.pop()
    return tuple(a) if a else (0,)


def add(a: Poly, b: Poly) -> Poly:
    c = [0] * max(len(a), len(b))
    for i, x in enumerate(a):
        c[i] += x
    for i, x in enumerate(b):
        c[i] += x
    return trim(c)


def mul(a: Poly, b: Poly) -> Poly:
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    c[i+j] += x*y
    return trim(c)


def scale(a: Poly, s: int, shift: int = 0) -> Poly:
    return trim([0]*shift + [s*x for x in a])


def divide(a: Poly, d: int) -> Poly:
    require(d > 0 and all(x % d == 0 for x in a),
            f'Nonintegral division of {a} by {d}')
    return trim(x//d for x in a)


def evaluate(p: Poly, q: int) -> int:
    ans = 0
    for a in reversed(p):
        ans = ans*q + a
    return ans


def series_mul(a: list[Poly], b: list[Poly], n: int) -> list[Poly]:
    out: list[Poly] = [(0,)] * (n+1)
    for i, p in enumerate(a[:n+1]):
        for j, q in enumerate(b[:n+1-i]):
            out[i+j] = add(out[i+j], mul(p, q))
    return out


@lru_cache(None)
def narayana_b(m: int) -> Poly:
    """B_m(t) = sum_j binom(m,j)^2 t^j."""
    return tuple(comb(m, j)**2 for j in range(m+1))


@lru_cache(None)
def block_weight(d: int, total: int) -> Poly:
    """W_{d,s}(t): d nonnegative coordinates with prescribed sum s."""
    if total == 0:
        return (1,)
    return (0,) + tuple(comb(d, r)*comb(total-1, r-1)
                        for r in range(1, min(d, total)+1))


def check_quartic(F: list[Poly], n: int) -> None:
    """Verify the explicit d=2 quartic coefficientwise in t through z^n."""
    powers = [[(1,)] + [(0,)]*n, F[:n+1]]
    for _ in range(2, 5):
        powers.append(series_mul(powers[-1], F, n))
    # (coefficient polynomial in t, power of z, power of F)
    terms = [((0, 0, 0, 0, 1), 4, 4), ((0, 0, 1, 2, 1), 3, 3),
             ((0, 0, -1), 2, 3), ((0, 2, 2, 2), 2, 2), ((0, 2), 1, 2),
             ((1, 2, 1), 1, 1), ((-1,), 0, 1), ((1,), 0, 0)]
    out: list[Poly] = [(0,)] * (n+1)
    for coefficient, shift, power in terms:
        for k in range(shift, n+1):
            out[k] = add(out[k], mul(coefficient, powers[power][k-shift]))
    require(all(p == (0,) for p in out), 'Quartic identity failed')


# --------------------------------------------------------------------------
# Suite 1: the rectangular parameter range
# --------------------------------------------------------------------------

def validate(d: int, c: int, n: int) -> None:
    require(d >= 1 and c >= 0 and n >= 0, 'Require d >= 1, c >= 0, n >= 0.')


def bridge_poly(d: int, c: int, m: int) -> Poly:
    return tuple(comb(d*m, j)*comb(c*m, j)
                 for j in range(min(d*m, c*m)+1))


def exponential_recurrence(d: int, c: int, n: int) -> list[Poly]:
    """n*A_n = sum_{m=1}^n C_m*A_{n-m}, with exact divisions."""
    validate(d, c, n)
    rows: list[Poly] = [(1,)]
    bridges = [(1,)] + [bridge_poly(d, c, m) for m in range(1, n+1)]
    for k in range(1, n+1):
        p: Poly = (0,)
        for m in range(1, k+1):
            p = add(p, mul(bridges[m], rows[k-m]))
        rows.append(divide(p, k))
    return rows


def coordinate_dp(d: int, c: int, n: int) -> list[Poly]:
    """Enumerate original coordinates, without any walk or bridge formula.

    After coordinate j of block r, total <= c*r is safe to enforce because
    coordinates are nonnegative. No smaller, intermediate prefix bound is used.
    """
    validate(d, c, n)
    states: dict[tuple[int, int], int] = {(0, 0): 1}
    rows: list[Poly] = [(1,)]
    for r in range(1, n+1):
        cap = c*r
        for _ in range(d):
            nxt: dict[tuple[int, int], int] = defaultdict(int)
            for (total, support), count in states.items():
                for value in range(cap-total+1):
                    nxt[total+value, support+(value != 0)] += count
            states = nxt
        p = [0] * (min(d*r, c*r)+1)
        for (_, support), count in states.items():
            p[support] += count
        rows.append(trim(p))
    return rows


def subset_walk_dp(d: int, c: int, n: int) -> list[Poly]:
    """Walk symbol (1+u)^c (1+t/u)^d; height checked at block ends only."""
    validate(d, c, n)
    steps = [(ell-j, j, comb(c, ell)*comb(d, j))
             for ell in range(c+1) for j in range(d+1)]
    states: dict[tuple[int, int], int] = {(0, 0): 1}
    rows: list[Poly] = [(1,)]
    for r in range(1, n+1):
        nxt: dict[tuple[int, int], int] = defaultdict(int)
        for (height, support), count in states.items():
            for step, marks, ways in steps:
                if height+step >= 0:
                    nxt[height+step, support+marks] += count*ways
        states = nxt
        rows.append(trim(states.get((0, j), 0)
                         for j in range(min(d*r, c*r)+1)))
    return rows


def exhaustive_arrays(d: int, c: int, n: int) -> tuple[Poly, int]:
    """Visit every feasible array (tiny cases only), without merged states."""
    validate(d, c, n)
    p = [0] * (min(d*n, c*n)+1)
    leaves = 0

    def visit(i: int, total: int, support: int) -> None:
        nonlocal leaves
        if i == d*n:
            p[support] += 1
            leaves += 1
            return
        cap = c*(i//d+1)
        for value in range(cap-total+1):
            visit(i+1, total+value, support+(value != 0))
    visit(0, 0, 0)
    return trim(p), leaves


def gamma_dp(d: int, n: int) -> Poly:
    """Uncolored U,D,H microsteps; negativity allowed inside each d-block."""
    states: dict[tuple[int, int], int] = {(0, 0): 1}
    for i in range(1, d*n+1):
        nxt: dict[tuple[int, int], int] = defaultdict(int)
        for (height, down), count in states.items():
            for step, mark in ((1, 0), (-1, 1), (0, 0)):
                h = height+step
                if i % d == 0 and h < 0:
                    continue
                nxt[h, down+mark] += count
        states = nxt
    return trim(states.get((0, j), 0) for j in range(d*n//2+1))


def gamma_expand(gamma: Poly, degree: int) -> Poly:
    p: Poly = (0,)
    for j, coefficient in enumerate(gamma):
        p = add(p, scale(tuple(comb(degree-2*j, k)
                               for k in range(degree-2*j+1)),
                         coefficient, j))
    return p


def exact_variance(p: Poly) -> Fraction:
    total = sum(p)
    mean = Fraction(sum(j*v for j, v in enumerate(p)), total)
    return Fraction(sum(j*j*v for j, v in enumerate(p)), total) - mean*mean


def variance_formula(d: int, n: int, totals: list[int]) -> Fraction:
    if n == 0:
        return Fraction(0)
    return Fraction(d*sum(comb(2*d*m-2, d*m-1)*totals[n-m]
                          for m in range(1, n+1)), 2*totals[n])


def suite_rectangular(out: Path) -> dict:
    cache: dict[tuple[int, int], list[Poly]] = {}
    triples = 0
    for d in range(1, 6):
        for c in range(0, 7):
            expected = exponential_recurrence(d, c, 8)
            require(coordinate_dp(d, c, 8) == expected,
                    f'Coordinate DP disagrees at d={d}, c={c}')
            require(subset_walk_dp(d, c, 8) == expected,
                    f'Subset-walk DP disagrees at d={d}, c={c}')
            cache[d, c] = expected
            triples += 9
    dualities = 0
    for d in range(1, 6):
        for c in range(1, 6):
            require(cache[d, c] == cache[c, d],
                    f'Rectangular duality failed at d={d}, c={c}')
            dualities += 9
    exhaustive_cases = 0
    leaves = 0
    for d in range(1, 4):
        for c in range(0, 4):
            for n in range(0, 4):
                p, count = exhaustive_arrays(d, c, n)
                require(p == cache[d, c][n],
                        f'Exhaustive enumeration failed at d={d},c={c},n={n}')
                leaves += count
                exhaustive_cases += 1
    gamma_rows = []
    gamma_cases = 0
    variance_cases = 0
    for d in range(1, 7):
        rows = exponential_recurrence(d, d, 8)
        totals = [sum(p) for p in rows]
        for n, p in enumerate(rows):
            gamma = gamma_dp(d, n)
            require(gamma_expand(gamma, d*n) == p,
                    f'Gamma path expansion failed at d={d}, n={n}')
            require(p == p[::-1], f'Palindromicity failed at d={d}, n={n}')
            require(exact_variance(p) == variance_formula(d, n, totals),
                    f'Exact variance identity failed at d={d}, n={n}')
            gamma_rows.append({'d': d, 'n': n, 'coefficients': list(gamma)})
            gamma_cases += 1
            variance_cases += 1
    check_quartic(exponential_recurrence(2, 2, 16), 16)
    # Match four printed d=2 examples after independently recomputing them.
    published = [(1, 4, 1), (1, 12, 27, 12, 1), (1, 24, 134, 236, 134, 24, 1),
                 (1, 40, 410, 1540, 2380, 1540, 410, 40, 1)]
    require(cache[2, 2][1:5] == published,
            'Printed double-chain examples not reproduced')
    rows_json = [{'d': d, 'c': c, 'n': n, 'coefficients': list(p)}
                 for (d, c), rows in sorted(cache.items())
                 for n, p in enumerate(rows)]
    (out/'exact_polynomials.json').write_text(
        json.dumps(rows_json, indent=2)+'\n')
    (out/'gamma_polynomials.json').write_text(
        json.dumps(gamma_rows, indent=2)+'\n')
    with (out/'small_values.csv').open('w', newline='') as f:
        w = csv.writer(f)
        w.writerow(['block_size_d', 'blocks_n', 'lattice_points',
                    'h_coefficients_in_increasing_degree', 'variance'])
        for d in range(1, 6):
            for n, p in enumerate(cache[d, d]):
                w.writerow([d, n, sum(p), ' '.join(map(str, p)),
                            str(exact_variance(p))])
    return {
        'three_method_parameter_triples': triples,
        'three_method_range': '1<=d<=5, 0<=c<=6, 0<=n<=8',
        'independent_methods': ['coordinate dynamic programming',
                                'subset-walk dynamic programming',
                                'exponential-formula recurrence'],
        'exhaustive_array_cases': exhaustive_cases,
        'exhaustive_feasible_arrays_visited': leaves,
        'exhaustive_range': '1<=d<=3, 0<=c<=3, 0<=n<=3',
        'support_preserving_duality_checks': dualities,
        'gamma_expansion_checks': gamma_cases,
        'gamma_range': '1<=d<=6, 0<=n<=8',
        'exact_variance_checks': variance_cases,
        'quartic_checked_through_z_degree': 16,
        'source_d2_examples_matched': 4}


# --------------------------------------------------------------------------
# Suite 2: the deeper diagonal range, endpoints and mixed block sizes
# --------------------------------------------------------------------------

def advance(states: dict[int, Poly], d: int) -> dict[int, Poly]:
    """Append one block using its actual coordinate-sum distribution."""
    out: dict[int, Poly] = {}
    for slack, p in states.items():
        for total in range(slack+d+1):
            h = slack+d-total
            out[h] = add(out.get(h, (0,)), mul(p, block_weight(d, total)))
    return out


def sum_states(states: dict[int, Poly]) -> Poly:
    ans: Poly = (0,)
    for p in states.values():
        ans = add(ans, p)
    return ans


def lattice_dp(parts: tuple[int, ...]) -> Poly:
    states = {0: (1,)}
    for d in parts:
        require(d >= 1, 'Block sizes must be positive')
        states = advance(states, d)
    return sum_states(states)


def coordinate_enumeration(parts: tuple[int, ...]) -> Poly:
    """Enumerate every individual lattice point, without block weights."""
    total_length = sum(parts)
    if total_length == 0:
        return (1,)
    ends = tuple(itertools.accumulate(parts))
    answer = [0]*(total_length+1)

    def visit(i: int, used: int, support: int) -> None:
        if i == total_length:
            answer[support] += 1
            return
        next_boundary = next(b for b in ends if b > i)
        for value in range(next_boundary-used+1):
            visit(i+1, used+value, support+(value > 0))
    visit(0, 0, 0)
    return trim(answer)


def diagonal_recurrence(d: int, n: int, gamma: bool = False) -> list[Poly]:
    """Rows of the diagonal recurrence, in the t-basis or the gamma basis."""
    rows: list[Poly] = [(1,)]
    for k in range(1, n+1):
        p: Poly = (0,)
        for j in range(1, k+1):
            m = d*j
            bridge = (tuple(factorial(m)//(factorial(r)**2*factorial(m-2*r))
                            for r in range(m//2+1))
                      if gamma else narayana_b(m))
            p = add(p, mul(bridge, rows[k-j]))
        rows.append(divide(p, k))
    return rows


def gamma_transform(p: Poly, degree: int) -> Poly:
    """Rewrite a symmetric polynomial in the basis t^r (1+t)^(degree-2r)."""
    residual = list(p) + [0]*(degree+1-len(p))
    out = []
    for r in range(degree//2+1):
        g = residual[r]
        out.append(g)
        for j in range(degree-2*r+1):
            residual[j+r] -= g*comb(degree-2*r, j)
    require(not any(residual), 'Gamma reconstruction failed')
    return trim(out)


def endpoint_factorization(d: int, n: int, q: int) -> list[Poly]:
    """Endpoint polynomials from exp(sum (z^m/m) [S^m]_{>=0}) at integer t."""
    rows: list[Poly] = [(1,)]
    for k in range(1, n+1):
        p: Poly = (0,)
        for j in range(1, k+1):
            width = d*j
            positive_part = tuple(evaluate(block_weight(width, width-h), q)
                                  for h in range(width+1))
            p = add(p, mul(positive_part, rows[k-j]))
        rows.append(divide(p, k))
    return rows


def mixed_recurrence(types: tuple[int, ...],
                     n: int) -> dict[tuple[int, ...], Poly]:
    """The commutative mixed-block-size formula, by its own recursion."""
    zero = (0,)*len(types)
    out: dict[tuple[int, ...], Poly] = {zero: (1,)}
    for k in range(1, n+1):
        for m in itertools.product(range(k+1), repeat=len(types)):
            if sum(m) != k:
                continue
            p: Poly = (0,)
            for ell in itertools.product(*(range(x+1) for x in m)):
                size = sum(ell)
                if not size:
                    continue
                multiplicity = factorial(size)
                for x in ell:
                    multiplicity //= factorial(x)
                degree = sum(x*d for x, d in zip(ell, types))
                remainder = tuple(x-y for x, y in zip(m, ell))
                p = add(p, scale(mul(narayana_b(degree), out[remainder]),
                                 multiplicity))
            out[m] = divide(p, k)
    return out


def suite_diagonal(out: Path) -> dict:
    coefficients: dict[str, dict] = {}
    totals: list[tuple[int, int, int]] = []
    gamma_cases = diagonal_cases = brute_cases = endpoint_cases = 0
    for d in range(1, 9):
        rows = diagonal_recurrence(d, 12)
        gamma_rows = diagonal_recurrence(d, 12, gamma=True)
        states = {0: (1,)}
        for n in range(13):
            if n:
                states = advance(states, d)
            require(sum_states(states) == rows[n],
                    f'Block-weight lattice DP failed at d={d}, n={n}')
            diagonal_cases += 1
            require(rows[n] == rows[n][::-1], 'Palindromicity failed')
            require(all(x > 0 for x in rows[n]),
                    'Coefficient positivity failed')
            gamma = gamma_transform(rows[n], n*d)
            require(gamma == gamma_rows[n] and all(x > 0 for x in gamma),
                    f'Gamma test failed at d={d}, n={n}')
            gamma_cases += 1
            coefficients[f'{d},{n}'] = {'coefficients': list(rows[n]),
                                        'gamma': list(gamma)}
            totals.append((d, n, sum(rows[n])))
            if n*d <= 8:
                require(coordinate_enumeration((d,)*n) == rows[n],
                        f'Coordinate enumeration failed at d={d}, n={n}')
                brute_cases += 1
            if n*d >= 1:
                require(rows[n][1] == d*d*comb(n+1, 2),
                        'First support coefficient formula failed')
            second = rows[n][2] if len(rows[n]) > 2 else 0
            numerator = (d*d*(d-1)**2*comb(n+3, 4)
                         + 2*(3*d**4-d*d)*comb(n+2, 4)
                         + d*d*(d+1)**2*comb(n+1, 4))
            require(numerator % 4 == 0 and second == numerator//4,
                    'Second support coefficient formula failed')
        for r in range(1, 6):
            seq = [(p[r] if len(p) > r else 0) for p in rows]
            for _ in range(2*r):
                seq = [b-a for a, b in zip(seq, seq[1:])]
            target = factorial(2*r)*d**(2*r)//(factorial(r)*factorial(r+1))
            require(all(x == target for x in seq),
                    'Fixed-support finite-difference check failed')
    for d in range(1, 5):
        for q in (0, 1, 2, 7):
            refined = endpoint_factorization(d, 6, q)
            states = {0: (1,)}
            for n in range(7):
                if n:
                    states = advance(states, d)
                actual = trim(evaluate(states.get(h, (0,)), q)
                              for h in range(n*d+1))
                require(actual == refined[n],
                        f'Endpoint factorization failed d={d}, t={q}, n={n}')
                endpoint_cases += 1
    check_quartic(diagonal_recurrence(2, 16), 16)
    types = (1, 2, 3)
    mixed = mixed_recurrence(types, 4)
    observed: dict[tuple[int, ...], Poly] = defaultdict(lambda: (0,))
    ordered = 0
    for n in range(5):
        for word in itertools.product(types, repeat=n):
            key = tuple(word.count(d) for d in types)
            observed[key] = add(observed[key], lattice_dp(word))
            ordered += 1
    require(dict(observed) == mixed, 'Mixed-size generating identity failed')
    counterexample = {','.join(map(str, w)): list(lattice_dp(w))
                      for w in ((1, 1, 2), (1, 2, 1), (2, 1, 1))}
    require(counterexample['1,1,2'] != counterexample['1,2,1'],
            'Order-dependence counterexample did not reproduce')
    (out/'coefficients.json').write_text(
        json.dumps(coefficients, indent=2)+'\n')
    with (out/'lattice_point_totals.csv').open('w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['d', 'n', 'total'])
        writer.writerows(totals)
    return {
        'block_weight_dp_vs_exponential': {'cases': diagonal_cases,
                                           'd': '1..8', 'n': '0..12'},
        'individual_lattice_point_enumeration': {'cases': brute_cases,
                                                 'dimension_at_most': 8},
        'gamma_transform_vs_exponential': {'cases': gamma_cases},
        'endpoint_refinement': {'cases': endpoint_cases, 'd': '1..4',
                                'n': '0..6', 't': [0, 1, 2, 7]},
        'fixed_support_finite_differences': {'cases': 8*5,
                                             'support': '1..5', 'd': '1..8'},
        'first_two_support_coefficients': 'all 104 diagonal cases',
        'double_chain_quartic': 'zero through z^16, as polynomials in t',
        'mixed_size_identity': {'block_sizes': list(types),
                                'maximum_blocks': 4,
                                'multiplicity_vectors': len(mixed),
                                'ordered_compositions': ordered},
        'mixed_size_counterexample_to_order_invariance': counterexample}


# --------------------------------------------------------------------------

def run(out: Path) -> dict:
    out.mkdir(parents=True, exist_ok=True)
    rectangular = suite_rectangular(out)
    diagonal = suite_diagonal(out)
    report = {
        'status': 'PASS',
        'arithmetic': 'exact Python integers and fractions.Fraction',
        'python_version': platform.python_version(),
        'assertions': 'explicit require(); active under python -O',
        'suite_1_rectangular': rectangular,
        'suite_2_diagonal_deeper': diagonal,
        'limitations': 'Finite checks only; no proof assistant or external '
                       'referee. The two suites use different methods over '
                       'disjoint ranges and neither subsumes the other.'}
    (out/'verification.json').write_text(json.dumps(report, indent=2)+'\n')
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    default = Path(__file__).resolve().parents[1]/'results'
    parser.add_argument('--output', '--out', dest='output', type=Path,
                        default=default)
    args = parser.parse_args()
    print(json.dumps(run(args.output), indent=2))


if __name__ == '__main__':
    main()
