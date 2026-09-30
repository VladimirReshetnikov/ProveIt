#!/usr/bin/env python3
"""Reproduce finite checks for Approximate Phase Rigidity.

Exact tests need only the Python standard library. Numerical diagnostics need
mpmath. They use arbitrary precision but NOT directed rounding; they are not
proof certificates. The article contains the proofs of the infinite statements.
No network access is used.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
import json
from math import gcd
from pathlib import Path
import platform
import random
import sys
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
SEED = 20260930


def v2(n: int) -> int:
    """The two-adic valuation of a positive integer."""
    if n <= 0:
        raise ValueError("v2 requires a positive integer")
    return (n & -n).bit_length() - 1


def resonance_order(a: int, b: int, budget: int, degree: int) -> int:
    """Exact exponent at the reduced positive rational mesh a/b."""
    if min(a, b, budget) < 1 or degree < 0 or gcd(a, b) != 1:
        raise ValueError("Require a,b,budget > 0, degree >= 0 and gcd(a,b)=1")
    z = 0 if budget < b else v2(a) + (budget // b).bit_length()
    return max(0, z - degree)


def exact_checks() -> dict[str, Any]:
    counts: Counter[str] = Counter()
    for a in range(1, 25):
        for b in range(1, 19):
            if gcd(a, b) != 1:
                continue
            for nmax in range(1, 65):
                orders = [0 if n % b else v2(a) + 1 + v2(n // b)
                          for n in range(1, nmax + 1)]
                z = max(orders)
                predicted = (0 if nmax < b else
                             v2(a) + (nmax // b).bit_length())
                assert z == predicted, (a, b, nmax, z, predicted)
                counts['finite_zero_order_maximum'] += 1
                if nmax >= b:
                    s = (nmax // b).bit_length() - 1
                    grid = b * 2**s
                    assert grid <= nmax < 2 * grid
                    assert orders[grid - 1] == z
                    counts['grid_budget_and_maximum'] += 2
                for r in range(9):
                    q = resonance_order(a, b, nmax, r)
                    assert q == max(0, z - r)
                    threshold = b * 2**max(0, r - v2(a))
                    assert (q > 0) == (nmax >= threshold)
                    counts['exponent_formula_and_threshold'] += 2
    for n in range(1, 101):
        total = 2 * sum((Fraction(n + 1 - k, n + 1)
                         for k in range(1, n + 1)), Fraction(0))
        assert total == n
        counts['fejer_weight_sum'] += 1
        # Parseval normalization of the squared Fejer kernel F_n^2.
        squared = 1 + 2 * sum((Fraction(n + 1 - k, n + 1)**2
                               for k in range(1, n + 1)), Fraction(0))
        length = n + 1
        assert squared == Fraction(2 * length**2 + 1, 3 * length)
        counts['squared_fejer_normalization'] += 1
    return {'status': 'PASS', 'assertions': sum(counts.values()),
            'counts': dict(counts),
            'ranges': {'coprime_a': [1, 24], 'coprime_b': [1, 18],
                       'budget': [1, 64], 'degree': [0, 8],
                       'fejer_order': [1, 100]}}


def numerical_checks(dps: int) -> dict[str, Any]:
    try:
        import mpmath as mp
    except ImportError as exc:
        raise RuntimeError("Install mpmath, or run with --exact-only") from exc
    mp.mp.dps = dps
    rng = random.Random(SEED)
    counts: Counter[str] = Counter()
    tol = mp.mpf(10)**(-(dps // 3))
    # The analytic relative tail exponent is at most 10^(-dps+10).
    tail_target = mp.mpf(10)**(-dps + 10)
    max_tail = mp.mpf(0)

    def H(t: Any) -> Any:
        nonlocal max_tail
        t = mp.mpf(t)
        if t == 0:
            return mp.mpf(1)
        if t == mp.floor(t):
            return mp.mpf(0)
        x, product = t, mp.mpf(1)
        # Tail equals H(x); bound its relative departure via the article.
        while abs(x) > mp.mpf('0.5') or 4*mp.pi**2*x*x/9 > tail_target:
            product *= mp.sinpi(x) / (mp.pi*x)
            x /= 2
        max_tail = max(max_tail, 4*mp.pi**2*x*x/9)
        return product

    def G(t: Any) -> Any:
        return mp.exp(-mp.log(t)**2 / (2*mp.log(2))) / mp.sqrt(t)

    points = [mp.sqrt(2)*n for n in range(1, 129)]
    points += [mp.mpf(a)/b for b in [3, 5, 7, 11]
               for a in range(b+1, 8*b) if a % b]
    max_upper_ratio = mp.mpf(0)
    min_lower_ratio = mp.inf
    for t in points:
        value = abs(H(t))
        distance = abs(t - mp.nint(t))
        j = int(mp.ceil(mp.log(2*t, 2)))
        lower = mp.exp(-mp.pi**2/9) * (2*distance/(mp.pi*t))**j
        assert value <= G(t)*(1+tol), ('upper', str(t))
        assert value >= lower*(1-tol), ('lower', str(t))
        counts['H_upper_lower_envelopes'] += 2
        max_upper_ratio = max(max_upper_ratio, value/G(t))
        min_lower_ratio = min(min_lower_ratio, value/lower)
    for n in range(1, 257):
        assert abs(n*mp.sqrt(2) - mp.nint(n*mp.sqrt(2))) >= mp.mpf(1)/(4*n)
        counts['sqrt2_finite_type_bound'] += 1

    max_tail_bound_ratio = mp.mpf(0)
    for j in range(101):
        s = mp.mpf(j)/200
        val = H(s)
        assert mp.exp(-4*mp.pi**2*s*s/9)*(1-tol) <= val <= 1+tol
        counts['small_argument_tail_bound'] += 1
        if s:
            max_tail_bound_ratio = max(max_tail_bound_ratio,
                                      -mp.log(val)/(4*mp.pi**2*s*s/9))

    # Leading zero coefficients, using values on both sides of each zero.
    eps = mp.mpf('1e-12')
    jet_residuals = []
    for integer in [1, 2, 3, 4, 6, 8, 12, 16, 24]:
        p = v2(integer) + 1
        odd = integer // 2**v2(integer)
        expected = -H(mp.mpf(odd)/2) / mp.mpf(integer)**p
        for sign in [-1, 1]:
            delta = sign * eps
            observed = H(integer+delta) / delta**p
            residual = abs(observed/expected-1)
            assert residual < mp.mpf('1e-8'), (integer, sign, str(residual))
            counts['leading_integer_zero_coefficients'] += 1
            jet_residuals.append(residual)

    local_rows = []
    for a, b in [(1, 1), (3, 5), (4, 3), (5, 7)]:
        m0 = mp.mpf(a)/b
        odd = a // 2**v2(a)
        for s in range(4):
            length = b*2**s
            p = v2(a) + s + 1
            expected = -H(mp.mpf(odd)/2) / m0**p
            residual = abs(H(length*(m0+eps))/eps**p / expected - 1)
            assert residual < mp.mpf('1e-8'), (a, b, s, str(residual))
            counts['local_grid_alias_exponents'] += 1
            local_rows.append({'a': a, 'b': b, 'phases': length, 'power': p,
                               'relative_residual': mp.nstr(residual, 12)})

    max_sharp_residual = mp.mpf(0)
    for n in range(1, 21):
        phases = [mp.mpf(j)/(n+1) for j in range(n)]
        for k in range(1, n+1):
            coeff = sum(mp.exp(-2j*mp.pi*k*x) for x in phases)/n
            residual = abs(abs(coeff) - mp.mpf(1)/n)
            assert residual < tol
            max_sharp_residual = max(max_sharp_residual, residual)
            counts['sharp_positive_low_moment_example'] += 1

    minimum_positive_margin = mp.inf
    minimum_complex_margin = mp.inf
    maximum_annihilator_residual = mp.mpf(0)
    for n in range(1, 13):
        for trial in range(8):
            phases = [mp.mpf(rng.randrange(10**9))/10**9 for _ in range(n)]
            nodes = [mp.exp(-2j*mp.pi*x) for x in phases]
            raw = [rng.randrange(1, 10**6) for _ in range(n)]
            weights = [mp.mpf(w)/sum(raw) for w in raw]
            coeffs = [sum(w*z**k for w, z in zip(weights, nodes))
                      for k in range(1, n+1)]
            margin = n*max(map(abs, coeffs))
            assert margin >= 1-tol
            minimum_positive_margin = min(minimum_positive_margin, margin)
            counts['random_positive_moment_barrier'] += 1
            # General complex weights, mass normalized by the final weight.
            cw = [mp.mpc(rng.randrange(-100, 101), rng.randrange(-100, 101))/10
                  for _ in range(n-1)]
            cw.append(1-sum(cw))
            moments = [sum(w*z**k for w, z in zip(cw, nodes))
                       for k in range(n+1)]
            cmargin = (2**n-1)*max(map(abs, moments[1:]))
            assert cmargin >= 1-tol
            minimum_complex_margin = min(minimum_complex_margin, cmargin)
            counts['random_complex_moment_barrier'] += 1
            # Coefficients are ascending in powers of z.
            poly = [mp.mpc(1)]
            for z in nodes:
                new = [mp.mpc(0)]*(len(poly)+1)
                for k, coeff in enumerate(poly):
                    new[k] -= z*coeff
                    new[k+1] += coeff
                poly = new
            residual = abs(sum(c*m for c, m in zip(poly, moments)))
            assert residual < tol
            maximum_annihilator_residual = max(maximum_annihilator_residual, residual)
            counts['complex_annihilator_identity'] += 1

    # Differentiation is a diagnostic on a finite smooth product, with a fixed
    # product length to avoid differentiating an adaptive stopping condition.
    terms = int(mp.ceil((dps + 15)*mp.log(10)/mp.log(4))) + 8
    def fixed_product(t: Any) -> Any:
        value = mp.mpf(1)
        for k in range(terms):
            x = t / 2**k
            value *= mp.sinpi(x)/(mp.pi*x) if x else 1
        return value
    derivative_ratios = []
    for t in [mp.sqrt(2), mp.sqrt(3), mp.mpf('3.125'), mp.mpf('8.25')]:
        for j in [1, 2, 3]:
            value = abs(mp.diff(fixed_product, t, j))/(2*mp.pi)**j
            ratio = value/(2**j*G(t))
            assert ratio <= 1+tol
            derivative_ratios.append(ratio)
            counts['differentiated_envelope'] += 1

    return {'status': 'PASS', 'assertions': sum(counts.values()),
            'counts': dict(counts), 'seed': SEED, 'decimal_precision': dps,
            'mpmath_version': mp.__version__,
            'interpretation': 'Finite high-precision diagnostics, NOT interval certificates',
            'H_test_points': len(points),
            'max_analytic_log_tail_bound': mp.nstr(max_tail, 12),
            'max_H_over_upper_envelope': mp.nstr(max_upper_ratio, 12),
            'min_H_over_lower_envelope': mp.nstr(min_lower_ratio, 12),
            'max_leading_jet_relative_residual': mp.nstr(max(jet_residuals), 12),
            'local_grid_alias_checks': local_rows,
            'max_sharp_moment_absolute_residual': mp.nstr(max_sharp_residual, 12),
            'minimum_positive_moment_margin': mp.nstr(minimum_positive_margin, 12),
            'minimum_complex_moment_margin': mp.nstr(minimum_complex_margin, 12),
            'max_annihilator_absolute_residual': mp.nstr(maximum_annihilator_residual, 12),
            'max_derivative_envelope_ratio': mp.nstr(max(derivative_ratios), 12)}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--exact-only', action='store_true')
    parser.add_argument('--dps', type=int, default=90)
    parser.add_argument('--output', type=Path, default=ROOT/'validation'/'results.json')
    args = parser.parse_args()
    if args.dps < 70:
        parser.error('--dps must be at least 70 for the default near-zero tests')
    results: dict[str, Any] = {'python_version': platform.python_version(),
                               'exact': exact_checks()}
    if not args.exact_only:
        results['numerical'] = numerical_checks(args.dps)
    results['all_passed'] = True
    args.output.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(results, indent=2, sort_keys=True)
    args.output.write_text(text+'\n', encoding='utf-8')
    print(text)
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (AssertionError, ValueError, RuntimeError) as error:
        print(f'FAIL: {error}', file=sys.stderr)
        sys.exit(1)
