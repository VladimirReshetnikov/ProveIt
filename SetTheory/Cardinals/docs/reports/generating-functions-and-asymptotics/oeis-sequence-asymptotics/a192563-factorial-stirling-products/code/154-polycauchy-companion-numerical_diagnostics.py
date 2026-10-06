#!/usr/bin/env python3
"""Optional finite-size diagnostics; not interval bounds or error certificates.

Requires exactly mpmath 1.3.0; never installs packages. The default uses
100 decimal digits. Bernoulli sums, not gamma differentiation, supply
the derivatives. Exact rational contraction coefficients are imported
from the standard-library checker.
"""
from __future__ import annotations

import argparse
import hashlib
import sys

sys.dont_write_bytecode = True
from exact_checks import (bernoulli_recurrence, bounded_int, contraction_partitions,
                          emit_json, moment_count, require, stirling_second_rows)

PINNED_VERSION = '1.3.0'
DIAGONAL_SIZES = (20, 50, 100, 200, 500, 1000)
ASPECT_PAIRS = ((50, 25), (50, 100), (200, 100), (200, 400), (500, 250), (500, 1000))


def checked_mpmath():
    try:
        import mpmath
    except ImportError as error:
        raise RuntimeError('Optional diagnostics require mpmath==1.3.0; no installation was attempted') from error
    if mpmath.__version__ != PINNED_VERSION:
        raise RuntimeError(f'mpmath=={PINNED_VERSION} is required; found {mpmath.__version__}')
    return mpmath


def exact_sample_counts(pairs):
    """Retain only current unsigned Stirling row; compute exact integer counts."""
    requests = {}
    for n, k in pairs:
        requests.setdefault(n, set()).add(k)
    row = [1]
    results = {}
    for n in range(1, max(requests) + 1):
        current = [0] * (n + 1)
        for m, value in enumerate(row):
            current[m] += (n - 1) * value
            current[m + 1] += value
        row = current
        for k in sorted(requests.get(n, ())):
            results[n, k] = moment_count(row, k)
    return results


def finite_saddle(mp, n, k, digits):
    def values(r):
        t = mp.exp(r)
        p = [t / (t + q) for q in range(n)]
        derivative = 1 + mp.fsum(p)
        second = mp.fsum(value * (1 - value) for value in p)
        return r * derivative - k, derivative + r * second

    left, right = mp.mpf(0), mp.mpf(1)
    while values(right)[0] < 0:
        right *= 2
    r = (left + right) / 2
    tolerance = mp.mpf(10) ** (-(digits - 15))
    for _ in range(4 * digits):
        value, derivative = values(r)
        if abs(value) <= tolerance * k:
            return r, value
        if value < 0:
            left = r
        else:
            right = r
        proposal = r - value / derivative
        r = proposal if left < proposal < right else (left + right) / 2
    raise RuntimeError('Safeguarded finite-sum Newton iteration did not meet its requested tolerance')


def evaluate_polynomial(mp, coefficients, p):
    value = mp.mpf(0)
    for coefficient in reversed(coefficients):
        value = value * p + coefficient
    return value


def diagnose_one(mp, n, k, exact, coefficients, bernoulli, second, digits, order):
    r, saddle_residual = finite_saddle(mp, n, k, digits)
    t = mp.exp(r)
    probabilities = [t / (t + q) for q in range(n)]
    derivatives = [mp.mpf(0)]
    max_j = 2 * order + 2
    for j in range(1, max_j + 1):
        derivatives.append(mp.fsum(evaluate_polynomial(mp, bernoulli[j], p)
                                   for p in probabilities) + int(j == 1))
    kappas = [mp.mpf(0)] + [mp.fsum(second[j][v] * r ** v * derivatives[v]
                                          for v in range(1, j + 1))
                                  for j in range(1, max_j + 1)]
    b = kappas[2]
    require(b > 0, 'Finite saddle curvature must be positive')
    log_finite_product = r + mp.fsum(mp.log(t + q) for q in range(n))
    log_gamma_quotient = r + mp.loggamma(n + t) - mp.loggamma(t)
    # log(k!) is evaluated as loggamma(k+1), without forming the factorial;
    # none of the logarithmic derivatives is obtained by gamma differentiation.
    log_leading = mp.loggamma(k + 1) + log_finite_product - k * mp.log(r) - mp.log(2 * mp.pi * b) / 2
    log_exact = mp.log(exact)
    exact_over_leading = mp.exp(log_exact - log_leading)
    h = r / k
    corrections = []
    for polynomial in coefficients:
        terms = []
        for exponents, fraction in polynomial.items():
            term = mp.mpf(fraction.numerator) / fraction.denominator
            j_degree = 0
            for i, multiplicity in enumerate(exponents):
                if multiplicity:
                    term *= kappas[i + 3] ** multiplicity
                    j_degree += (i + 3) * multiplicity
            terms.append(term / b ** (j_degree // 2))
        corrections.append(mp.fsum(terms))

    shown_digits = min(70, digits - 30)
    def show(value):
        return mp.nstr(value, shown_digits, strip_zeros=False)

    models = []
    for truncation_r in range(1, order + 2):
        correction_sum = mp.fsum(corrections[:truncation_r])
        models.append({'R': truncation_r, 'P_R': show(correction_sum),
                       'relative_model_error': show(correction_sum / exact_over_leading - 1),
                       'scaled_residual': show((exact_over_leading - correction_sum) / h ** truncation_r)})
    # Deliberately do not serialize a multi-thousand-digit decimal integer.
    # Hexadecimal conversion is exact and exempt from Python's decimal limit.
    exact_hex = format(exact, 'x')
    return {'n': n, 'k': k, 'aspect_ratio': f'{k}/{n}', 'r': show(r), 'b': show(b), 'h': show(h),
            'saddle_equation_residual': show(saddle_residual),
            'finite_product_minus_gamma_log': show(log_finite_product - log_gamma_quotient),
            'exact_count_bit_length': exact.bit_length(),
            'exact_count_hex_sha256': hashlib.sha256(exact_hex.encode('ascii')).hexdigest(),
            'log_exact_count': show(log_exact), 'exact_over_leading': show(exact_over_leading),
            'corrections_E0_through_order': [show(value) for value in corrections],
            'models': models}


def run_diagnostics(digits=100, order=6):
    require(type(digits) is int and 100 <= digits <= 200, 'digits must be in [100,200]')
    require(type(order) is int and 2 <= order <= 6, 'order must be in [2,6]')
    mp = checked_mpmath()
    pairs = tuple((n, n) for n in DIAGONAL_SIZES) + ASPECT_PAIRS
    exact = exact_sample_counts(pairs)
    coefficients = contraction_partitions(order)
    bernoulli = bernoulli_recurrence(2 * order + 2)
    second = stirling_second_rows(2 * order + 2)
    with mp.workdps(digits):
        samples = [diagnose_one(mp, n, k, exact[n, k], coefficients, bernoulli, second, digits, order)
                   for n, k in pairs]
    return {'schema': 'report154.numerical-diagnostics.v1', 'status': 'completed',
            'python_optimization': sys.flags.optimize, 'mpmath_version': mp.__version__,
            'working_decimal_digits': digits, 'displayed_significant_digits': min(70, digits - 30),
            'contraction_order': order, 'sample_count': len(samples),
            'definition': 'scaled_residual = (A_nk / M_nk - P_R) / (r/k)^R; P_R=sum(E_q,q=0..R-1)',
            'scope': 'Floating-point diagnostics only. No certified interval, error constant, onset, or finite threshold oracle.',
            'methods': ['Exact integer unsigned-Stirling recurrence for sample counts',
                        'Safeguarded Newton saddle from finite Bernoulli probability sums',
                        'Integer Bernoulli cumulant polynomials through order 2*order+2',
                        'Exact rational weighted-partition contraction coefficients',
                        'Finite log product compared with log-gamma quotient, without gamma differentiation'],
            'samples': samples}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--digits', type=bounded_int(100, 200), default=100)
    parser.add_argument('--order', type=bounded_int(2, 6), default=6)
    parser.add_argument('--output', help='Create one fresh JSON file; existing paths are never replaced')
    args = parser.parse_args(argv)
    try:
        emit_json(run_diagnostics(args.digits, args.order), args.output)
    except (OSError, ValueError, RuntimeError) as error:
        parser.exit(1, f'error: {error}\n')


if __name__ == '__main__':
    main()
