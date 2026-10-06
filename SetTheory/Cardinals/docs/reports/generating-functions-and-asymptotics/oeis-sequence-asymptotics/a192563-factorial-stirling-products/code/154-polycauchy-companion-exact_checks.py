#!/usr/bin/env python3
"""Exact, bounded finite checks for Report154; Python standard library only.

The algorithms check finite identities, not analytic remainders or onsets.
No validation uses removable ``assert`` statements. See README.md.
"""
from __future__ import annotations

import argparse
from bisect import bisect_left, bisect_right
from collections import Counter
from fractions import Fraction
import hashlib
import json
from math import comb, factorial
from pathlib import Path
import sys

sys.dont_write_bytecode = True
# A shipped, standard-library-only sibling; no downloaded/imported code.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from release_tools import fresh_file

OFFICIAL_PREFIX = (
    1, 2, 13, 161, 3148, 87784, 3274640, 156359874,
    9252910816, 662065322016, 56172251821992, 5562573507747288,
    634574662217269824, 82482896750780978880, 12101565966159294983808,
    1987899464090970683668944, 363036441677797499946379776,
)
SOURCE_URL = 'https://github.com/oeis/oeisdata/blob/main/seq/A192/A192563.seq'
SOURCE_SHA256 = 'ceb63b09626a09d9cb3e498daeedced3c8fb9a17413424c68bd0aac7c835e576'


class CheckFailure(RuntimeError):
    """A finite identity or input validation failed."""


def require(condition, message):
    if not condition:
        raise CheckFailure(message)


class Checks:
    def __init__(self):
        self.counts = Counter()

    def equal(self, name, left, right):
        require(left == right, f'{name}: {left!r} != {right!r}')
        self.counts[name] += 1

    def true(self, name, condition):
        require(condition, name)
        self.counts[name] += 1


def stirling_first_rows(limit):
    """Unsigned [n,m] using [n+1,m] = n[n,m] + [n,m-1]."""
    rows = [[1]]
    for n in range(limit):
        previous = rows[-1]
        current = [0] * (n + 2)
        for m, value in enumerate(previous):
            current[m] += n * value
            current[m + 1] += value
        rows.append(current)
    return rows


def stirling_second_rows(limit):
    """{n,m} using {n+1,m} = m{n,m} + {n,m-1}."""
    rows = [[1]]
    for n in range(limit):
        previous = rows[-1]
        current = [0] * (n + 2)
        for m in range(1, n + 2):
            current[m] = previous[m - 1]
            if m < len(previous):
                current[m] += m * previous[m]
        rows.append(current)
    return rows


def moment_count(first_row, k):
    return sum(value * (m + 1) ** k for m, value in enumerate(first_row))


def stirling_product_count(first_rows, second_rows, n, k):
    return sum(factorial(j) * first_rows[n + 1][j + 1]
               * second_rows[k + 1][j + 1] for j in range(min(n, k) + 1))


def derivative_product_rows(n_limit, k_limit):
    """D[n][k] = F_n^(k)(0), by the integer Leibniz convolution.

    Start with F_0(z)=exp(z). Multiply successively by exp(z)+n.
    This routine neither constructs nor calls either Stirling table.
    """
    choose = [[comb(k, v) for v in range(k + 1)] for k in range(k_limit + 1)]
    rows = [[1] * (k_limit + 1)]
    for n in range(n_limit):
        previous = rows[-1]
        rows.append([n * previous[k] + sum(choose[k][v] * previous[v]
                     for v in range(k + 1)) for k in range(k_limit + 1)])
    return rows


def double_factorial_odd(j):
    value = 1
    for odd in range(1, j + 1, 2):
        value *= odd
    return value


def weighted_partitions(total, width):
    """Exponent tuples m3,... with sum (j-2)m_j = total."""
    exponents = [0] * width

    def visit(weight, remaining):
        if weight > width:
            if remaining == 0:
                yield tuple(exponents)
            return
        for multiplicity in range(remaining // weight + 1):
            exponents[weight - 1] = multiplicity
            yield from visit(weight + 1, remaining - weight * multiplicity)
        exponents[weight - 1] = 0

    yield from visit(1, total)


def gaussian_factor(exponents):
    degree = sum((index + 3) * multiplicity
                 for index, multiplicity in enumerate(exponents))
    if degree % 2:
        return 0
    return (-1) ** (degree // 2) * double_factorial_odd(degree - 1)


def contraction_partitions(order):
    """Direct weighted-partition formula, retaining exact Fractions."""
    width = 2 * order
    answers = []
    for q in range(order + 1):
        polynomial = {}
        for exponents in weighted_partitions(2 * q, width):
            denominator = 1
            for i, multiplicity in enumerate(exponents):
                denominator *= factorial(multiplicity) * factorial(i + 3) ** multiplicity
            polynomial[exponents] = Fraction(gaussian_factor(exponents), denominator)
        answers.append(polynomial)
    return answers


def exponential_recurrence(order):
    """H_d = sum_w w Q_w H_(d-w)/d, independent of enumeration.

    A monomial key records its x_j powers. Its (iu)^J power is then
    determined by the key. It is contracted only after computing H.
    """
    width = 2 * order
    identity = (0,) * width
    h = [{identity: Fraction(1)}]
    contracted = []
    for degree in range(1, width + 1):
        polynomial = {}
        for weight in range(1, degree + 1):
            multiplier = Fraction(weight, degree * factorial(weight + 2))
            for exponents, coefficient in h[degree - weight].items():
                updated = list(exponents)
                updated[weight - 1] += 1
                key = tuple(updated)
                polynomial[key] = polynomial.get(key, Fraction(0)) + multiplier * coefficient
        h.append(polynomial)
    for polynomial in h:
        terms = {key: value * gaussian_factor(key) for key, value in polynomial.items()
                 if gaussian_factor(key)}
        contracted.append(terms)
    return h, contracted


def monomial(width, powers):
    key = [0] * width
    for index, power in powers.items():
        key[index - 3] = power
    return tuple(key)


def known_first_coefficients(width):
    return [
        {monomial(width, {4: 1}): Fraction(1, 8),
         monomial(width, {3: 2}): Fraction(-5, 24)},
        {monomial(width, {6: 1}): Fraction(-1, 48),
         monomial(width, {3: 1, 5: 1}): Fraction(7, 48),
         monomial(width, {4: 2}): Fraction(35, 384),
         monomial(width, {3: 2, 4: 1}): Fraction(-35, 64),
         monomial(width, {3: 4}): Fraction(385, 1152)},
    ]


def bernoulli_recurrence(max_j):
    """Coefficient lists for B_1=p; B_(j+1)=p(1-p)B'_j."""
    polynomials = [[], [0, 1]]
    for j in range(1, max_j):
        previous = polynomials[-1]
        current = [0] * (len(previous) + 1)
        for v in range(1, len(previous)):
            current[v] += v * previous[v]
            current[v + 1] -= v * previous[v]
        polynomials.append(current)
    return polynomials


def bernoulli_stirling(max_j):
    second = stirling_second_rows(max_j)
    return [[]] + [[0] + [(-1) ** (v - 1) * factorial(v - 1) * second[j][v]
                           for v in range(1, j + 1)] for j in range(1, max_j + 1)]


def polynomial_at(polynomial, p):
    value = 0
    for coefficient in reversed(polynomial):
        value = value * p + coefficient
    return value


def euler_bernoulli_step(polynomial):
    """Apply z(d/dz) with p'=p(1-p) to a polynomial in z,p."""
    result = Counter()
    for (z_power, p_power), coefficient in polynomial.items():
        result[z_power, p_power] += z_power * coefficient
        result[z_power + 1, p_power] += p_power * coefficient
        result[z_power + 1, p_power + 1] -= p_power * coefficient
    return {key: value for key, value in result.items() if value}


def threshold_ge(sequence, x):
    index = bisect_left(sequence, x)
    if index == len(sequence):
        raise ValueError('Threshold lies beyond the supplied finite sequence')
    return index


def threshold_gt(sequence, x):
    index = bisect_right(sequence, x)
    if index == len(sequence):
        raise ValueError('Threshold lies beyond the supplied finite sequence')
    return index


def floor_fraction(value):
    return value.numerator // value.denominator


def ceil_fraction(value):
    return -((-value.numerator) // value.denominator)


def serialize_contractions(coefficients):
    result = []
    for q, polynomial in enumerate(coefficients):
        terms = []
        for exponents, coefficient in sorted(polynomial.items()):
            j_degree = sum((i + 3) * m for i, m in enumerate(exponents))
            terms.append({'coefficient': str(coefficient), 'b_power': j_degree // 2,
                          'kappa_powers': {str(i + 3): m for i, m in enumerate(exponents) if m}})
        result.append({'q': q, 'terms': terms})
    return result


def run_checks(max_n=64, order=6):
    require(type(max_n) is int and 16 <= max_n <= 64, 'max_n must be an integer in [16,64]')
    require(type(order) is int and 2 <= order <= 6, 'order must be an integer in [2,6]')
    checks = Checks()
    first = stirling_first_rows(max_n + 1)
    second = stirling_second_rows(max_n + 1)
    derivatives = derivative_product_rows(max_n, max_n)
    diagonal = []
    for n in range(max_n + 1):
        checks.equal('first_stirling_row_sum_factorial', sum(first[n]), factorial(n))
        for k in range(max_n + 1):
            moment = moment_count(first[n], k)
            checks.equal('moment_vs_stirling_product', moment,
                         stirling_product_count(first, second, n, k))
            checks.equal('moment_vs_exponential_product_derivatives', moment, derivatives[n][k])
        diagonal.append(moment_count(first[n], n))
    for n, expected in enumerate(OFFICIAL_PREFIX):
        checks.equal('official_prefix', diagonal[n], expected)
    for n in range(max_n):
        checks.true('strict_diagonal_monotonicity', diagonal[n] < diagonal[n + 1])

    coefficients = contraction_partitions(order)
    h, contracted = exponential_recurrence(order)
    for q in range(order + 1):
        checks.equal('contraction_polynomial_identity', coefficients[q], contracted[2 * q])
        for exponents, coefficient in coefficients[q].items():
            checks.equal('contraction_term_identity', coefficient, contracted[2 * q][exponents])
            checks.equal('contraction_weight', sum((i + 1) * m for i, m in enumerate(exponents)), 2 * q)
            checks.equal('contraction_even_gaussian_degree',
                         sum((i + 3) * m for i, m in enumerate(exponents)) % 2, 0)
    for degree in range(1, 2 * order + 1, 2):
        checks.equal('odd_weight_gaussian_vanishing', contracted[degree], {})
    for q, expected in enumerate(known_first_coefficients(2 * order), 1):
        checks.equal('displayed_E1_E2', coefficients[q], expected)
    checks.equal('leading_E1_constant', sum(coefficients[1].values()), Fraction(-1, 12))

    max_j = 2 * order + 2
    bernoulli = bernoulli_recurrence(max_j)
    explicit = bernoulli_stirling(max_j)
    operator_second = stirling_second_rows(max_j)
    euler_polynomial = {(1, 1): 1}
    for j in range(1, max_j + 1):
        checks.equal('bernoulli_polynomial_identity', bernoulli[j], explicit[j])
        for p in (Fraction(0), Fraction(1, 7), Fraction(1, 2), Fraction(6, 7), Fraction(1)):
            checks.equal('bernoulli_rational_evaluation', polynomial_at(bernoulli[j], p),
                         polynomial_at(explicit[j], p))
        checks.equal('bernoulli_at_zero', polynomial_at(bernoulli[j], 0), 0)
        checks.equal('bernoulli_at_one', polynomial_at(bernoulli[j], 1), int(j == 1))
        if j > 1:
            euler_polynomial = euler_bernoulli_step(euler_polynomial)
        expanded = {}
        for v in range(1, j + 1):
            for p_power, coefficient in enumerate(bernoulli[v]):
                if coefficient:
                    expanded[v, p_power] = operator_second[j][v] * coefficient
        checks.equal('euler_bernoulli_operator_polynomial', euler_polynomial, expanded)
    for j in range(max_j + 1):
        for degree in range(33):
            falling = 1
            rhs = 0
            for v in range(j + 1):
                if v:
                    falling *= degree - v + 1
                rhs += operator_second[j][v] * falling
            checks.equal('euler_operator_on_monomials', degree ** j, rhs)

    for n in range(max_n):
        equality = diagonal[n]
        midpoint = Fraction(diagonal[n] + diagonal[n + 1], 2)
        checks.equal('threshold_exact_equality_ge', threshold_ge(diagonal, equality), n)
        checks.equal('threshold_exact_equality_gt', threshold_gt(diagonal, equality), n + 1)
        checks.equal('threshold_between_ge', threshold_ge(diagonal, midpoint), n + 1)
        checks.equal('threshold_between_gt', threshold_gt(diagonal, midpoint), n + 1)
        for x in (Fraction(equality) - Fraction(1, 2), Fraction(equality),
                  Fraction(equality) + Fraction(1, 2), midpoint):
            checks.equal('threshold_ge_vs_linear_scan', threshold_ge(diagonal, x),
                         next(i for i, a in enumerate(diagonal) if a >= x))
            checks.equal('threshold_gt_vs_linear_scan', threshold_gt(diagonal, x),
                         next(i for i, a in enumerate(diagonal) if a > x))

    # Exact finite rounding lemma: supplied strict brackets imply the bounds.
    # These brackets are constructed from exact integers, never from an
    # unproved finite-size asymptotic error constant.
    for lower in range(max_n - 1):
        upper = lower + 2
        for left in (Fraction(lower), Fraction(4 * lower + 1, 4)):
            for right in (Fraction(upper), Fraction(4 * upper - 1, 4)):
                nu, epsilon = (left + right) / 2, (right - left) / 2
                n_minus, n_plus = floor_fraction(nu - epsilon), ceil_fraction(nu + epsilon)
                checks.equal('rounding_left_endpoint', n_minus, lower)
                checks.equal('rounding_right_endpoint', n_plus, upper)
                for x in (Fraction(diagonal[lower + 1]),
                          Fraction(diagonal[lower] + diagonal[upper], 2)):
                    checks.true('strict_finite_bracket', diagonal[n_minus] < x < diagonal[n_plus])
                    checks.true('equality_safe_window', n_minus + 1 <= threshold_ge(diagonal, x)
                                <= threshold_gt(diagonal, x) <= n_plus)

    payload = {
        'bounds': {'max_n': max_n, 'max_k': max_n, 'contraction_order': order,
                   'bernoulli_order': max_j, 'operator_monomial_degree': 32},
        'check_counts': dict(sorted(checks.counts.items())),
        'total_exact_checks': sum(checks.counts.values()),
        'diagonal': [str(value) for value in diagonal],
        'contractions': serialize_contractions(coefficients),
        'contraction_term_counts': [len(poly) for poly in coefficients],
        'formal_H_term_counts': [len(poly) for poly in h],
        'bernoulli_polynomials': {str(j): bernoulli[j] for j in range(1, max_j + 1)},
        'official_prefix': {'offset': 0, 'count': len(OFFICIAL_PREFIX),
                            'source': SOURCE_URL, 'snapshot_sha256': SOURCE_SHA256},
    }
    digest = hashlib.sha256(json.dumps(payload, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    return {'schema': 'report154.exact-checks.v1', 'status': 'pass',
            'python_optimization': sys.flags.optimize, 'mathematical_payload_sha256': digest,
            'scope': 'Finite exact identities only; no asymptotic remainder or onset certification.',
            'payload': payload}


def emit_json(result, output=None):
    data = (json.dumps(result, indent=2, sort_keys=True) + '\n').encode('utf-8')
    if output is None:
        sys.stdout.write(data.decode('utf-8'))
    else:
        with fresh_file(output) as stream:
            stream.write(data)


def bounded_int(minimum, maximum):
    def parse(value):
        try:
            result = int(value)
        except ValueError as error:
            raise argparse.ArgumentTypeError('An integer is required') from error
        if not minimum <= result <= maximum:
            raise argparse.ArgumentTypeError(f'Value must be in [{minimum},{maximum}]')
        return result
    return parse


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n', type=bounded_int(16, 64), default=64)
    parser.add_argument('--order', type=bounded_int(2, 6), default=6)
    parser.add_argument('--output', help='Create one fresh JSON file; existing paths are never replaced')
    args = parser.parse_args(argv)
    try:
        emit_json(run_checks(args.max_n, args.order), args.output)
    except (CheckFailure, OSError, ValueError, RuntimeError) as error:
        parser.exit(1, f'error: {error}\n')


if __name__ == '__main__':
    main()
