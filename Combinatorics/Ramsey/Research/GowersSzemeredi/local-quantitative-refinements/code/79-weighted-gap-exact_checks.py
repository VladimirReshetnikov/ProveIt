#!/usr/bin/env python3
"""Report291: bounded exact certificates and identities, not a formal proof."""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
import json
import random
import sys

sys.dont_write_bytecode = True
MAX_SUPPORT = 48
MAX_COORDINATE = 96
MAX_FINITE_ORDER = 48
MAX_TARGET_ORDER = 4096
MAX_WEIGHT_BITS = 64
MAX_DENOMINATOR_BITS = 32
MAX_POLYNOMIAL_DEGREE = 24
MAX_HISTOGRAM_BITS = 4096
RANDOM_SEED = 683744248


def require(condition, message):
    """Mathematical checks and safety guards remain active under python -O."""
    if not condition:
        raise RuntimeError(message)


def bounded_integer(value, name, low, high):
    if type(value) is not int or not low <= value <= high:
        raise ValueError(f'{name} must be an integer from {low} through {high}')
    return value


def _exact(value, *, nonnegative=True, bits=MAX_WEIGHT_BITS, denominator_bits=MAX_DENOMINATOR_BITS):
    if type(value) not in (int, Fraction):
        raise ValueError('exact int or Fraction required; bool and float are rejected')
    value = Fraction(value)
    if ((nonnegative and value < 0) or value.numerator.bit_length() > bits
            or value.denominator.bit_length() > denominator_bits):
        raise ValueError('exact number has wrong sign or exceeds arithmetic limits')
    return value


def _weight_vector(weights, length):
    if type(weights) is not tuple or len(weights) != length:
        raise ValueError('weights must be a tuple of the exact required length')
    values = tuple(_exact(w) for w in weights)
    if not any(values):
        raise ValueError('at least one weight must be positive')
    return values


def _finite_modulus(modulus):
    if modulus is not None:
        bounded_integer(modulus, 'target modulus', 1, MAX_TARGET_ORDER)
    return modulus


@dataclass(frozen=True)
class Energy:
    ordinary: object
    respected: object

    def __post_init__(self):
        for value in (self.ordinary, self.respected):
            _exact(value, bits=16384, denominator_bits=16384)
        if self.ordinary <= 0 or self.respected > self.ordinary:
            raise ValueError('energy requires 0 <= respected <= ordinary and ordinary > 0')

    @property
    def ratio(self):
        return Fraction(self.respected, self.ordinary)


def cyclic_energy(order, values, weights, target_modulus=None, method='pairs'):
    """Exact cyclic-domain energy: pairs or independent forced-fourth enumeration."""
    bounded_integer(order, 'source order', 1, MAX_FINITE_ORDER)
    if type(values) is not tuple or len(values) != order:
        raise ValueError('values must be a tuple of the exact source order')
    for value in values:
        bounded_integer(value, 'target value', -MAX_TARGET_ORDER, MAX_TARGET_ORDER)
    weights = _weight_vector(weights, order)
    _finite_modulus(target_modulus)
    if type(method) is not str or method not in ('pairs', 'triples'):
        raise ValueError('method must be pairs or triples')
    if method == 'triples':
        ordinary = respected = Fraction(0)
        for i, j, k in product(range(order), repeat=3):
            l = (i + j - k) % order
            mass = weights[i] * weights[j] * weights[k] * weights[l]
            ordinary += mass
            defect = values[i] + values[j] - values[k] - values[l]
            if defect == 0 if target_modulus is None else defect % target_modulus == 0:
                respected += mass
        return Energy(ordinary, respected)
    ordinary, respected = defaultdict(Fraction), defaultdict(Fraction)
    for i, wi in enumerate(weights):
        for j, wj in enumerate(weights):
            s, v = (i + j) % order, values[i] + values[j]
            if target_modulus is not None:
                v %= target_modulus
            ordinary[s] += wi * wj
            respected[s, v] += wi * wj
    return Energy(sum(v * v for v in ordinary.values()), sum(v * v for v in respected.values()))


# Polynomials are ascending coefficient tuples. Internal helpers operate only on
# already checked, bounded data; public entry points validate before arithmetic.
def _trim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return tuple(p) if p else (0,)


def _poly(p):
    if type(p) is not tuple or not 1 <= len(p) <= MAX_POLYNOMIAL_DEGREE + 1:
        raise ValueError('polynomial must be a nonempty tuple of degree at most 24')
    return _trim(tuple(_exact(v, nonnegative=False) for v in p))


def _padd(a, b):
    return _trim(tuple((a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
                       for i in range(max(len(a), len(b)))))


def _pscale(a, s):
    return _trim(tuple(s * v for v in a))


def _pmul(a, b):
    p = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            p[i + j] += x * y
    return _trim(p)


def polynomial_multiply(a, b):
    a, b = _poly(a), _poly(b)
    if len(a) + len(b) - 2 > MAX_POLYNOMIAL_DEGREE:
        raise ValueError('product degree exceeds 24')
    return _pmul(a, b)


def polynomial_derivative(p):
    p = _poly(p)
    return _trim(tuple(i * p[i] for i in range(1, len(p))))


def reduce_minimizer(p):
    """Exact remainder modulo t^4+4t^2-2; no numerical root evaluation."""
    out = list(_poly(p))
    for i in range(len(out) - 1, 3, -1):
        v = out[i]
        out[i] = 0
        out[i - 2] -= 4 * v
        out[i - 4] += 2 * v
    return _trim(out[:4])


def polynomial_evaluate(p, x):
    p, x = _poly(p), _exact(x, nonnegative=False)
    result = Fraction(0)
    for v in reversed(p):
        result = result * x + v
    return result


def cut_polynomial_counts(order, weight_exponents=None):
    """Literal ordered C3/C4 triples, with the fourth source entry forced.

    None gives a multivariate monomial indexed by the multiplicities of source
    vertices. A tuple of exponents gives a one-variable weight substitution.
    """
    if type(order) is not int or order not in (3, 4):
        raise ValueError('polynomial cut counts support only source orders 3 and 4')
    if weight_exponents is not None:
        if type(weight_exponents) is not tuple or len(weight_exponents) != order:
            raise ValueError('weight exponents must be a tuple of the exact source order')
        for v in weight_exponents:
            bounded_integer(v, 'weight exponent', 0, 6)
    ordinary, respected = Counter(), Counter()
    for i, j, k in product(range(order), repeat=3):
        l = (i + j - k) % order
        indices = (i, j, k, l)
        monomial = (tuple(indices.count(v) for v in range(order)) if weight_exponents is None
                    else sum(weight_exponents[v] for v in indices))
        ordinary[monomial] += 1
        if i + j == k + l:
            respected[monomial] += 1
    return dict(ordinary=dict(sorted(ordinary.items())), respected=dict(sorted(respected.items())))


def check_cut_polynomials():
    c3 = cut_polynomial_counts(3)
    expected = {(4, 0, 0): 1, (0, 4, 0): 1, (0, 0, 4): 1,
                (2, 2, 0): 4, (0, 2, 2): 4, (2, 0, 2): 4, (1, 2, 1): 4}
    require(c3['respected'] == expected, 'all C3 respected polynomial coefficients')
    failed = Counter(c3['ordinary']); failed.subtract(c3['respected'])
    require({k: v for k, v in failed.items() if v} == {(2, 1, 1): 4, (1, 1, 2): 4},
            'C3 failure polynomial is 4abc(a+c)')
    symmetric = cut_polynomial_counts(3, (0, 1, 0))
    require(symmetric == dict(ordinary={0: 6, 1: 8, 2: 12, 4: 1},
                             respected={0: 6, 2: 12, 4: 1}), 'symmetric C3 polynomial')
    c4 = cut_polynomial_counts(4, (0, 1, 1, 0))
    require(c4 == dict(ordinary={0: 6, 1: 8, 2: 36, 3: 8, 4: 6},
                      respected={0: 6, 2: 24, 3: 8, 4: 6}), 'all C4 polynomial coefficients')
    value = cyclic_energy(4, (0, 1, 2, 3), (1, Fraction(3, 5), Fraction(3, 5), 1))
    require(value == Energy(Fraction(16416, 625), Fraction(10716, 625)), 'C4 rational weights')
    n = (6, 0, 12, 0, 1)
    require(reduce_minimizer((-2, 0, 4, 0, 1)) == (0,), 'minimizer defining polynomial')
    require(reduce_minimizer(_pmul((2, 0, 1), (2, 0, 1))) == (6,), '(t^2+2)^2=6')
    require(reduce_minimizer(n) == (8, 0, 8), 'C3 numerator = 8(t^2+1)')
    derivative_numerator = _padd(n, _pscale(_pmul((0, 1), polynomial_derivative(n)), -1))
    require(derivative_numerator == (6, 0, -12, 0, -3), 'derivative numerator = -3(t^4+4t^2-2)')
    require(reduce_minimizer(derivative_numerator) == (0,), 'minimizer stationarity')
    require(polynomial_evaluate((-2, 0, 4, 0, 1), Fraction(2, 3)) < 0
            < polynomial_evaluate((-2, 0, 4, 0, 1), Fraction(7, 10)), 'positive root bracket')
    require(342 ** 2 - 6 * 139 ** 2 == 1038 and 11 ** 2 * 6 > 25 ** 2,
            'strict rational comparison integer squares')
    return dict(C3=c3, C3_symmetric=symmetric, C4=c4, C4_rational_energy=value,
                minimizer_polynomial=(-2, 0, 4, 0, 1), root_bracket=(Fraction(2, 3), Fraction(7, 10)),
                rational_lower_margin_square=1038)


C9_EXPECTED = (
    (81, 53, 53, 53, 53, 53, 53, 53, 53),
    (81, 53, 41, 41, 41, 41, 41, 41, 53),
    (81, 53, 41, 45, 45, 45, 45, 41, 53),
    (81, 53, 41, 45, 65, 65, 45, 41, 53),
    (81, 53, 41, 33, 29, 29, 33, 41, 53),
    (81, 53, 41, 33, 29, 29, 33, 41, 53),
    (81, 53, 41, 45, 41, 41, 45, 41, 53),
    (81, 53, 41, 45, 65, 65, 45, 41, 53),
)


def c9_interval_row(separation, defect_order):
    bounded_integer(separation, 'exceptional-edge separation', 1, 4)
    if defect_order is not None:
        bounded_integer(defect_order, 'defect order', 2, MAX_TARGET_ORDER)
    rows = []
    for direction in range(9):
        hist = Counter()
        for start in range(9):
            count = sum((start + j) % 9 in (0, separation) for j in range(direction))
            hist[count if defect_order is None else count % defect_order] += 1
        rows.append(sum(v * v for v in hist.values()))
    return tuple(rows)


def check_c9():
    rows = []
    for q in (2, None):
        for k in range(1, 5):
            masses = c9_interval_row(k, q)
            require(masses == C9_EXPECTED[len(rows)], 'C9 full derivative histogram row')
            values = [0]
            for edge in range(8):
                values.append(values[-1] - 2 + 9 * (edge in (0, k)))
            modulus = 18 if q == 2 else None
            energies = cyclic_energy(9, tuple(values), (1,) * 9, modulus, 'triples')
            require(energies == Energy(729, sum(masses)), 'C9 actual map realizes interval counts')
            require(energies == cyclic_energy(9, tuple(values), (1,) * 9, modulus), 'C9 pair oracle')
            if q is None:
                for finite_q in (3, 4, 17, 4096):
                    require(c9_interval_row(k, finite_q) == masses, 'all tested orders above two agree')
            rows.append(dict(separation=k, defect_order=q, derivative_masses=masses, energy=energies))
    support = (0, 1, 3, 4, 6, 7)
    weights = tuple(int(i in support) for i in range(9))
    spike = cyclic_energy(9, (1,) + (0,) * 8, weights, 2, 'triples')
    require(spike == Energy(162, 106), 'C9 single-spike certificate')
    return dict(rows=rows, spike_support=support, spike_energy=spike,
                target_pattern_classes=2, interval_counts_range=(0, 2))


BRANCH_ROWS = (
    ((0, 0, 0, 1, 2), (1,) * 5),
    ((0, 0, 0, 1, 1, 2), (1,) * 6),
    ((0, 0, 0, 1, 1, 1, 1, 1), (1, 1, 3, 3, 2, 1, 1, 1)),
    ((0, 0, 0, 1, 1, 1, 1, 2), (0, 0, 1, 1, 1, 1, 1, 1)),
    ((0, 0, 0, 1, 1, 1, 2, 1), (1,) * 8),
    ((0, 0, 0, 1, 1, 1, 2, 2, 3), (1,) * 9),
    ((0, 0, 0, 1, 1, 1, 2, 2, 2, 2), (0, 0, 1, 1, 1, 1, 1, 1, 0, 1)),
)
BRANCH_MAXIMA = tuple(tuple(Fraction(v) for v in row.split()) for row in (
    '57/85 57/85 57/85 57/85 57/85 57/85 57/85 57/85 57/85 57/85',
    '25/37 49/73 49/73 49/73 49/73 49/73 49/73 49/73 49/73 49/73',
    '2065/3169 1999/3071 1963/3023 1943/3003 1937/2997 387/599 387/599 387/599 387/599 387/599',
    '25/37 49/73 49/73 49/73 49/73 49/73 49/73 49/73 49/73 49/73',
    '43/69 59/96 57/91 5/8 109/173 27/43 27/43 27/43 27/43 27/43',
    '413/657 389/601 359/559 15/23 333/509 325/497 323/491 107/163 107/163 107/163',
    '159/247 151/231 145/221 143/215 47/71 139/211 139/211 139/211 139/211 139/211',
))


def branch_data(row):
    bounded_integer(row, 'branch row', 1, 7)
    return BRANCH_ROWS[row - 1]


def _branch_inputs(coefficients, weights, modulus):
    if type(coefficients) is not tuple or not 1 <= len(coefficients) <= 10:
        raise ValueError('branch coefficients must be a tuple of one through ten entries')
    for c in coefficients:
        bounded_integer(c, 'branch coefficient', 0, 3)
    weights = _weight_vector(weights, len(coefficients))
    if modulus is not None:
        bounded_integer(modulus, 'branch source modulus', 10, 18)
    return coefficients, weights, modulus


def coefficient_histogram(coefficients, weights, modulus=None, method='pairs'):
    """Weighted C_N(z,t), retaining the essential finite-domain slope N*d."""
    c, weights, modulus = _branch_inputs(coefficients, weights, modulus)
    if type(method) is not str or method not in ('pairs', 'quadruples'):
        raise ValueError('method must be pairs or quadruples')
    histogram = defaultdict(Fraction)
    support = tuple(i for i, w in enumerate(weights) if w)
    if method == 'pairs':
        pairs = defaultdict(Fraction)
        for i, j in product(support, repeat=2):
            pairs[i + j, c[i] + c[j]] += weights[i] * weights[j]
        for (s, r), weight in pairs.items():
            for (other_s, other_r), other_weight in pairs.items():
                delta = s - other_s
                if delta == 0 if modulus is None else delta % modulus == 0:
                    histogram[0 if modulus is None else delta // modulus, r - other_r] += weight * other_weight
    else:
        for i, j, k, l in product(support, repeat=4):
            delta = i + j - k - l
            if delta == 0 if modulus is None else delta % modulus == 0:
                histogram[0 if modulus is None else delta // modulus, c[i] + c[j] - c[k] - c[l]] += (
                    weights[i] * weights[j] * weights[k] * weights[l])
    return dict(sorted(histogram.items()))


def _defect_histogram(histogram):
    if type(histogram) is not dict or not 1 <= len(histogram) <= 39:
        raise ValueError('defect histogram must be a nonempty dict with at most 39 entries')
    for key, count in histogram.items():
        if type(key) is not tuple or len(key) != 2:
            raise ValueError('defect keys must be (wrap, coefficient) tuples')
        bounded_integer(key[0], 'wrap index', -1, 1)
        bounded_integer(key[1], 'defect coefficient', -6, 6)
        if not _exact(count, bits=MAX_HISTOGRAM_BITS, denominator_bits=MAX_HISTOGRAM_BITS):
            raise ValueError('histogram entries must be positive')
    if (0, 0) not in histogram:
        raise ValueError('histogram must include its diagonal')
    if any(histogram.get((-z, -t)) != count for (z, t), count in histogram.items()):
        raise ValueError('histogram must have reflection symmetry')
    return histogram


def _symbolic_numerator(histogram, q, h):
    return sum(count for (z, t), count in histogram.items()
               if (z == 0 if h is None else True)
               and (t + z * (h or 0) == 0 if q is None else (t + z * (h or 0)) % q == 0))


def symbolic_numerator(histogram, q, h):
    """h=None means no respected wrapping comparisons; q=None means infinite order."""
    histogram = _defect_histogram(histogram)
    if q is not None:
        bounded_integer(q, 'order of nonzero u', 2, MAX_TARGET_ORDER)
    m = max(abs(t) for z, t in histogram)
    if h is not None:
        bounded_integer(h, 'slope coefficient', -m, m)
    return _symbolic_numerator(histogram, q, h)


def symbolic_maximum(histogram):
    """Exactly enumerates the proof's bounded equality patterns, not arbitrary maps.

    For M>0: 2M(2M+1) slope/order evaluations and 2M no-wrap evaluations.
    For M=0 each count is one. Duplicate equality patterns are not deduplicated.
    """
    histogram = _defect_histogram(histogram)
    m = max(abs(t) for z, t in histogram)
    orders = (*range(2, 2 * m + 1), None)
    best, maximizer, patterns = -1, None, []
    for q in orders:
        for h in range(-m, m + 1):
            numerator = _symbolic_numerator(histogram, q, h)
            patterns.append(dict(order_u=q, h=h, numerator=numerator))
            if numerator > best:
                best, maximizer = numerator, dict(order_u=q, h=h)
    zero_wrap = []
    for q in orders:
        numerator = _symbolic_numerator(histogram, q, None)
        require(numerator <= best, 'no-respected-wrap case is dominated')
        zero_wrap.append(dict(order_u=q, numerator=numerator))
    return dict(energy=Energy(sum(histogram.values()), best), M=m, maximizer=maximizer,
                symbolic_patterns=len(patterns), no_wrap_patterns=len(zero_wrap),
                evaluations=patterns, no_wrap_evaluations=zero_wrap)


def realized_pair_energy(coefficients, weights, modulus, q, h):
    """Realize every symbolic slope in C_(Nq) or Z with u=N and d=h.

    h=None uses target Z x C_q (or Z x Z), so v is independent of u.
    """
    c, weights, modulus = _branch_inputs(coefficients, weights, modulus)
    if q is not None:
        bounded_integer(q, 'order of nonzero u', 2, MAX_TARGET_ORDER)
    if h is not None:
        bounded_integer(h, 'slope coefficient', -6, 6)
    ordinary, respected = defaultdict(Fraction), defaultdict(Fraction)
    for i, wi in enumerate(weights):
        for j, wj in enumerate(weights):
            s, r = i + j, c[i] + c[j]
            domain_sum = s if modulus is None else s % modulus
            if h is None:
                value = (s, r if q is None else r % q)
            elif modulus is None:
                value = r if q is None else r % q
            else:
                value = h * s + modulus * r
                if q is not None:
                    value %= modulus * q
            ordinary[domain_sum] += wi * wj
            respected[domain_sum, value] += wi * wj
    return Energy(sum(v * v for v in ordinary.values()), sum(v * v for v in respected.values()))


def branch_certificate(row, modulus=None):
    c, w = branch_data(row)
    histogram = coefficient_histogram(c, w, modulus)
    result = symbolic_maximum(histogram)
    result.update(row=row, source_modulus=modulus, coefficients=c, weights=w, histogram=histogram)
    return result


def check_branches():
    rows, pattern_count, no_wrap_count, realizations = [], 0, 0, 0
    for row in range(1, 8):
        certificates = []
        for column, modulus in enumerate((*range(10, 19), None)):
            certificate = branch_certificate(row, modulus)
            c, w = branch_data(row)
            require(certificate['histogram'] == coefficient_histogram(c, w, modulus, 'quadruples'),
                    'independent literal weighted quadruple branch histogram')
            require(certificate['energy'].ratio == BRANCH_MAXIMA[row - 1][column], 'exact branch table entry')
            require(certificate['energy'].ratio <= Fraction(25, 37) < Fraction(17, 25), 'strict branch margin')
            for evaluation in certificate['evaluations']:
                actual = realized_pair_energy(c, w, modulus, evaluation['order_u'], evaluation['h'])
                require(actual.respected == evaluation['numerator'] and actual.ordinary == certificate['energy'].ordinary,
                        'actual target realizes each symbolic pattern')
                realizations += 1
            for evaluation in certificate['no_wrap_evaluations']:
                actual = realized_pair_energy(c, w, modulus, evaluation['order_u'], None)
                require(actual.respected == evaluation['numerator'], 'independent target realizes no-respected-wrap pattern')
                realizations += 1
            m = certificate['M']
            expected = 2 * m * (2 * m + 1) if m else 1
            require(certificate['symbolic_patterns'] == expected, 'declared finite equality-pattern count')
            pattern_count += certificate['symbolic_patterns']
            no_wrap_count += certificate['no_wrap_patterns']
            certificates.append(certificate)
        maximum = max(c['energy'].ratio for c in certificates)
        attaining = tuple(c['source_modulus'] for c in certificates if c['energy'].ratio == maximum)
        rows.append(dict(row=row, maximum=maximum, attaining_moduli=attaining, certificates=certificates))
    require(rows[5]['maximum'] == Fraction(323, 491) and rows[5]['attaining_moduli'] == (16,), 'correct row-six maximum')
    require(rows[6]['maximum'] == Fraction(143, 215) and rows[6]['attaining_moduli'] == (13,), 'correct row-seven maximum')
    c, w = branch_data(3)
    require(coefficient_histogram(c, w) == {(0, -1): 530, (0, 0): 1935, (0, 1): 530}, 'row-three forced losses')
    pair_weights = tuple(sum(w[i] * w[s - i] for i in range(len(w)) if 0 <= s - i < len(w))
                         for s in range(2 * len(w) - 1))
    require(pair_weights == (1, 2, 7, 12, 19, 24, 25, 22, 18, 16, 11, 6, 3, 2, 1), 'row-three pair weights')
    require(tuple(sum(coefficient_histogram(c, w, n).values()) for n in range(10, 16))
            == (3169, 3071, 3023, 3003, 2997, 2995), 'row-three denominator list')
    require(Fraction(2109, 3169) < Fraction(25, 37), 'target-independent row-three loose certificate')
    return dict(certificate_count=70, finite_wrap_cases=63, no_wrap_cases=7,
                symbolic_pattern_evaluations=pattern_count, no_wrap_pattern_evaluations=no_wrap_count,
                actual_target_realizations=realizations, rows=rows,
                row_three_pair_weights=pair_weights, row_three_forced_failure=1060,
                row_three_loose_bound=Fraction(2109, 3169))


def finite_quotient_lift(quotient_order, kernel_order, weights):
    """C_(km) -> C_m: count all quotient patterns and check both weighted energies."""
    bounded_integer(quotient_order, 'quotient order', 1, 8)
    bounded_integer(kernel_order, 'kernel order', 1, 16)
    n = quotient_order * kernel_order
    if n > MAX_FINITE_ORDER:
        raise ValueError('lifted source order exceeds 48')
    weights = _weight_vector(weights, quotient_order)
    patterns = Counter()
    for i, j, k in product(range(n), repeat=3):
        l = (i + j - k) % n
        patterns[(i % quotient_order, j % quotient_order, k % quotient_order, l % quotient_order)] += 1
    require(len(patterns) == quotient_order ** 3, 'all quotient additive patterns are represented')
    require(set(patterns.values()) == {kernel_order ** 3}, 'each quotient pattern has exactly |K|^3 lifts')
    quotient = cyclic_energy(quotient_order, tuple(range(quotient_order)), weights)
    lifted = cyclic_energy(n, tuple(i % quotient_order for i in range(n)),
                           tuple(weights[i % quotient_order] for i in range(n)))
    require(lifted == Energy(kernel_order ** 3 * quotient.ordinary, kernel_order ** 3 * quotient.respected),
            'both finite quotient energy identities')
    return dict(quotient_order=quotient_order, kernel_order=kernel_order,
                source_order=n, patterns=dict(sorted(patterns.items())), quotient_energy=quotient, lifted_energy=lifted)


def check_finite_lifts():
    rows = []
    for q, weights, maximum_kernel in ((3, (5, 3, 5), 16), (4, (5, 3, 3, 5), 12)):
        for k in range(1, maximum_kernel + 1):
            result = finite_quotient_lift(q, k, weights)
            result['pattern_count'] = len(result.pop('patterns'))
            rows.append(result)
    return dict(cases=len(rows), rows=rows)


def _finite_weight(weight):
    if type(weight) is not dict or not 1 <= len(weight) <= MAX_SUPPORT:
        raise ValueError('weight must be a nonempty dict with at most 48 entries')
    out = {}
    for j, value in weight.items():
        bounded_integer(j, 'support coordinate', -MAX_COORDINATE, MAX_COORDINATE)
        value = _exact(value)
        if value:
            out[j] = value
    if not out:
        raise ValueError('weight must contain a positive entry')
    return out


def _conv(a, b, modulus=None):
    out = defaultdict(Fraction)
    for i, x in a.items():
        for j, y in b.items():
            out[(i + j) if modulus is None else (i + j) % modulus] += x * y
    return dict(out)


def _add(a, b, scale=1, shift=0, modulus=None):
    out = defaultdict(Fraction, a)
    for i, x in b.items():
        key = i + shift if modulus is None else (i + shift) % modulus
        out[key] += scale * x
    return dict(out)


def _norm(a):
    return sum(x * x for x in a.values())


def _residue_energy(fibers, modulus=None, carry=1):
    a, b, c = fibers
    aa, ab, ac = (_conv(a, v, modulus) for v in (a, b, c))
    bb, bc, cc = _conv(b, b, modulus), _conv(b, c, modulus), _conv(c, c, modulus)
    last = _add(bb, ac, 2, modulus=modulus)
    ordinary = (_norm(_add(aa, bc, 2, carry, modulus))
                + _norm(_add(_add({}, ab, 2), cc, 1, carry, modulus)) + _norm(last))
    respected = _norm(aa) + 4 * _norm(bc) + 4 * _norm(ab) + _norm(cc) + _norm(last)
    return Energy(ordinary, respected)


def staircase_residue_energy(weight):
    weight = _finite_weight(weight)
    fibers = [{}, {}, {}]
    for j, w in weight.items():
        n, r = divmod(j, 3)
        fibers[r][n] = w
    return _residue_energy(fibers)


def staircase_direct_energy(weight, method='pairs'):
    weight = _finite_weight(weight)
    if type(method) is not str or method not in ('pairs', 'quadruples'):
        raise ValueError('method must be pairs or quadruples')
    if method == 'quadruples':
        if len(weight) > 8:
            raise ValueError('literal staircase oracle is limited to eight positive support points')
        ordinary = respected = Fraction(0)
        for i, j, k, l in product(weight, repeat=4):
            if i + j == k + l:
                mass = weight[i] * weight[j] * weight[k] * weight[l]
                ordinary += mass
                if i // 3 + j // 3 == k // 3 + l // 3:
                    respected += mass
        return Energy(ordinary, respected)
    pairs, graph = defaultdict(Fraction), defaultdict(Fraction)
    for i, wi in weight.items():
        for j, wj in weight.items():
            pairs[i + j] += wi * wj
            graph[i + j, i // 3 + j // 3] += wi * wj
    return Energy(_norm(pairs), _norm(graph))


def finite_cut_residue_energy(kernel_order, weights):
    """Finite index-three cut C_(3m), K=3C_(3m), with carry 3t=1 in K=C_m."""
    bounded_integer(kernel_order, 'kernel order', 1, 16)
    weights = _weight_vector(weights, 3 * kernel_order)
    fibers = tuple({j: weights[3 * j + r] for j in range(kernel_order)} for r in range(3))
    return _residue_energy(fibers, kernel_order, 1)


def triangle_counts(length):
    bounded_integer(length, 'triangle length', 1, 128)
    pair_counts = Counter(i + j for i in range(length) for j in range(length))
    h = sum(v * v for v in pair_counts.values())
    j = sum(v * pair_counts.get(k - 1, 0) for k, v in pair_counts.items())
    require(3 * h == 2 * length ** 3 + length, 'exact H_M formula')
    require(3 * j == 2 * length ** 3 - 2 * length, 'exact J_M formula')
    require(h - j == length, 'exact H_M-J_M=M identity')
    return dict(M=length, H=h, J=j)


def finite_error_identity(length):
    """Cross-multiply exact polynomials; works for any t, with N=t^4+12t^2+6."""
    data = triangle_counts(length)
    n, eight_t = (6, 0, 12, 0, 1), (0, 8)
    d = _padd(n, eight_t)
    nh, dm = _pscale(n, data['H']), _padd(_pscale(n, data['H']), _pscale(eight_t, data['J']))
    v = 2 * length ** 2 + 1
    candidate_num = _pscale(n, v)
    candidate_den = _padd(_pscale(d, v), _pscale(eight_t, -3))
    require(_pmul(nh, candidate_den) == _pmul(dm, candidate_num), 'exact finite-ratio formula')
    difference_num = _padd(_pmul(nh, d), _pscale(_pmul(n, dm), -1))
    difference_den = _pmul(dm, d)
    error_num = _pscale(_pmul(n, eight_t), 3)
    error_den = _pmul(d, _padd(_pscale(d, 2 * length ** 2 - 2), _pscale(n, 3)))
    require(_pmul(difference_num, error_den) == _pmul(difference_den, error_num), 'exact finite-error formula')
    data.update(respected_polynomial=nh, ordinary_polynomial=dm,
                reduced_respected=reduce_minimizer(nh), reduced_ordinary=reduce_minimizer(dm))
    return data


def check_staircase():
    rng = random.Random(RANDOM_SEED)
    for _ in range(256):
        f = {j: Fraction(rng.randrange(5), rng.randrange(1, 6)) for j in range(-12, 14)}
        require(staircase_residue_energy(f) == staircase_direct_energy(f), 'seeded rational residue identity')
    for _ in range(24):
        support = rng.sample(range(-15, 16), 8)
        f = {j: Fraction(rng.randrange(1, 5), rng.randrange(1, 5)) for j in support}
        require(staircase_residue_energy(f) == staircase_direct_energy(f, 'quadruples'), 'literal staircase oracle')
    for m in range(1, 17):
        weights = tuple(Fraction(rng.randrange(1, 6), rng.randrange(1, 6)) for _ in range(3 * m))
        require(finite_cut_residue_energy(m, weights) == cyclic_energy(3 * m, tuple(j % 3 for j in range(3 * m)), weights),
                'finite index-three residue formula with carry')
    rows = [finite_error_identity(m) for m in range(1, 129)]
    # Rational t also tests the whole finite-energy identity, independently of
    # the algebraic minimizer and the polynomial cross-multiplication above.
    for m in range(1, 17):
        for t in (Fraction(2, 3), Fraction(3, 5), Fraction(7, 10)):
            f = {3 * j + r: (t if r == 1 else 1) for j in range(m) for r in range(3)}
            h, j = rows[m - 1]['H'], rows[m - 1]['J']
            n = t ** 4 + 12 * t ** 2 + 6
            require(staircase_direct_energy(f) == Energy(n * h + 8 * t * j, n * h), 'explicit finite staircase energies')
    return dict(seed=RANDOM_SEED, random_exact_fiber_cases=256, literal_quadruple_cases=24,
                finite_index_three_cases=16, rational_finite_energy_cases=48,
                triangle_and_finite_error_cases=128, rows=rows)


def _algebraic_conv(a, b, modulus):
    out = {}
    for i, x in a.items():
        for j, y in b.items():
            key = (i + j) % modulus
            out[key] = _padd(out.get(key, (0,)), _pmul(x, y))
    return out


def _algebraic_scale(a, scalar):
    return {i: _pmul(value, scalar) for i, value in a.items()}


def _algebraic_shift(a, shift, modulus):
    return {(i + shift) % modulus: value for i, value in a.items()}


def check_attainment_identities():
    """Completed finite identities in Q[t]; no numerical algebraic-root tests.

    Carry one tests constant fibers on C_(3m). Carry zero tests arbitrary
    proportional fibers on C3 x C_m. The written proof, not these samples,
    establishes necessity, sufficiency and the general torsion criterion.
    """
    cases = 0
    t, t2 = (0, 1), (0, 0, 1)
    for m in range(1, 17):
        for carry in (0, 1):
            a = {j: ((1 if carry else 1 + j % 3),) for j in range(m)}
            b, c = _algebraic_scale(a, t), dict(a)
            aa, bc = _algebraic_conv(a, a, m), _algebraic_conv(b, c, m)
            ab, cc = _algebraic_conv(a, b, m), _algebraic_conv(c, c, m)
            bb, ac = _algebraic_conv(b, b, m), _algebraic_conv(a, c, m)
            require(_algebraic_scale(aa, t) == _algebraic_shift(bc, carry, m),
                    't(f0*f0)=shift(f1*f2)')
            require(ab == _algebraic_scale(_algebraic_shift(cc, carry, m), t),
                    'f0*f1=t shift(f2*f2)')
            require(bb == _algebraic_scale(ac, t2), 'f1*f1=t^2(f0*f2)')
            require(_algebraic_conv(aa, a, m) == _algebraic_shift(_algebraic_conv(cc, c, m), 2 * carry, m),
                    'actual cyclic convolution cubic identity')
            cases += 1
    # The first two polynomial identities vanish for A=C=0,B=1;
    # the third is 1=0 and deliberately fails.
    zero, one = (0,), (1,)
    first = _pmul(t, _pmul(zero, zero)) == _pmul(one, zero)
    second = _pmul(zero, one) == _pmul(t, _pmul(zero, zero))
    third = _pmul(one, one) == _pmul(t2, _pmul(zero, zero))
    require(first and second and not third, 'third equality identity excludes the B-only spurious triple')
    return dict(finite_convolution_examples=cases, spurious_B_only_triple_excluded=True,
                scope='Completed finite identities only; not an exhaustive endpoint classification')


def jsonable(value):
    if isinstance(value, Fraction):
        return str(value)
    if isinstance(value, Energy):
        return dict(ordinary=jsonable(value.ordinary), respected=jsonable(value.respected), ratio=str(value.ratio))
    if type(value) is dict:
        if all(type(k) is str for k in value):
            return {k: jsonable(v) for k, v in value.items()}
        return [dict(key=jsonable(k), value=jsonable(v)) for k, v in value.items()]
    if type(value) in (tuple, list):
        return [jsonable(v) for v in value]
    if value is None or type(value) in (str, int, bool):
        return value
    raise ValueError('unsupported JSON value; exact objects only')


def run_checks():
    return dict(report=291, schema_version=1, status='passed',
                scope='Bounded exact arithmetic certificates; written proofs supply arbitrary-group, minimization and nonattainment arguments',
                cut_polynomials=check_cut_polynomials(), C9=check_c9(),
                symbolic_certificates=check_branches(), finite_lifts=check_finite_lifts(),
                staircase=check_staircase(), attainment_identities=check_attainment_identities())


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.parse_args(argv)
    print(json.dumps(jsonable(run_checks()), sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
