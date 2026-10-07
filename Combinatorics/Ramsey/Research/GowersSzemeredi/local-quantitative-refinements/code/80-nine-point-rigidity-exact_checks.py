#!/usr/bin/env python3
"""Read-only exact diagnostics for Report292; no finite check replaces its proofs."""
from __future__ import annotations

import sys
sys.dont_write_bytecode = True
import argparse
from collections import Counter, defaultdict
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations, product
from math import comb
import json

MAX_RANK = 3
MAX_TARGET = 4096
MAX_WEIGHT = (1 << 31) - 1


def require(condition, message):
    """A correctness guard that remains active under Python optimization."""
    if type(condition) is not bool or type(message) is not str:
        raise ValueError('guard requires a bool and a message string')
    if not condition:
        raise RuntimeError(message)


def _integer(value, name, low, high):
    if type(value) is not int or not low <= value <= high:
        raise ValueError(name + ' is outside its bounded integer domain')
    return value


def _exact(value, name, nonnegative=True):
    if type(value) not in (int, Fraction):
        raise ValueError(name + ' must be an exact integer or Fraction')
    if (nonnegative and value < 0) or abs(value.numerator) > MAX_WEIGHT or value.denominator > MAX_WEIGHT:
        raise ValueError(name + ' is outside its bounded rational domain')
    return value


@dataclass(frozen=True)
class Energy:
    ordinary: int | Fraction
    respected: int | Fraction

    def __post_init__(self):
        for value in (self.ordinary, self.respected):
            if type(value) not in (int, Fraction):
                raise ValueError('energies must be exact integers or Fractions')
            if abs(value.numerator).bit_length() > 4096 or value.denominator.bit_length() > 4096:
                raise ValueError('energy exceeds the exact-size bound')
        if not 0 <= self.respected <= self.ordinary or self.ordinary <= 0:
            raise ValueError('energies require 0 <= respected <= ordinary and ordinary > 0')

    @property
    def ratio(self):
        return Fraction(self.respected, self.ordinary)


def points(rank):
    """Lexicographic coordinates for F_3^rank, including rank zero."""
    _integer(rank, 'rank', 0, MAX_RANK)
    return tuple(product(range(3), repeat=rank))


def _target_modulus(modulus):
    if modulus is not None:
        _integer(modulus, 'target modulus', 1, MAX_TARGET)
    return modulus


def _inputs(rank, values, weights, modulus, method):
    domain = points(rank)
    if type(values) is not tuple or len(values) != len(domain):
        raise ValueError('values must be a full-domain tuple')
    for value in values:
        _integer(value, 'target value', -MAX_TARGET, MAX_TARGET)
    if type(weights) is not tuple or len(weights) != len(domain):
        raise ValueError('weights must be a full-domain tuple')
    for weight in weights:
        _exact(weight, 'weight')
    if not any(weights):
        raise ValueError('weight must be nonzero')
    _target_modulus(modulus)
    if type(method) is not str or method not in ('pairs', 'triples'):
        raise ValueError('method must be pairs or triples')
    return domain


def energy(rank, values, weights, modulus=None, method='pairs'):
    """Exact ordered energy in F_3^rank with target Z or C_modulus.

    Ranks 0..3, target integers -4096..4096, moduli 1..4096, and
    rational input numerators/denominators of at most 2^31-1 are supported.
    Pair convolution and source-triple enumeration are independent paths.
    """
    domain = _inputs(rank, values, weights, modulus, method)
    if method == 'pairs':
        source = defaultdict(int)
        lifted = defaultdict(int)
        for i, x in enumerate(domain):
            for j, y in enumerate(domain):
                weight = weights[i] * weights[j]
                total = tuple((a + b) % 3 for a, b in zip(x, y))
                target = values[i] + values[j]
                if modulus is not None:
                    target %= modulus
                source[total] += weight
                lifted[total, target] += weight
        return Energy(sum(v * v for v in source.values()), sum(v * v for v in lifted.values()))
    index = {x: i for i, x in enumerate(domain)}
    ordinary = respected = 0
    for i, x in enumerate(domain):
        for j, y in enumerate(domain):
            for k, z in enumerate(domain):
                w = tuple((a + b - c) % 3 for a, b, c in zip(x, y, z))
                ell = index[w]
                weight = weights[i] * weights[j] * weights[k] * weights[ell]
                ordinary += weight
                defect = values[i] + values[j] - values[k] - values[ell]
                if defect == 0 if modulus is None else defect % modulus == 0:
                    respected += weight
    return Energy(ordinary, respected)


def support_weights(rank, support):
    """Convert a strictly increasing nonempty tuple of point indices to weights."""
    size = len(points(rank))
    if type(support) is not tuple or not 1 <= len(support) <= size:
        raise ValueError('support must be a bounded nonempty tuple')
    for i in support:
        _integer(i, 'support index', 0, size - 1)
    if any(a >= b for a, b in zip(support, support[1:])):
        raise ValueError('support indices must be strictly increasing')
    chosen = set(support)
    return tuple(int(i in chosen) for i in range(size))


def indicator_energy(rank, values, support, modulus=None, method='pairs'):
    return energy(rank, values, support_weights(rank, support), modulus, method)


def _quadruples(rank):
    domain = points(rank)
    index = {x: i for i, x in enumerate(domain)}
    return tuple((i, j, k, index[tuple((a + b - c) % 3 for a, b, c in zip(x, y, z))])
                 for i, x in enumerate(domain) for j, y in enumerate(domain)
                 for k, z in enumerate(domain))


def _support_mask(quadruple):
    mask = 0
    for i in quadruple:
        mask |= 1 << i
    return mask


def _zeta(histogram):
    """Fixed nine-bit subset sum: output[S] = sum_{T subset S} input[T]."""
    result = histogram.copy()
    for bit in range(9):
        flag = 1 << bit
        for mask in range(512):
            if mask & flag:
                result[mask] += result[mask ^ flag]
    return result


def _indicator_arrays(values, modulus=None):
    _inputs(2, values, (1,) * 9, modulus, 'triples')
    ordinary = [0] * 512
    respected = [0] * 512
    for i, j, k, ell in _quadruples(2):
        support = (1 << i) | (1 << j) | (1 << k) | (1 << ell)
        ordinary[support] += 1
        defect = values[i] + values[j] - values[k] - values[ell]
        if defect == 0 if modulus is None else defect % modulus == 0:
            respected[support] += 1
    return _zeta(ordinary), _zeta(respected)


def _hyperplanes(rank):
    """All affine hyperplanes, as bit masks, using normalized linear forms."""
    domain = points(rank)
    normals = [x for x in domain if any(x) and next(v for v in x if v) == 1]
    masks = []
    for normal in normals:
        for level in range(3):
            masks.append(sum(1 << i for i, x in enumerate(domain)
                             if sum(a * b for a, b in zip(normal, x)) % 3 == level))
    return tuple(masks)


def check_lines():
    cases = 0
    for modulus in (None, *range(1, 10)):
        alphabet = range(-2, 3) if modulus is None else range(modulus)
        for values in product(alphabet, repeat=3):
            zero = lambda value: value == 0 if modulus is None else value % modulus == 0
            midpoints = sum(zero(2 * values[i] - values[(i + 1) % 3] - values[(i + 2) % 3])
                            for i in range(3))
            actual = energy(1, values, (1, 1, 1), modulus)
            require(actual == Energy(27, 15 + 4 * midpoints), 'three-point line formula failed')
            require(actual == energy(1, values, (1, 1, 1), modulus, 'triples'), 'line energy paths disagree')
            increments = tuple(values[(i + 1) % 3] - values[i] for i in range(3))
            repeated = any(zero(increments[i] - increments[j]) for i, j in combinations(range(3), 2))
            require(repeated == (midpoints > 0), 'cyclic-increment equivalence failed')
            cases += 1
    require(cases == 2150, 'line diagnostic count failed')
    return dict(cases=cases, ordinary=27, automatic_respected=15,
                per_midpoint_equality=4, failed_line_ratio=Fraction(5, 9),
                target_moduli=(None, *range(1, 10)))


def integer_partitions(total):
    _integer(total, 'partition total', 1, 9)
    def visit(remaining, largest):
        if remaining == 0:
            yield ()
        else:
            for head in range(min(remaining, largest), 0, -1):
                for tail in visit(remaining - head, head):
                    yield (head, *tail)
    return tuple(visit(total, total))


def _cycle_profiles(partition):
    count = len(partition)
    result = set()
    for labels in product(range(count), repeat=9):
        if tuple(labels.count(i) for i in range(count)) != partition:
            continue
        cycles = tuple(labels[j:j + 3] for j in (0, 3, 6))
        if any(len(set(cycle)) == 3 for cycle in cycles):
            continue
        result.add(tuple(sorted(tuple(cycle.count(i) for i in range(count)) for cycle in cycles)))
    return sorted(result)


def _relation_coefficients(rows, wanted):
    # Only the three fixed high-square partitions call this bounded search.
    for multipliers in product(range(-3, 4), repeat=3):
        actual = tuple(sum(c * row[j] for c, row in zip(multipliers, rows))
                       for j in range(len(wanted)))
        if actual == wanted:
            return multipliers
    return None


def check_derivative_partitions():
    partitions = integer_partitions(9)
    high = tuple(p for p in partitions if len(p) > 1 and sum(v * v for v in p) > 45)
    require(high == ((8, 1), (7, 2), (7, 1, 1)), 'high-square partition list failed')
    details = []
    for partition in high:
        profiles = _cycle_profiles(partition)
        require(bool(profiles), 'missing admissible cycle profile')
        for rows in profiles:
            # Integer combinations of the zero cycle sums may force colors equal.
            collapses = []
            for i, j in combinations(range(len(partition)), 2):
                wanted = tuple(int(k == i) - int(k == j) for k in range(len(partition)))
                coefficients = _relation_coefficients(rows, wanted)
                if coefficients is not None:
                    collapses.append(dict(colors=(i, j), coefficients=coefficients))
            if collapses:
                details.append(dict(partition=partition, cycle_rows=rows, forced_equal=collapses[0]))
            else:
                require(partition == (7, 2), 'forbidden partition lacks an integer-relation certificate')
                majority = _relation_coefficients(rows, (3, 0))
                order_two = _relation_coefficients(rows, (-2, 2))
                require(majority is not None and order_two is not None, 'order-two derivative certificate failed')
                require(all(row[1] % 2 == 0 for row in rows), 'C2 realization of (7,2) failed')
                details.append(dict(partition=partition, cycle_rows=rows,
                                    majority_three_zero=majority, exceptional_difference_two_zero=order_two))
    require(sum('forced_equal' not in row for row in details) == 1, 'surviving cycle-profile count failed')
    require(len(partitions) == 30, 'integer partition count failed')
    return dict(partitions_of_nine=len(partitions), nonconstant_above_45=high,
                permitted_above_45=((7, 2),), certificate_rows=details,
                full_plane_bound=Energy(729, 441),
                low_histogram_full_plane_bound=Energy(729, 81 + 2 * 4 * 45))


def check_spike():
    values = (1,) + (0,) * 8
    support = tuple(i for i, (_, y) in enumerate(points(2)) if y in (0, 1))
    six = indicator_energy(2, values, support, 2)
    require(six == Energy(162, 106), 'six-point spike energy failed')
    require(six == indicator_energy(2, values, support, 2, 'triples'), 'spike paths disagree')
    full = energy(2, values, (1,) * 9, 2)
    require(full == Energy(729, 505), 'full-plane spike energy failed')
    require(Fraction(5, 9) < Fraction(49, 81) < six.ratio < Fraction(17, 25), 'witness bounds failed')
    ordinary_polynomial = [0] * 5
    respected_polynomial = [0] * 5
    chosen = set(support)
    for quadruple in _quadruples(2):
        if all(i in chosen for i in quadruple):
            degree = quadruple.count(0)
            ordinary_polynomial[degree] += 1
            if degree % 2 == 0:
                respected_polynomial[degree] += 1
    require(tuple(ordinary_polynomial) == (81, 56, 24, 0, 1), 'weighted spike ordinary polynomial failed')
    require(tuple(respected_polynomial) == (81, 0, 24, 0, 1), 'weighted spike respected polynomial failed')
    spike_weight = Fraction(8, 5)
    weights = tuple(spike_weight if i == 0 else int(i in chosen) for i in range(9))
    weighted = energy(2, values, weights, 2)
    require(weighted == energy(2, values, weights, 2, 'triples'), 'weighted spike paths disagree')
    require(weighted == Energy(Fraction(149121, 625), Fraction(93121, 625)), 'weighted spike exact energies failed')
    require(weighted.ratio < Fraction(5, 8), 'weighted spike comparison failed')
    return dict(support=support, six_point=six, full_plane=full,
                weighted_spike_value=spike_weight, weighted_six_point=weighted,
                ordinary_spike_polynomial=tuple(ordinary_polynomial),
                respected_spike_polynomial=tuple(respected_polynomial),
                weighted_scope='One explicit upper-bound witness, not a weighted optimality claim')


def check_generic_two_row_spike():
    """Formal row constants and an order-two symbol; no target sampling.

    At a fixed source sum the coefficients of b,c are unique. Thus arbitrary
    relations involving b,c cannot merge different parity classes at that sum.
    The only remaining equality test uses a nonzero symbol delta with 2delta=0.
    """
    domain = points(2)
    support = tuple(i for i, (_, y) in enumerate(domain) if y in (0, 1))
    source = defaultdict(lambda: [0] * 3)
    target = defaultdict(lambda: [0] * 3)
    row_constants = defaultdict(set)
    for i, j in product(support, repeat=2):
        x, y = domain[i], domain[j]
        total = tuple((a + b) % 3 for a, b in zip(x, y))
        # Row y=0 has value c, with c+delta at index 0; row y=1 has b.
        b_coefficient = int(x[1] == 1) + int(y[1] == 1)
        c_coefficient = 2 - b_coefficient
        parity = (int(i == 0) + int(j == 0)) % 2
        degree = int(i == 0) + int(j == 0)
        row_constants[total].add((b_coefficient, c_coefficient))
        source[total][degree] += 1
        target[total, b_coefficient, c_coefficient, parity][degree] += 1
    require(len(source) == 9 and all(len(v) == 1 for v in row_constants.values()),
            'row-pair types interact at one source sum')
    def sum_squares(polynomials):
        result = [0] * 5
        for polynomial in polynomials:
            for i, first in enumerate(polynomial):
                for j, second in enumerate(polynomial):
                    result[i + j] += first * second
        return tuple(result)
    ordinary = sum_squares(source.values())
    respected = sum_squares(target.values())
    require(ordinary == (81, 56, 24, 0, 1), 'formal two-row ordinary polynomial failed')
    require(respected == (81, 0, 24, 0, 1), 'formal two-row respected polynomial failed')
    require(sum(ordinary) == 162 and sum(respected) == 106, 'formal two-row indicator count failed')
    return dict(source_sums=9, unique_row_constant_pair_at_each_source_sum=True,
                ordinary_polynomial=ordinary, respected_polynomial=respected,
                scope='Formal arbitrary row constants b,c and one nonzero order-two delta')


def check_spike_all_supports():
    """Independently verify formulas A-D and the complete analytic sharpness table."""
    domain = points(2)
    index = {x: i for i, x in enumerate(domain)}
    lines = tuple(_hyperplanes(2))
    through_origin = tuple(line for line in lines if line & 1)
    antipodal = {frozenset((i, index[tuple(-v % 3 for v in x)]))
                 for i, x in enumerate(domain) if i != 0}
    require(len(lines) == 12 and len(through_origin) == len(antipodal) == 4,
            'spike geometry counts failed')
    ordinary, respected = _indicator_arrays((1,) + (0,) * 8, 2)
    table = {n: Counter() for n in range(1, 10)}
    minimizing = []
    omitted_origin = containing_origin = complement_checks = 0
    for mask in range(1, 512):
        support = tuple(i for i in range(9) if mask & (1 << i))
        actual = indicator_energy(2, (1,) + (0,) * 8, support, 2)
        require(actual == Energy(ordinary[mask], respected[mask]), 'spike all-support energy paths disagree')
        require(81 * actual.respected >= 53 * actual.ordinary, 'spike indicator lower bound failed')
        if 81 * actual.respected == 53 * actual.ordinary:
            minimizing.append(mask)
        if not mask & 1:
            omitted_origin += 1
            require(actual.ratio == 1, 'support avoiding the spike has a loss')
            continue
        containing_origin += 1
        n = len(support)
        line_count = sum(mask & line == line for line in lines)
        origin_line_count = sum(mask & line == line for line in through_origin)
        pair_counts = Counter(tuple((a + b) % 3 for a, b in zip(domain[i], domain[j]))
                              for i, j in product(support, repeat=2))
        t_count = sum(pair_counts[domain[i]] - 2 for i in support if i != 0)
        formula_a = 2 * n * n - n + 8 * comb(n, 4) + (36 - 8 * n) * line_count
        formula_c = 2 * (comb(n - 1, 3) - (n - 5) * origin_line_count - line_count)
        require(actual.ordinary == formula_a, 'analytic spike formula A failed')
        require(actual.ordinary - actual.respected == 4 * t_count, 'analytic spike formula B failed')
        require(t_count == formula_c, 'analytic spike formula C failed')
        complement = 511 ^ mask
        c = 9 - n
        complement_lines = sum(complement & line == line for line in lines)
        complement_pairs = sum(all(complement & (1 << i) for i in pair) for pair in antipodal)
        require(line_count == 12 - 4 * c + comb(c, 2) - complement_lines,
                'analytic spike complement-line formula D failed')
        require(origin_line_count == 4 - c + complement_pairs,
                'analytic spike antipodal-pair formula D failed')
        complement_checks += 1
        if n >= 5:
            if c == 4:
                require(complement_lines in (0, 1), 'four-point complement line count failed')
            elif c == 3:
                require((complement_lines, complement_pairs) in ((1, 0), (0, 0), (0, 1)),
                        'three-point complement types failed')
            elif c == 2:
                require(complement_lines == 0 and complement_pairs in (0, 1), 'two-point complement types failed')
            else:
                require(complement_lines == complement_pairs == 0, 'small complement types failed')
        table[n][actual.ordinary, t_count] += 1
    expected = {
        1: {(1, 0)}, 2: {(6, 0)}, 3: {(15, 0), (27, 2)},
        4: {(36, 2), (40, 0), (40, 2)}, 5: {(77, 4), (81, 6)},
        6: {(150, 10), (150, 12), (162, 14)}, 7: {(271, 18), (271, 22)},
        8: {(456, 36)}, 9: {(729, 56)}}
    minima = (Fraction(1), Fraction(1), Fraction(19, 27), Fraction(7, 9),
              Fraction(19, 27), Fraction(53, 81), Fraction(183, 271),
              Fraction(13, 19), Fraction(505, 729))
    rows = []
    for n in range(1, 10):
        require(set(table[n]) == expected[n], 'analytic spike table entries failed')
        require(sum(table[n].values()) == comb(8, n - 1), 'analytic spike table support count failed')
        minimum = min(Fraction(ordinary - 4 * t_count, ordinary) for ordinary, t_count in table[n])
        require(minimum == minima[n - 1], 'analytic spike row minimum failed')
        rows.append(dict(support_size=n, cases=[dict(ordinary=ordinary, T=t_count, supports=count)
                         for (ordinary, t_count), count in sorted(table[n].items())], minimum=minimum))
    expected_minimizers = tuple(sorted(511 ^ line for line in lines if not line & 1))
    require(tuple(minimizing) == expected_minimizers and len(minimizing) == 8,
            'eight spike minimizing supports failed')
    require((omitted_origin, containing_origin, complement_checks) == (255, 256, 256),
            'spike support coverage failed')
    return dict(supports_checked=511, supports_omitting_spike=omitted_origin,
                supports_containing_spike=containing_origin,
                formula_A_checks=256, formula_B_checks=256, formula_C_checks=256,
                formula_D_checks=complement_checks, analytic_table=rows,
                minimum=Fraction(53, 81), minimizing_support_count=8,
                minimizing_support_masks=tuple(minimizing),
                equality_description='Complements of the eight affine lines avoiding the spike')


def check_improved_constants():
    eta = Fraction(13303, 21303)
    chain = (Fraction(5, 9), Fraction(49, 81), eta, Fraction(5, 8), Fraction(53, 81))
    require(all(a < b for a, b in zip(chain, chain[1:])), 'improved constant ordering failed')
    support = tuple(i for i, (_, y) in enumerate(points(2)) if y in (0, 1))
    weights = tuple(8 if i == 0 else 5 if i in support else 0 for i in range(9))
    actual = energy(2, (1,) + (0,) * 8, weights, 2)
    require(actual == Energy(149121, 93121) and actual.ratio == eta, 'integer spike witness failed')
    require(actual == energy(2, (1,) + (0,) * 8, weights, 2, 'triples'), 'integer spike witness paths disagree')
    polynomial = (-27, 0, 8, 0, 1)
    # t*N'(t)-N(t) = 3*(t^4+8*t^2-27), N=81+24*t^2+t^4.
    numerator = (81, 0, 24, 0, 1)
    stationary = tuple((i - 1) * coefficient for i, coefficient in enumerate(numerator))
    require(stationary == tuple(3 * coefficient for coefficient in polynomial), 'gamma stationary polynomial failed')
    require(_polynomial_value(polynomial, Fraction(3, 2)) < 0 < _polynomial_value(polynomial, Fraction(8, 5)),
            'gamma positive-root bracket failed')
    require((numerator[0] + 27 * numerator[4], numerator[2] - 8 * numerator[4]) == (108, 16),
            'gamma numerator reduction failed')
    require(Fraction(131, 20) ** 2 < 43 and _polynomial_value(polynomial, Fraction(8, 5)) > 0,
            'gamma elementary radical brackets failed')
    lower_numerator = 11 + 4 * Fraction(131, 20)
    require(lower_numerator / (lower_numerator + 14 * Fraction(8, 5)) == Fraction(93, 149),
            'gamma rational lower-bound substitution failed')
    require(Fraction(93, 149) > Fraction(49, 81), 'gamma low-histogram branch comparison failed')
    return dict(increasing_constants=chain, eta=eta, integer_weights=weights,
                integer_witness=actual, gamma_stationary_polynomial=polynomial,
                gamma_positive_root_bracket=(Fraction(3, 2), Fraction(8, 5)),
                numerator_reduced_modulo_stationary_polynomial=(108, 0, 16),
                gamma_rational_lower_bound=Fraction(93, 149),
                scope='Sharp indicator constant 53/81; gamma and eta are non-sharp weighted upper bounds')


def check_c2_maps():
    lines = set(_hyperplanes(2))
    cuts = lines | {511 ^ line for line in lines}
    require(len(lines) == 12 and len(cuts) == 24, 'plane line/cut count failed')
    ordinary_hist = [0] * 512
    records = Counter()
    for quadruple in _quadruples(2):
        support = _support_mask(quadruple)
        parity = 0
        for index in quadruple:
            parity ^= 1 << index
        ordinary_hist[support] += 1
        records[support, parity] += 1
    ordinary = _zeta(ordinary_hist)
    outside_minima = Counter()
    family_counts = Counter()
    maximum_full = maximum_minimum = Fraction(0)
    maximum_full_maps = []
    maximum_minimum_maps = []
    representatives = (0, 1, min(cuts), 7, 85, 511)
    representative_arrays = {}
    for coloring in range(512):
        histogram = [0] * 512
        for (support, parity), multiplicity in records.items():
            if (coloring & parity).bit_count() % 2 == 0:
                histogram[support] += multiplicity
        respected = _zeta(histogram)
        if coloring in representatives:
            representative_arrays[coloring] = respected
        values = tuple((coloring >> i) & 1 for i in range(9))
        require(energy(2, values, (1,) * 9, 2) == Energy(ordinary[511], respected[511]),
                'C2 full-plane parity and pair energies disagree')
        ratios = [Fraction(respected[support], ordinary[support]) for support in range(1, 512)]
        minimum = min(ratios)
        family = 'constant' if coloring in (0, 511) else 'cut' if coloring in cuts else 'outside'
        family_counts[family] += 1
        if family == 'outside':
            outside_minima[minimum] += 1
            full = ratios[-1]
            if full > maximum_full:
                maximum_full, maximum_full_maps = full, [coloring]
            elif full == maximum_full:
                maximum_full_maps.append(coloring)
            if minimum > maximum_minimum:
                maximum_minimum, maximum_minimum_maps = minimum, [coloring]
            elif minimum == maximum_minimum:
                maximum_minimum_maps.append(coloring)
        elif family == 'constant':
            require(minimum == 1, 'constant map indicator minimum failed')
        else:
            require(minimum == Fraction(13, 19), 'C2 cut indicator minimum failed')
    expected = {Fraction(53, 81): 18, Fraction(433, 729): 72, Fraction(139, 243): 144,
                Fraction(35, 57): 144, Fraction(11, 19): 108}
    require(dict(family_counts) == dict(constant=2, cut=24, outside=486), 'C2 classification counts failed')
    require(dict(outside_minima) == expected, 'C2 hereditary indicator distribution failed')
    require(maximum_full == Fraction(505, 729), 'C2 full-indicator maximum failed')
    require(maximum_minimum == Fraction(53, 81), 'C2 hereditary indicator maximum failed')
    # An independent pair-convolution path checks all supports for representatives.
    for coloring in representatives:
        values = tuple((coloring >> i) & 1 for i in range(9))
        baseline, lifted = _indicator_arrays(values, 2)
        require(baseline == ordinary, 'indicator denominators disagree')
        require(lifted == representative_arrays[coloring], 'C2 parity and target-arithmetic arrays disagree')
        for mask in range(1, 512):
            support = tuple(i for i in range(9) if mask & (1 << i))
            require(indicator_energy(2, values, support, 2) == Energy(ordinary[mask], lifted[mask]),
                    'subset-transform and pair energies disagree')
    return dict(maps=512, nonempty_supports_per_map=511, map_support_pairs=512 * 511,
                families=dict(family_counts), maximum_full_indicator_outside=maximum_full,
                maximum_hereditary_indicator_outside=maximum_minimum,
                outside_minimum_distribution=[dict(ratio=r, maps=outside_minima[r]) for r in sorted(outside_minima)],
                full_maximizing_maps=tuple(maximum_full_maps),
                hereditary_maximizing_maps=tuple(maximum_minimum_maps),
                independent_pair_crosschecks=len(representatives) * 511,
                all_map_full_plane_pair_crosschecks=512)


def check_integer_cut_indicators():
    values = tuple(y for _, y in points(2))
    ordinary, respected = _indicator_arrays(values)
    ratios = [Fraction(respected[mask], ordinary[mask]) for mask in range(1, 512)]
    minimum = min(ratios)
    attaining = tuple(mask for mask in range(1, 512) if ratios[mask - 1] == minimum)
    expected = tuple(sorted(511 ^ (1 << i) for i, (_, y) in enumerate(points(2)) if y == 1))
    require(minimum == Fraction(13, 19), 'integer cut indicator minimum failed')
    require(attaining == expected, 'integer cut minimizing supports failed')
    for mask in range(1, 512):
        support = tuple(i for i in range(9) if mask & (1 << i))
        require(indicator_energy(2, values, support) == Energy(ordinary[mask], respected[mask]),
                'integer cut pair and subset energies disagree')
    require(energy(2, values, (1,) * 9) == Energy(729, 513), 'full integer cut energy failed')
    return dict(target='Z', values=values, supports_checked=511,
                minimum=minimum, attaining_support_masks=attaining,
                attaining_support_count=len(attaining), attaining_energy=Energy(456, 312),
                full_plane=Energy(729, 513),
                scope='Indicator minimum only; this is not the weighted infimum')


def _allowed_plane_sections(plane, domain, index):
    members = [i for i in range(27) if plane & (1 << i)]
    lines = set()
    for i, j in combinations(members, 2):
        third = index[tuple((-a - b) % 3 for a, b in zip(domain[i], domain[j]))]
        line = (1 << i) | (1 << j) | (1 << third)
        require(line & plane == line and line.bit_count() == 3, 'affine line construction failed')
        lines.add(line)
    require(len(lines) == 12, 'plane line count failed')
    return frozenset({0, plane} | lines | {plane ^ line for line in lines})


def check_rank_three_sections():
    domain = points(3)
    index = {x: i for i, x in enumerate(domain)}
    planes = _hyperplanes(3)
    require(len(planes) == len(set(planes)) == 39, 'rank-three plane count failed')
    sections = {plane: _allowed_plane_sections(plane, domain, index) for plane in planes}
    require(all(len(allowed) == 26 for allowed in sections.values()), 'allowed section count failed')
    fixed = tuple(sum(1 << i for i, x in enumerate(domain) if x[0] == level) for level in range(3))
    full = (1 << 27) - 1
    require((fixed[0] | fixed[1] | fixed[2]) == full and sum(p.bit_count() for p in fixed) == 27,
            'fixed parallel planes do not partition the domain')
    valid = set()
    tested = 0
    for first, second, third in product(*(sorted(sections[plane]) for plane in fixed)):
        candidate = first | second | third
        tested += 1
        if all(candidate & plane in sections[plane] for plane in planes):
            valid.add(candidate)
    expected = {0, full} | set(planes) | {full ^ plane for plane in planes}
    require(tested == 17576 and valid == expected and len(valid) == 80, 'rank-three geometric diagnostic failed')
    sizes = Counter(mask.bit_count() for mask in valid)
    require(dict(sizes) == {0: 1, 9: 39, 18: 39, 27: 1}, 'rank-three valid set sizes failed')
    return dict(points=27, affine_planes=39, allowed_sections_per_plane=26,
                fixed_parallel_planes=3, candidate_subsets=tested, valid_subsets=len(valid),
                empty=1, full=1, hyperplanes=39, hyperplane_complements=39,
                scope='Exhaustive rank-three diagnostic, not an infinite-dimensional proof')


def cut_polynomials(modulus=None):
    _target_modulus(modulus)
    ordinary = [0] * 5
    respected = [0] * 5
    for quadruple in _quadruples(1):
        i, j, k, ell = quadruple
        degree = quadruple.count(1)
        ordinary[degree] += 1
        defect = i + j - k - ell
        if defect == 0 if modulus is None else defect % modulus == 0:
            respected[degree] += 1
    return tuple(ordinary), tuple(respected)


def _polynomial_value(coefficients, value):
    result = 0
    for coefficient in reversed(coefficients):
        result = result * value + coefficient
    return result


def check_cut_polynomials():
    rows = []
    for modulus in (None, 2, 4, 6, 9):
        ordinary, respected = cut_polynomials(modulus)
        require(ordinary == (6, 8, 12, 0, 1), 'ordinary cut polynomial failed')
        require(respected == (6, 0, 12, 0, 1), 'respected cut polynomial failed')
        for tau in (0, Fraction(2, 3), Fraction(7, 10), 1, 2):
            actual = energy(1, (0, 1, 2), (1, tau, 1), modulus)
            require(actual == Energy(_polynomial_value(ordinary, tau), _polynomial_value(respected, tau)),
                    'polynomial evaluation and pair energy disagree')
        rows.append(dict(target='Z' if modulus is None else 'C' + str(modulus),
                         ordinary=ordinary, respected=respected))
    ordinary, respected = cut_polynomials(3)
    require(ordinary == respected == (6, 8, 12, 0, 1), 'affine C3 control failed')
    minimal = (-2, 0, 4, 0, 1)
    require(_polynomial_value(minimal, Fraction(2, 3)) < 0 < _polynomial_value(minimal, Fraction(7, 10)),
            'positive minimizer root bracket failed')
    require(Fraction(49, 20) ** 2 > 6, 'square-root upper bound failed')
    require(_polynomial_value((8, -17, 8), Fraction(7, 10)) == Fraction(1, 50), 'rho comparison failed')
    require(Fraction(17, 25) - Fraction(53, 81) == Fraction(52, 2025), 'threshold difference failed')
    return dict(nonaffine_cases=rows, affine_C3=dict(ordinary=ordinary, respected=respected),
                positive_minimizer_polynomial=minimal, positive_root_bracket=(Fraction(2, 3), Fraction(7, 10)),
                threshold_difference=Fraction(52, 2025))


def jsonable(value):
    """Encode exact objects without floating-point conversion."""
    if type(value) is Fraction:
        return str(value)
    if type(value) is Energy:
        return dict(ordinary=jsonable(value.ordinary), respected=jsonable(value.respected), ratio=str(value.ratio))
    if type(value) is dict:
        if not all(type(key) is str for key in value):
            raise ValueError('JSON dictionaries require string keys')
        return {key: jsonable(item) for key, item in value.items()}
    if type(value) in (tuple, list):
        return [jsonable(item) for item in value]
    if value is None or type(value) in (str, int, bool):
        return value
    raise ValueError('unsupported exact JSON value')


def run_checks():
    return dict(report=292, schema_version=1, status='passed',
                scope='Bounded exact diagnostics only; the report supplies arbitrary-target and infinite-dimensional proofs',
                line_test=check_lines(), derivative_partitions=check_derivative_partitions(),
                spike=check_spike(), generic_two_row_spike=check_generic_two_row_spike(),
                spike_all_supports=check_spike_all_supports(), improved_constants=check_improved_constants(),
                c2_maps=check_c2_maps(),
                integer_cut_indicators=check_integer_cut_indicators(),
                rank_three_sections=check_rank_three_sections(), cut_polynomials=check_cut_polynomials())


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.parse_args(argv)
    print(json.dumps(jsonable(run_checks()), indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
