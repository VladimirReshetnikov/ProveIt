#!/usr/bin/env python3
"""Report290: bounded exact finite diagnostics, not a proof-assistant certificate."""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations, product
import json
from math import gcd
import sys

sys.dont_write_bytecode = True
MAX_SUPPORT = 128
MAX_FINITE_ORDER = 128
MAX_COORDINATE = 4096
MAX_WEIGHT_BITS = 128
MAX_DENOMINATOR_BITS = 64
MAX_EXHAUSTIVE_MAPS = 150000


def require(condition, message):
    """Checks remain active under python -O."""
    if not condition:
        raise RuntimeError(message)


def bounded_integer(value, name, low, high):
    if type(value) is not int or not low <= value <= high:
        raise ValueError(f'{name} must be an integer from {low} through {high}')
    return value


def _exact_nonnegative(value):
    if type(value) not in (int, Fraction):
        raise ValueError('weights must be exact integers or Fractions; no bools or floats')
    value = Fraction(value)
    if value < 0 or value.numerator.bit_length() > MAX_WEIGHT_BITS or value.denominator.bit_length() > MAX_DENOMINATOR_BITS:
        raise ValueError('weight is negative or exceeds the exact arithmetic limits')
    return value


@dataclass(frozen=True)
class Group:
    """One to four cyclic factors; modulus 0 denotes Z. Finite factors are canonical."""
    moduli: tuple

    def __post_init__(self):
        if type(self.moduli) is not tuple or not 1 <= len(self.moduli) <= 4:
            raise ValueError('moduli must be a tuple of one through four integers')
        size = 1
        for modulus in self.moduli:
            bounded_integer(modulus, 'modulus', 0, MAX_FINITE_ORDER)
            size *= max(1, modulus)
        if size > MAX_FINITE_ORDER:
            raise ValueError('product of finite factor orders exceeds 128')

    @property
    def zero(self):
        return (0,) * len(self.moduli)

    @property
    def finite(self):
        return 0 not in self.moduli

    def point(self, value):
        if type(value) is not tuple or len(value) != len(self.moduli):
            raise ValueError('points must be coordinate tuples of the exact group dimension')
        for coordinate, modulus in zip(value, self.moduli):
            bounded_integer(coordinate, 'coordinate', 0 if modulus else -MAX_COORDINATE,
                            modulus - 1 if modulus else MAX_COORDINATE)
        return value

    def _add(self, x, y):
        return tuple((a + b) % m if m else a + b for a, b, m in zip(x, y, self.moduli))

    def _neg(self, x):
        return tuple(-a % m if m else -a for a, m in zip(x, self.moduli))

    def _sub(self, x, y):
        return self._add(x, self._neg(y))

    def _scale(self, n, x):
        return tuple(n * a % m if m else n * a for a, m in zip(x, self.moduli))

    def add(self, x, y):
        return self._add(self.point(x), self.point(y))

    def sub(self, x, y):
        return self._sub(self.point(x), self.point(y))

    def scale(self, n, x):
        bounded_integer(n, 'multiplier', -MAX_COORDINATE, MAX_COORDINATE)
        return self._scale(n, self.point(x))

    def elements(self):
        if not self.finite:
            raise ValueError('enumerating an infinite group is unsupported')
        return tuple(product(*(range(m) for m in self.moduli)))


def _group(group):
    if type(group) is not Group:
        raise ValueError('a Group instance is required')
    return group


def _weights(domain, weights):
    _group(domain)
    if type(weights) is not dict or not 1 <= len(weights) <= MAX_SUPPORT:
        raise ValueError('weights must be a nonempty dictionary with at most 128 keys')
    result = {}
    for x, weight in weights.items():
        domain.point(x)
        value = _exact_nonnegative(weight)
        if value:
            result[x] = value
    if not result:
        raise ValueError('at least one weight must be positive')
    return result


def _images(domain, target, images, points):
    _group(domain)
    _group(target)
    if type(images) is not dict or len(images) != len(points) or set(images) != set(points):
        raise ValueError('image keys must be exactly the required support or full domain')
    for x, value in images.items():
        domain.point(x)
        target.point(value)
    return images


def _full_map(domain, target, images):
    points = _group(domain).elements()
    _images(domain, target, images, points)
    return points


@dataclass(frozen=True)
class Energy:
    ordinary: object
    respected: object

    def __post_init__(self):
        for value in (self.ordinary, self.respected):
            if type(value) not in (int, Fraction):
                raise ValueError('energies must be exact integers or Fractions')
        if self.ordinary <= 0 or not 0 <= self.respected <= self.ordinary:
            raise ValueError('energy requires 0 <= respected <= ordinary and ordinary > 0')

    @property
    def ratio(self):
        return Fraction(self.respected, self.ordinary)


def energy(domain, target, weights, images):
    """Pair-sum histograms give ordered energies, including repeated coordinates."""
    weights = _weights(domain, weights)
    _images(domain, target, images, weights)
    ordinary, respected = defaultdict(Fraction), defaultdict(Fraction)
    for x, wx in weights.items():
        for y, wy in weights.items():
            mass = wx * wy
            s = domain._add(x, y)
            ordinary[s] += mass
            respected[(s, target._add(images[x], images[y]))] += mass
    return Energy(sum(v * v for v in ordinary.values()), sum(v * v for v in respected.values()))


def direct_energy(domain, target, weights, images):
    """Independent literal four-loop oracle, limited to eight positive support points."""
    weights = _weights(domain, weights)
    if len(weights) > 8:
        raise ValueError('literal ordered-quadruple oracle has an eight-point limit')
    _images(domain, target, images, weights)
    ordinary = respected = Fraction(0)
    for x, y, z, t in product(weights, repeat=4):
        if domain._add(x, y) == domain._add(z, t):
            mass = weights[x] * weights[y] * weights[z] * weights[t]
            ordinary += mass
            if target._add(images[x], images[y]) == target._add(images[z], images[t]):
                respected += mass
    return Energy(ordinary, respected)


def indicator_minimum(domain, target, images):
    """All nonempty subsets of a full finite domain of order at most eight."""
    points = _full_map(domain, target, images)
    if len(points) > 8:
        raise ValueError('exhaustive indicator search has an eight-point domain limit')
    best, witness, count = Fraction(1), None, 0
    by_size = {}
    for size in range(1, len(points) + 1):
        size_best = Fraction(1)
        for subset in combinations(points, size):
            count += 1
            value = energy(domain, target, dict.fromkeys(subset, 1), {x: images[x] for x in subset}).ratio
            if witness is None or value < best:
                best, witness = value, subset
            size_best = min(size_best, value)
        by_size[size] = size_best
    return dict(ratio=best, witness=witness, subsets=count, minimum_by_size=by_size)


def derivative_masses(domain, target, images):
    """Q_h for every h, on a full finite domain; sum Q_h equals full energy."""
    points = _full_map(domain, target, images)
    return {h: sum(c * c for c in Counter(target._sub(images[domain._add(x, h)], images[x])
                                         for x in points).values()) for h in points}


def condition_p(domain, target, images):
    """Check all (x,h), returning the first failing pair or None."""
    points = _full_map(domain, target, images)
    for x in points:
        for h in points:
            values = [images[domain._add(x, domain._scale(j, h))] for j in range(4)]
            if target._add(values[3], values[0]) != target._add(values[2], values[1]):
                return dict(holds=False, witness=(x, h))
    return dict(holds=True, witness=None)


def classify_finite(domain, target, images):
    """Canonical translation subgroup, then independently verify the two-coset form.

    Returns affine, index_two, or other. For endpoint maps the returned K is also
    exactly the zero set of a(2x)-2a(x)+a(0); its complement has curvature -eta.
    This is a structural test, not a computation of an arbitrary map's infimum.
    """
    points = _full_map(domain, target, images)
    beta = images[domain.zero]
    b = {x: target._sub(images[x], beta) for x in points}
    kernel = tuple(h for h in points if all(target._sub(b[domain._add(x, h)], b[x]) == b[h]
                                          for x in points))
    require(domain.zero in kernel, 'translation subgroup contains zero')
    require(all(domain._add(x, y) in kernel for x, y in product(kernel, repeat=2)),
            'translation subgroup closure')
    require(all(b[domain._add(x, y)] == target._add(b[x], b[y]) for x, y in product(kernel, repeat=2)),
            'common kernel map is a homomorphism')
    result = dict(kind='other', kernel=kernel, beta=beta, homomorphism={x: b[x] for x in kernel})
    if len(kernel) == len(points):
        result['kind'] = 'affine'
    elif 2 * len(kernel) == len(points):
        t = next(x for x in points if x not in kernel)
        u = b[t]
        eta = target._sub(target._scale(2, u), b[domain._scale(2, t)])
        require(eta != target.zero, 'nonaffine index-two defect is nonzero')
        require(all(b[domain._add(t, k)] == target._add(u, b[k]) for k in kernel),
                'the other coset uses the same homomorphism')
        curvature = {x: target._sub(b[domain._scale(2, x)], target._scale(2, b[x])) for x in points}
        require(tuple(x for x in points if curvature[x] == target.zero) == kernel,
                'intrinsic curvature kernel')
        require(all(curvature[x] == target._neg(eta) for x in points if x not in kernel),
                'complement curvature is minus eta')
        result.update(kind='index_two', t=t, u=u, eta=eta, curvature=curvature)
    return result


def plane_data(target, values):
    """Four values indexed by 00,01,10,11; return (energy, doubled mass, k)."""
    _group(target)
    if type(values) is not tuple or len(values) != 4:
        raise ValueError('plane values must be a tuple of four target points')
    for value in values:
        target.point(value)
    d = sum(c * c for c in Counter(target._scale(2, v) for v in values).values())
    k = sum(target._add(values[0], values[j]) == target._add(values[p], values[q])
            for j, p, q in ((1, 2, 3), (2, 1, 3), (3, 1, 2)))
    return dict(respected=d + 24 + 8 * k, doubled_mass=d, partitions=k)


def affine_planes(domain):
    _group(domain)
    if any(m != 2 for m in domain.moduli):
        raise ValueError('affine-plane enumeration requires elementary-two factors')
    points = domain.elements()
    return tuple(sorted({tuple(sorted((x, domain._add(x, h), domain._add(x, k),
                                       domain._add(domain._add(x, h), k))))
                         for x in points for h in points if h != domain.zero
                         for k in points if k != domain.zero and k != h}))


def grid_obstruction(domain, target, images, h, k):
    _full_map(domain, target, images)
    domain.point(h)
    domain.point(k)
    two_h = domain._scale(2, h)
    return target._sub(target._sub(images[domain._add(two_h, k)], images[k]),
                       target._sub(images[two_h], images[domain.zero]))


def obstruction_average(q):
    if type(q) is not int or q not in (2, 4):
        raise ValueError('obstruction order must be two or four')
    return sum((Fraction(gcd(q, i, j), q) for i, j in product(range(q), repeat=2)), Fraction(0)) / (q * q)


def _tables(group):
    points = group.elements()
    index = {x: j for j, x in enumerate(points)}
    add = tuple(tuple(index[group._add(x, y)] for y in points) for x in points)
    sub = tuple(tuple(index[group._sub(x, y)] for y in points) for x in points)
    return points, add, sub


def _indexed_plane(values, add):
    d = sum(c * c for c in Counter(add[v][v] for v in values).values())
    k = sum(add[values[0]][values[j]] == add[values[p]][values[q]]
            for j, p, q in ((1, 2, 3), (2, 1, 3), (3, 1, 2)))
    return d + 24 + 8 * k, d, k


def _bounded_enumeration(order, target_size):
    bounded_integer(order, 'domain order', 1, 8)
    bounded_integer(target_size, 'target order', 1, 9)
    if target_size ** (order - 1) > MAX_EXHAUSTIVE_MAPS:
        raise ValueError('normalized map enumeration exceeds 150000 maps')
    return product(range(target_size), repeat=order - 1)


def box_energy(rank, torsion_order, n):
    """Exact energy for [-N,N]^rank times a finite group of the given order."""
    bounded_integer(rank, 'free rank', 0, 4)
    bounded_integer(torsion_order, 'torsion order', 1, 128)
    bounded_integer(n, 'box radius', 0, 32)
    m = 2 * n + 1
    return torsion_order ** 3 * ((2 * m ** 3 + m) // 3) ** rank


def box_quotient_counts(n):
    """Literal Z x C4 box counts for quotient C2 x C2 and b(p,q)=pq.

    Radii 0..8 are supported. Includes all 64 additive quotient patterns even
    when some have no lifts (N=0); finite observations do not prove a limit.
    """
    bounded_integer(n, 'box radius', 0, 8)
    points = tuple(product(range(-n, n + 1), range(4)))
    quotient = tuple(product(range(2), repeat=2))
    patterns = {(*first, ((first[0][0] + first[1][0] - first[2][0]) % 2,
                         (first[0][1] + first[1][1] - first[2][1]) % 2)): 0
                for first in product(quotient, repeat=3)}
    ordinary = respected = 0
    for x, y, z in product(points, repeat=3):
        t = (x[0] + y[0] - z[0], (x[1] + y[1] - z[1]) % 4)
        if not -n <= t[0] <= n:
            continue
        ordinary += 1
        respected += (x[0] * x[1] + y[0] * y[1] - z[0] * z[1] - t[0] * t[1]) % 2 == 0
        pattern = tuple((p[0] % 2, p[1] % 2) for p in (x, y, z, t))
        patterns[pattern] += 1
    require(ordinary == box_energy(1, 4, n), 'exact box ordinary energy')
    require(sum(patterns.values()) == ordinary, 'box quotient patterns partition quadruples')
    differences = Counter()
    for pattern, count in patterns.items():
        differences[((pattern[0][0] - pattern[2][0]) % 2,
                     (pattern[0][1] - pattern[2][1]) % 2)] += count
    return dict(N=n, size=len(points), energy=Energy(ordinary, respected), patterns=patterns,
                difference_counts=dict(differences),
                relative_pattern_spread=Fraction(max(patterns.values()) - min(patterns.values()), ordinary))


def check_energy_oracles():
    cases = 0
    for domain, points in ((Group((0,)), ((-1,), (0,), (1,), (3,))),
                           (Group((4,)), ((0,), (1,), (2,), (3,))),
                           (Group((2, 2)), tuple(product(range(2), repeat=2)))):
        for target in (Group((0,)), Group((3,)), Group((2, 2))):
            for offset in range(3):
                weights = {x: Fraction(j + 1, j + offset + 2) for j, x in enumerate(points)}
                images = {x: ((j * j - offset,) if not target.finite else
                               target.elements()[(j * j + offset) % len(target.elements())])
                          for j, x in enumerate(points)}
                require(energy(domain, target, weights, images) == direct_energy(domain, target, weights, images),
                        'pair histogram versus literal ordered quadruples')
                cases += 1
    return dict(weighted_cases=cases, maximum_support=4)


def check_cyclic():
    rows, total, classification_count = [], 0, 0
    bounds = {3: Fraction(19, 27), 4: Fraction(11, 16), 5: Fraction(17, 25), 6: Fraction(19, 27)}
    for n in range(1, 7):
        count = failing = affine = index_two = 0
        maximum, witness = Fraction(0), None
        for modulus in range(2, 10):
            domain, target = Group((n,)), Group((modulus,))
            for tail in _bounded_enumeration(n, modulus):
                a = (0,) + tail
                count += 1
                increments = tuple((a[(x + 1) % n] - a[x]) % modulus for x in range(n))
                p = all(increments[(x + 2) % n] == increments[x] for x in range(n))
                if p:
                    result = classify_finite(domain, target, {(j,): (a[j],) for j in range(n)})
                    classification_count += 1
                    require(result['kind'] in ('affine', 'index_two'), 'cyclic P structural classification')
                    affine += result['kind'] == 'affine'
                    index_two += result['kind'] == 'index_two'
                    continue
                failing += 1
                q = [sum(c * c for c in Counter((a[(x + h) % n] - a[x]) % modulus
                                                for x in range(n)).values()) for h in range(n)]
                ratio = Fraction(sum(q), n ** 3)
                require(ratio <= bounds[n], 'small cyclic bound outside P')
                if n == 5:
                    require(q[1] <= 17 and q[2] <= 17, 'C5 derivative bound')
                    require(q[1] != 17 or q[2] == 13, 'C5 Q1=17 implies Q2=13')
                    require(q[2] != 17 or q[1] == 13, 'C5 Q2=17 implies Q1=13')
                if ratio > maximum:
                    maximum, witness = ratio, dict(target_modulus=modulus, values=a)
        total += count
        rows.append(dict(order=n, normalized_maps=count, failing_P=failing, affine=affine,
                         index_two=index_two, largest_full_ratio_outside_P=maximum if failing else None,
                         maximizer=witness))
    require(total == 138516, 'declared cyclic enumeration count')
    return dict(normalized_maps_total=total, canonical_classifications=classification_count,
                domain_orders=[1, 6], target_moduli=[2, 9], rows=rows)


def check_planes_and_gluing():
    plane_rows, gluing_rows = [], []
    domain = Group((2, 2))
    points = domain.elements()
    for factors in [(m,) for m in range(2, 9)] + [(2, 2), (2, 4)]:
        target = Group(factors)
        images, add, _ = _tables(target)
        count = 0
        histogram = Counter()
        for tail in _bounded_enumeration(4, len(images)):
            a = (0,) + tail
            e, d, k = _indexed_plane(a, add)
            direct = sum(add[a[x]][a[y]] == add[a[z]][a[x ^ y ^ z]] for x, y, z in product(range(4), repeat=3))
            require(e == direct, 'plane formula versus all 64 additive quadruples')
            require((k == 3 and e == 64) or (k == 2 and e == 48) or (k <= 1 and e <= 40), 'plane trichotomy')
            if e in (48, 64):
                classified = classify_finite(domain, target, dict(zip(points, (images[v] for v in a))))
                require(classified['kind'] == ('affine' if e == 64 else 'index_two'), 'plane structure agrees with energy')
            histogram[e] += 1
            count += 1
        plane_rows.append(dict(target=factors, normalized_maps=count, energy_histogram=dict(sorted(histogram.items()))))
    domain = Group((2, 2, 2))
    points = domain.elements()
    point_index = {x: j for j, x in enumerate(points)}
    planes = tuple(tuple(point_index[x] for x in plane) for plane in affine_planes(domain))
    require(len(planes) == 14, 'F2^3 affine plane count')
    for factors in [(2,), (3,), (4,), (2, 2)]:
        target = Group(factors)
        images, add, _ = _tables(target)
        count = affine = index_two = bad = 0
        for tail in _bounded_enumeration(8, len(images)):
            a = (0,) + tail
            count += 1
            if any(_indexed_plane(tuple(a[x] for x in plane), add)[0] <= 40 for plane in planes):
                bad += 1
                continue
            result = classify_finite(domain, target, dict(zip(points, (images[v] for v in a))))
            require(result['kind'] in ('affine', 'index_two'), 'global elementary-two gluing')
            affine += result['kind'] == 'affine'
            index_two += result['kind'] == 'index_two'
        gluing_rows.append(dict(target=factors, normalized_maps=count, affine=affine,
                                index_two=index_two, bad_plane=bad))
    require(sum(row['normalized_maps'] for row in plane_rows) == 1871, 'declared plane map count')
    require(sum(row['normalized_maps'] for row in gluing_rows) == 35083, 'declared global gluing count')
    return dict(plane_normalized_maps=1871, plane_rows=plane_rows,
                gluing_normalized_maps=35083, affine_planes_per_map=14, gluing_rows=gluing_rows)


def check_mixed_classification():
    """Full maps on C2 x C3, with target C2, C3, or C4; generic API only."""
    domain = Group((2, 3))
    points = domain.elements()
    rows = []
    for modulus in (2, 3, 4):
        target = Group((modulus,))
        counts = Counter()
        for tail in _bounded_enumeration(6, modulus):
            a = (0,) + tail
            mapping = dict(zip(points, ((v,) for v in a)))
            result = classify_finite(domain, target, mapping)
            counts[result['kind']] += 1
            masses = derivative_masses(domain, target, mapping)
            ratio = Fraction(sum(masses.values()), 6 ** 3)
            if result['kind'] in ('affine', 'index_two'):
                require(ratio == (1 if result['kind'] == 'affine' else Fraction(3, 4)), 'full finite endpoint ratio')
            else:
                require(ratio <= Fraction(19, 27), 'mixed finite full-indicator gap')
            require(condition_p(domain, target, mapping)['holds'] == (result['kind'] != 'other'),
                    'P classification for the cyclic group in mixed coordinates')
        rows.append(dict(target_modulus=modulus, normalized_maps=sum(counts.values()), classes=dict(counts)))
    return dict(domain=(2, 3), normalized_maps_total=sum(row['normalized_maps'] for row in rows), rows=rows)


def check_order_four_obstruction():
    domain, target = Group((8, 8)), Group((4,))
    points = domain.elements()
    images = {}
    for i, j in points:
        m, epsilon = divmod(i, 2)
        n, delta = divmod(j, 2)
        images[(i, j)] = ((m * delta - n * epsilon + 2 * m * n) % 4,)
    require(condition_p(domain, target, images)['holds'], 'all 4096 P equations in the order-four model')
    s = grid_obstruction(domain, target, images, (1, 0), (0, 1))
    require(s == (1,), 'genuine order-four obstruction')
    require(classify_finite(domain, target, images)['kind'] == 'other', 'order-four model is outside both families')
    masses = derivative_masses(domain, target, images)
    classes = Counter()
    for h, mass in masses.items():
        classes[(h[0] % 4, h[1] % 4)] += mass
    full = energy(domain, target, dict.fromkeys(points, 1), images)
    require(full.respected == sum(masses.values()) and full.ordinary == 64 ** 3, 'model derivative and pair-sum energies')
    for (i, j), respected in classes.items():
        d = 4 // gcd(4, i, j)
        require(respected <= full.ordinary // (16 * d), 'order-four difference class bound')
    require(full.ratio == Fraction(35, 128), 'order-four model full ratio')
    require(obstruction_average(2) == Fraction(5, 8) and obstruction_average(4) == Fraction(11, 32), 'grid reciprocal averages')
    return dict(domain=(8, 8), target=(4,), P_equations=4096, s=s, energy=full,
                reciprocal_averages={'2': obstruction_average(2), '4': obstruction_average(4)},
                respected_difference_classes=dict(sorted(classes.items())))


def check_c5_integer_example():
    domain, target = Group((5,)), Group((0,))
    images = {(j,): (j,) for j in range(5)}
    result = indicator_minimum(domain, target, images)
    masses = derivative_masses(domain, target, images)
    require(result['subsets'] == 31 and result['ratio'] == Fraction(17, 25), 'C5 integer example indicator minimum')
    require((masses[(1,)], masses[(2,)]) == (17, 13), 'C5 integer example derivative masses')
    require(result['minimum_by_size'] == {1: Fraction(1), 2: Fraction(1), 3: Fraction(15, 19),
                                           4: Fraction(9, 13), 5: Fraction(17, 25)}, 'C5 subset-size minima')
    result['derivative_masses'] = masses
    result['weighted_infimum_claimed'] = False
    return result


def check_box_lifting():
    expected = {1: Fraction(13, 19), 2: Fraction(11, 17), 4: Fraction(103, 163), 8: Fraction(121, 193)}
    rows = []
    for n, ratio in expected.items():
        row = box_quotient_counts(n)
        require(row['energy'].ratio == ratio, 'box quotient-function ratio')
        require(len(row['patterns']) == 64 and min(row['patterns'].values()) > 0, 'all 64 quotient patterns have lifts')
        rows.append(dict(N=n, size=row['size'], energy=row['energy'], quotient_patterns=64,
                         smallest_pattern_lifts=min(row['patterns'].values()),
                         largest_pattern_lifts=max(row['patterns'].values()),
                         relative_pattern_spread=row['relative_pattern_spread'],
                         difference_counts=row['difference_counts']))
    return dict(domain='Z x C4', quotient='C2 x C2', quotient_function='b(p,q)=pq in C2',
                limiting_ratio_proved_in_paper=Fraction(5, 8), rows=rows)


# The eight exhaustive extension branches in the arbitrary-target proof.
BRANCH_ROWS = (
    ((0, 0, 0, 1, 2), tuple(range(5))),
    ((0, 0, 0, 1, 1, 2), tuple(range(6))),
    ((0, 0, 0, 1, 1, 1, 1, 1), (1, 2, 3, 4, 5, 7)),
    ((0, 0, 0, 1, 1, 1, 1, 2), tuple(range(2, 8))),
    ((0, 0, 0, 1, 1, 1, 2, 1), tuple(range(8))),
    ((0, 0, 0, 1, 1, 1, 2, 2, 3), tuple(range(9))),
    ((0, 0, 0, 1, 1, 1, 2, 2, 2, 2), (2, 3, 4, 5, 6, 7, 9)),
    ((0, 0, 0, 1, 1, 1, 2, 2, 2, 3), tuple(range(10))),
)
NO_WRAP_SIGNED = ((53, 14, 2), (98, 24, 0), (90, 20, 0), (98, 24, 0),
                  (204, 64, 6), (321, 84, 0), (139, 36, 0), (470, 100, 0))
NO_WRAP_MAXIMA = ('57/85', '49/73', '9/13', '49/73', '27/43', '107/163', '139/211', '47/67')
WRAP_MAXIMA = tuple(tuple(Fraction(x) for x in row.split()) for row in (
    '57/85 57/85 57/85 57/85 57/85 57/85 57/85 57/85 57/85',
    '25/37 49/73 49/73 49/73 49/73 49/73 49/73 49/73 49/73',
    '24/35 47/67 23/33 9/13 9/13 9/13 9/13 9/13 9/13',
    '25/37 49/73 49/73 49/73 49/73 49/73 49/73 49/73 49/73',
    '43/69 59/96 57/91 5/8 109/173 27/43 27/43 27/43 27/43',
    '413/657 389/601 359/559 15/23 333/509 325/497 323/491 107/163 107/163',
    '159/247 151/231 145/221 143/215 47/71 139/211 139/211 139/211 139/211',
    '67/100 23/35 293/419 269/391 253/370 249/355 241/345 79/113 59/84'))
# Each entry is (row, N, ((exponent, positive-wrap coefficient), ...)).
POSITIVE_WRAP_POLYNOMIALS = (
    (2, 10, ((4, 1),)),
    (3, 10, ((1, 2), (2, 3))), (3, 11, ((2, 2),)), (3, 12, ((2, 1),)),
    (4, 10, ((4, 1),)),
    (5, 10, ((1, 4), (2, 18), (3, 10), (4, 3))),
    (5, 11, ((1, 2), (2, 8), (3, 8), (4, 2))),
    (5, 12, ((2, 5), (3, 4), (4, 1))), (5, 13, ((2, 2), (3, 2))), (5, 14, ((2, 1),)),
    (6, 10, ((2, 1), (3, 32), (4, 45), (5, 6))),
    (6, 11, ((3, 10), (4, 34), (5, 12))),
    (6, 12, ((3, 2), (4, 18), (5, 14), (6, 1))),
    (6, 13, ((4, 6), (5, 12), (6, 2))), (6, 14, ((4, 1), (5, 6), (6, 3))),
    (6, 15, ((5, 2), (6, 2))), (6, 16, ((6, 1),)),
    (7, 10, ((2, 7), (3, 10), (4, 1))), (7, 11, ((2, 2), (3, 6), (4, 2))),
    (7, 12, ((2, 1), (3, 2), (4, 2))), (7, 13, ((3, 2),)), (7, 14, ((4, 1),)),
    (8, 10, ((2, 10), (3, 100), (4, 55))),
    (8, 11, ((3, 52), (4, 64), (5, 4))),
    (8, 12, ((3, 16), (4, 58), (5, 10))),
    (8, 13, ((3, 4), (4, 34), (5, 18))),
    (8, 14, ((4, 16), (5, 18), (6, 1))), (8, 15, ((4, 4), (5, 14), (6, 2))),
    (8, 16, ((4, 1), (5, 6), (6, 3))), (8, 17, ((5, 2), (6, 2))), (8, 18, ((6, 1),)),
)


def branch_data(row):
    bounded_integer(row, 'branch row', 1, 8)
    return BRANCH_ROWS[row - 1]


def _coefficient_inputs(coefficients, subset, modulus):
    if type(coefficients) is not tuple or not 1 <= len(coefficients) <= 10:
        raise ValueError('coefficient vectors are tuples of one through ten integers')
    for value in coefficients:
        bounded_integer(value, 'coefficient', 0, 3)
    if type(subset) is not tuple or not 1 <= len(subset) <= 10:
        raise ValueError('test subsets are nonempty tuples of at most ten indices')
    for index in subset:
        bounded_integer(index, 'test index', 0, len(coefficients) - 1)
    if tuple(sorted(set(subset))) != subset:
        raise ValueError('test indices must be distinct and in increasing order')
    if modulus is not None:
        bounded_integer(modulus, 'cyclic certificate modulus', 10, 18)
    return coefficients, subset, modulus


def coefficient_histogram(coefficients, subset, modulus=None, method='pairs'):
    """Signed C(z,t); None denotes integer sums, finite moduli are 10..18.

    The pairs and quadruples methods are separately implemented count oracles.
    Finite wrapping retains the slope contribution: target defect is z*v+t*u,
    with v=N*d, not merely t*u. Every input is checked before counting.
    """
    c, subset, modulus = _coefficient_inputs(coefficients, subset, modulus)
    if type(method) is not str or method not in ('pairs', 'quadruples'):
        raise ValueError('counting method must be pairs or quadruples')
    histogram = Counter()
    if method == 'pairs':
        pairs = Counter((i + j, c[i] + c[j]) for i in subset for j in subset)
        for (s, r), multiplicity in pairs.items():
            for (other_s, other_r), other_multiplicity in pairs.items():
                delta = s - other_s
                if (delta == 0 if modulus is None else delta % modulus == 0):
                    z = 0 if modulus is None else delta // modulus
                    histogram[(z, r - other_r)] += multiplicity * other_multiplicity
    else:
        for i, j, k, l in product(subset, repeat=4):
            delta = i + j - k - l
            if (delta == 0 if modulus is None else delta % modulus == 0):
                z = 0 if modulus is None else delta // modulus
                histogram[(z, c[i] + c[j] - c[k] - c[l])] += 1
    return dict(sorted(histogram.items()))


def _defect_histogram(histogram):
    if type(histogram) is not dict or not 1 <= len(histogram) <= 39:
        raise ValueError('a nonempty defect dictionary with at most 39 entries is required')
    for key, count in histogram.items():
        if type(key) is not tuple or len(key) != 2:
            raise ValueError('defect keys are (wrap, coefficient) tuples')
        bounded_integer(key[0], 'wrap index', -1, 1)
        bounded_integer(key[1], 'defect coefficient', -6, 6)
        bounded_integer(count, 'defect count', 1, 10000)
    if sum(histogram.values()) > 10000 or (0, 0) not in histogram:
        raise ValueError('defect total exceeds 10000 or the diagonal is missing')
    if any(histogram.get((-z, -t)) != count for (z, t), count in histogram.items()):
        raise ValueError('defect counts must have (z,t) <-> (-z,-t) symmetry')
    return histogram


def symbolic_numerator(histogram, q, h):
    """Count t+z*h=0 mod q, or equality if q=None; u is always nonzero."""
    _defect_histogram(histogram)
    if q is not None:
        bounded_integer(q, 'order of u', 2, 4096)
    m = max(abs(t) for z, t in histogram)
    bounded_integer(h, 'slope coefficient', -m, m)
    return sum(count for (z, t), count in histogram.items()
               if (t + z * h == 0 if q is None else (t + z * h) % q == 0))


def symbolic_maximum(histogram):
    """Exhaustive q=2..2M plus infinity and h=-M..M symbolic reduction."""
    _defect_histogram(histogram)
    m = max(abs(t) for z, t in histogram)
    best, maximizer, patterns = -1, None, 0
    for q in (*range(2, 2 * m + 1), None):
        for h in range(-m, m + 1):
            numerator = symbolic_numerator(histogram, q, h)
            patterns += 1
            if numerator > best:
                best, maximizer = numerator, dict(order_u=q, h=h)
    # A v outside <u> contributes no nonzero-wrap terms. Check every zero-wrap
    # torsion pattern separately rather than relying on an unstated h choice.
    for q in (*range(2, 2 * m + 1), None):
        zero_wrap = sum(count for (z, t), count in histogram.items()
                        if z == 0 and (t == 0 if q is None else t % q == 0))
        require(zero_wrap <= best, 'v outside the subgroup generated by u is covered')
    return dict(energy=Energy(sum(histogram.values()), best), M=m,
                symbolic_patterns=patterns, maximizer=maximizer)


def three_case_maximum(histogram):
    """Algebraic primary certificate: orders 2, 3, and >=4/infinite.

    Requires zero-wrap defects at most two and positive-wrap support diameter
    at most three. These are checked hypotheses, not assumptions about H.
    """
    _defect_histogram(histogram)
    zero = {t: count for (z, t), count in histogram.items() if z == 0}
    positive = {t: count for (z, t), count in histogram.items() if z == 1}
    if any(abs(t) > 2 for t in zero):
        raise ValueError('three-case certificate requires zero-wrap defects at most two')
    if positive and max(positive) - min(positive) > 3:
        raise ValueError('positive-wrap support diameter exceeds three')
    residue_maxima = []
    for q in (2, 3):
        residues = Counter()
        for t, count in positive.items():
            residues[t % q] += count
        residue_maxima.append(max(residues.values(), default=0))
    residue_maxima.append(max(positive.values(), default=0))
    d0, d2 = zero.get(0, 0), zero.get(2, 0)
    numerators = (d0 + 2 * d2 + 2 * residue_maxima[0],
                  d0 + 2 * residue_maxima[1], d0 + 2 * residue_maxima[2])
    return dict(energy=Energy(sum(histogram.values()), max(numerators)),
                positive_wrap=positive, zero_wrap=zero,
                wrap_class_maxima=tuple(residue_maxima), three_numerators=numerators)


def realized_pair_energy(coefficients, subset, modulus, q, h):
    """Independent realization in C_(Nq), or Z if q=None.

    Use u=N,d=h so N*d=h*u. This retains the slope and realizes every formal
    q/h pattern. For the no-wrap case use domain Z and target c_i modulo q.
    """
    c, subset, modulus = _coefficient_inputs(coefficients, subset, modulus)
    if q is not None:
        bounded_integer(q, 'order of u', 2, 4096)
    bounded_integer(h, 'slope coefficient', -6, 6)
    ordinary, respected = Counter(), Counter()
    for i in subset:
        for j in subset:
            s = i + j
            domain_sum = s if modulus is None else s % modulus
            value = c[i] + c[j] if modulus is None else h * s + modulus * (c[i] + c[j])
            target_modulus = q if modulus is None else (modulus * q if q is not None else None)
            if target_modulus is not None:
                value %= target_modulus
            ordinary[domain_sum] += 1
            respected[(domain_sum, value)] += 1
    return Energy(sum(count * count for count in ordinary.values()),
                  sum(count * count for count in respected.values()))


def branch_certificate(row, modulus=None):
    c, subset = branch_data(row)
    histogram = coefficient_histogram(c, subset, modulus)
    require(histogram == coefficient_histogram(c, subset, modulus, 'quadruples'),
            'independent pair-sum and literal quadruple defect histograms')
    primary = three_case_maximum(histogram)
    general = symbolic_maximum(histogram)
    require(primary['energy'] == general['energy'], 'three-case and general q/h maxima agree')
    q, h = general['maximizer']['order_u'], general['maximizer']['h']
    require(realized_pair_energy(c, subset, modulus, q, h) == general['energy'],
            'an independent target realization attains the symbolic maximum')
    expected_d = NO_WRAP_SIGNED[row - 1]
    require(primary['zero_wrap'] == {t: expected_d[abs(t)] for t in range(-2, 3) if expected_d[abs(t)]},
            'listed signed no-wrap histogram')
    expected_p = {(r, n): dict(polynomial) for r, n, polynomial in POSITIVE_WRAP_POLYNOMIALS}
    require(primary['positive_wrap'] == expected_p.get((row, modulus), {}), 'listed positive-wrap polynomial')
    expected = Fraction(NO_WRAP_MAXIMA[row - 1]) if modulus is None else WRAP_MAXIMA[row - 1][modulus - 10]
    require(primary['energy'].ratio == expected, 'listed exact branch maximum')
    require(expected < Fraction(19, 27), 'strict branch indicator bound')
    return dict(row=row, modulus=modulus, coefficients=c, subset=subset, histogram=histogram,
                **primary, general_reduction=general)


def check_symbolic_certificates():
    rows = []
    for row in range(1, 9):
        nowrap = branch_certificate(row)
        cyclic = [branch_certificate(row, n) for n in range(10, 19)]
        rows.append(dict(row=row, no_wrap=nowrap, cyclic=cyclic))
    require(len(POSITIVE_WRAP_POLYNOMIALS) == 31, '31 nonzero positive-wrap polynomials')
    require(max(case['energy'].ratio for row in rows for case in row['cyclic']) == Fraction(59, 84),
            'largest finite-wrap branch ratio')
    require(max(row['no_wrap']['energy'].ratio for row in rows) == Fraction(47, 67),
            'largest no-wrap branch ratio')
    return dict(no_wrap_cases=8, finite_wrap_cases=72, nonzero_positive_wrap_polynomials=31,
                certificate_scope='Exhaustive arbitrary-target symbolic certificate for these eight branches; not finite-target map sampling',
                slope='v=N*d is retained; target defect is z*v+t*u with u nonzero',
                primary_reduction='ord(u)=2, ord(u)=3, or ord(u)>=4/infinite; positive-wrap diameter<=3',
                general_reduction='h=-M..M; q=2..2M or infinity; q>2M has the same zero tests as infinity',
                largest_no_wrap_ratio=Fraction(47, 67), largest_finite_wrap_ratio=Fraction(59, 84), rows=rows)


def check_c3_sharp_indicator():
    domain, target = Group((3,)), Group((0,))
    images = {(j,): (j,) for j in range(3)}
    result = indicator_minimum(domain, target, images)
    ratios = []
    for mask in range(1, 8):
        subset = tuple((j,) for j in range(3) if mask & (1 << j))
        measured = energy(domain, target, dict.fromkeys(subset, 1), {x: images[x] for x in subset})
        require(measured == direct_energy(domain, target, dict.fromkeys(subset, 1), {x: images[x] for x in subset}),
                'C3 sharpness subset direct ordered energy')
        require(measured.ratio == (Fraction(19, 27) if mask == 7 else Fraction(1)), 'C3 all seven sharpness subsets')
        ratios.append(dict(mask=mask, energy=measured))
    require(result['ratio'] == Fraction(19, 27) and result['subsets'] == 7, 'sharp universal indicator example')
    # An exact rational weight already disproves using this example as a
    # weighted sharpness certificate; irrational optimization is unnecessary.
    weighted = energy(domain, target, {(0,): 1, (1,): Fraction(2, 3), (2,): 1}, images)
    require(weighted.ratio < Fraction(19, 27), 'weighted sharpness is not inferred')
    return dict(indicator=result, subsets=ratios, weighted_test=weighted,
                weighted_test_weights=(1, Fraction(2, 3), 1), weighted_sharpness_claimed=False)


def check_small_order_arithmetic():
    """Exact integer arithmetic in Appendix A; algebraic histogram hypotheses are proved in the paper."""
    rows = []
    for n, bound, numerators in ((7, Fraction(33, 49), (223, 231)),
                                (8, Fraction(11, 16), (344, 336, 352)),
                                (9, Fraction(19, 27), (505, 513))):
        cut_ratio = Fraction(2 * n * n + 1, 3 * n * n)
        require(cut_ratio <= bound, 'arithmetic-cut case in small cyclic orders')
        require(all(Fraction(value, n ** 3) <= bound for value in numerators), 'small-order case arithmetic')
        rows.append(dict(order=n, full_indicator_bound=bound, arithmetic_cut_ratio=cut_ratio,
                         case_numerators=numerators, ordinary=n ** 3))
    return dict(scope='Arithmetic checks for the paper-proved arbitrary-target histogram cases, not a finite search proof', rows=rows)


def jsonable(value):
    if type(value) is Fraction:
        return str(value)
    if type(value) is Energy:
        return dict(ordinary=jsonable(value.ordinary), respected=jsonable(value.respected), ratio=str(value.ratio))
    if type(value) is dict:
        if not all(type(key) is str for key in value):
            return [dict(key=jsonable(key), value=jsonable(v)) for key, v in sorted(value.items())]
        return {key: jsonable(v) for key, v in value.items()}
    if type(value) in (tuple, list):
        return [jsonable(v) for v in value]
    if value is None or type(value) in (str, int, bool):
        return value
    raise ValueError('unsupported JSON value')


def run_checks():
    return dict(report=290, schema_version=2, status='passed',
                arithmetic='exact integers and Fractions; no floating point',
                scope='Exact symbolic branch certificates cover arbitrary targets by proved finite reductions; remaining finite diagnostics do not establish the general theorem or weighted sharpness',
                energy_oracles=check_energy_oracles(), cyclic=check_cyclic(),
                elementary_two=check_planes_and_gluing(), mixed_classification=check_mixed_classification(),
                order_four_obstruction=check_order_four_obstruction(),
                C5_integer_example=check_c5_integer_example(), box_lifting=check_box_lifting(),
                symbolic_certificates=check_symbolic_certificates(), C3_sharp_indicator=check_c3_sharp_indicator(),
                small_order_arithmetic=check_small_order_arithmetic())


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.parse_args(argv)
    print(json.dumps(jsonable(run_checks()), indent=2, sort_keys=True))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
