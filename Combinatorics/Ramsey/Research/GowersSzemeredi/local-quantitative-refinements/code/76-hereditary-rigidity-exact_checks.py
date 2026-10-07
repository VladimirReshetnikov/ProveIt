#!/usr/bin/env python3
"""Bounded, exact, offline diagnostics for Report288; no universal enumeration claim."""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from itertools import product, combinations
import json
from math import comb, isqrt

MAX_SUPPORT = 128
MAX_COORDINATE = 4096
MAX_WEIGHT_BITS = 256
MAX_DENOMINATOR_BITS = 128
MAX_PARAMETER = 32


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def bounded_integer(value, name, low=1, high=MAX_PARAMETER):
    if type(value) is not int or not low <= value <= high:
        raise ValueError(f'{name} must be an integer from {low} through {high}')
    return value


@dataclass(frozen=True)
class Group:
    """A product of at most three cyclic factors; modulus zero denotes Z."""
    moduli: tuple

    def __post_init__(self):
        if type(self.moduli) is not tuple or not 1 <= len(self.moduli) <= 3:
            raise ValueError('moduli must be a tuple with one through three entries')
        size = 1
        for modulus in self.moduli:
            bounded_integer(modulus, 'modulus', 0, 128)
            size *= max(modulus, 1)
        if size > 128:
            raise ValueError('product of finite factor sizes exceeds 128')

    @property
    def zero(self):
        return (0,) * len(self.moduli)

    def point(self, value):
        if type(value) is not tuple or len(value) != len(self.moduli):
            raise ValueError('group element must be a coordinate tuple of the right length')
        for x, modulus in zip(value, self.moduli):
            if type(x) is not int or abs(x) > MAX_COORDINATE:
                raise ValueError('integer coordinate outside the supported range')
            if modulus and not 0 <= x < modulus:
                raise ValueError('finite coordinates must be canonical residues')
        return value

    def add(self, x, y):
        self.point(x); self.point(y)
        return self._add(x, y)

    def _add(self, x, y):
        return tuple((a + b) % n if n else a + b for a, b, n in zip(x, y, self.moduli))

    def _sub(self, x, y):
        return tuple((a - b) % n if n else a - b for a, b, n in zip(x, y, self.moduli))

    def _neg(self, x):
        return tuple(-a % n if n else -a for a, n in zip(x, self.moduli))

    def elements(self):
        if 0 in self.moduli:
            raise ValueError('an infinite group has no enumerated full domain')
        return tuple(product(*(range(n) for n in self.moduli)))


def _group(group):
    if type(group) is not Group:
        raise ValueError('a validated Group is required')


def _weights(group, weights, allow_empty=False):
    _group(group)
    if type(weights) is not dict or len(weights) > MAX_SUPPORT:
        raise ValueError('weights must be a dictionary with at most 128 entries')
    result = {}
    for point, weight in weights.items():
        group.point(point)
        if type(weight) not in (int, Fraction):
            raise ValueError('weights must be exact integers or Fractions, not bools or floats')
        if weight < 0:
            raise ValueError('negative weights are forbidden')
        q = Fraction(weight)
        if q.numerator.bit_length() > MAX_WEIGHT_BITS or q.denominator.bit_length() > MAX_DENOMINATOR_BITS:
            raise ValueError('weight bit limit exceeded')
        if q:
            result[point] = q.numerator if q.denominator == 1 else q
    if not result and not allow_empty:
        raise ValueError('a nonzero weight is required')
    return result


def _convolution(group, left, right):
    result = Counter()
    for x, wx in left.items():
        for y, wy in right.items():
            result[group._add(x, y)] += wx * wy
    return result


def convolution(group, left, right):
    return dict(_convolution(group, _weights(group, left, True), _weights(group, right, True)))


def _norm(values):
    return sum(x * x for x in values.values())


@dataclass(frozen=True)
class Energy:
    ordinary: object
    respected: object

    @property
    def ratio(self):
        return Fraction(self.respected, self.ordinary)


def energy(domain, target, weights, images):
    """Ordered-pair buckets compute both ordered-quadruple energies exactly."""
    _group(target)
    weights = _weights(domain, weights)
    if type(images) is not dict or len(images) != len(weights) or set(images) != set(weights):
        raise ValueError('images must have exactly the positive-support keys')
    for image in images.values():
        target.point(image)
    ordinary = Counter(); respected = Counter()
    for x, wx in weights.items():
        for y, wy in weights.items():
            s = domain._add(x, y); t = target._add(images[x], images[y]); mass = wx * wy
            ordinary[s] += mass; respected[s, t] += mass
    answer = Energy(_norm(ordinary), _norm(respected))
    require(0 < answer.respected <= answer.ordinary, 'invalid energy ordering')
    return answer


def parity_sos(domain, weights):
    """The index-two SOS for the first-coordinate parity map, with target Z."""
    weights = _weights(domain, weights)
    if domain.moduli[0] % 2:
        raise ValueError('first coordinate must have even or infinite order')
    even = {x: w for x, w in weights.items() if not x[0] % 2}
    odd = {x: w for x, w in weights.items() if x[0] % 2}
    ee = _convolution(domain, even, even); oo = _convolution(domain, odd, odd)
    eo = _convolution(domain, even, odd)
    R = Counter()
    for x, wx in even.items():
        for y, wy in odd.items():
            R[domain._sub(y, x)] += wx * wy
    U = _norm(ee); V = _norm(oo); D = _norm(eo)
    C = sum(value * oo.get(x, 0) for x, value in ee.items())
    diff = sum((ee.get(x, 0) - oo.get(x, 0)) ** 2 for x in set(ee) | set(oo))
    shifts = set(R) | {domain._neg(h) for h in R}
    asym = sum((R.get(h, 0) - R.get(domain._neg(h), 0)) ** 2 for h in shifts)
    measured = energy(domain, Group((0,)), weights, {x: (x[0] % 2,) for x in weights})
    require(C == sum(v * R.get(domain._neg(h), 0) for h, v in R.items()), 'correlation C identity')
    require(D == _norm(R), 'correlation D identity')
    require(measured.ordinary == U + V + 2 * C + 4 * D, 'ordinary parity identity')
    require(measured.respected == U + V + 4 * D, 'respected parity identity')
    require(4 * measured.respected - 3 * measured.ordinary == diff + 2 * asym, 'index-two SOS')
    return dict(U=U, V=V, C=C, D=D, difference_norm=diff,
                correlation_asymmetry=asym, energy=measured)


def interval_ratio(m):
    bounded_integer(m, 'm')
    return Fraction(3, 4) + Fraction(9, 32 * m * m + 4)


def cylinder_ratio(m):
    bounded_integer(m, 'm')
    return Fraction(5 * m * m + 1, 8 * m * m + 1)


def box_ratio(m1, m2):
    bounded_integer(m1, 'm1'); bounded_integer(m2, 'm2')
    a, b = m1 * m1, m2 * m2
    return Fraction(40 * a * b + 8 * a + 8 * b + 7, (8 * a + 1) * (8 * b + 1))


def indicator_support_bound(epsilon):
    if type(epsilon) not in (int, Fraction) or epsilon <= 0:
        raise ValueError('epsilon must be a positive exact rational')
    epsilon = Fraction(epsilon)
    if max(epsilon.numerator.bit_length(), epsilon.denominator.bit_length()) > 128:
        raise ValueError('epsilon bit limit exceeded')
    # Smallest m with 32 epsilon m^2 >= 9; no floating-point rounding.
    numerator = 9 * epsilon.denominator; denominator = 32 * epsilon.numerator
    m = isqrt(numerator // denominator)
    if m * m * denominator < numerator:
        m += 1
    return max(6, 2 * m)


def binomial_ratio(m):
    bounded_integer(m, 'm')
    return Fraction(3, 4) + Fraction(comb(4 * m, 2 * m), 4 * comb(8 * m, 4 * m))


def cyclic_histograms(values, target):
    """Full-domain derivative histograms for a cyclic map with N <= 8."""
    _group(target)
    if type(values) is not tuple or not 1 <= len(values) <= 8:
        raise ValueError('values must be a tuple of one through eight image points')
    for value in values:
        target.point(value)
    n = len(values); Q = []
    for h in range(n):
        histogram = Counter(target._sub(values[(x + h) % n], values[x]) for x in range(n))
        Q.append(sum(count * count for count in histogram.values()))
    differences = {target._sub(values[(x + 1) % n], values[x]) for x in range(n)}
    return dict(Q=tuple(Q), affine=len(differences) == 1,
                energy=Energy(n ** 3, sum(Q)))


def check_small_cycles():
    counts = []; total = 0; nonaffine = 0
    targets = (Group((2,)), Group((3,)), Group((4,)), Group((2, 2)), Group((2, 3)))
    for target in targets:
        elements = target.elements(); count = 0
        for n in range(1, 7):
            for tail in product(elements, repeat=n - 1):
                values = (target.zero,) + tail
                result = cyclic_histograms(values, target); count += 1
                Q = result['Q']
                require(Q[0] == n * n and all(Q[h] == Q[-h] for h in range(n)), 'cyclic histogram symmetry')
                if not result['affine']:
                    nonaffine += 1
                    require(result['energy'].ratio <= Fraction(3, 4), 'small cyclic 3/4 bound')
        total += count; counts.append({'target_moduli': target.moduli, 'normalized_maps': count})
    return dict(cases=total, nonaffine=nonaffine, targets=counts, domain_orders=[1, 2, 3, 4, 5, 6])


def check_four_points():
    count = 0
    for target in (Group((0,)), Group((3,)), Group((2, 2))):
        pool = ((-1,), (0,), (1,)) if target.moduli == (0,) else target.elements()
        for values in product(pool, repeat=4):
            M = target._sub(target._add(values[0], values[3]), target._add(values[1], values[2]))
            if M == target.zero:
                continue
            w = {(i,): 1 for i in range(4)}
            for modulus in (0, 7, 8):
                measured = energy(Group((modulus,)), target, w, {(i,): values[i] for i in range(4)})
                require(measured.ordinary == 44 and measured.respected <= 32, 'four-point 8/11 count')
                count += 1
    return dict(cases=count, ordinary_energy=44, respected_upper=32)


def check_sos():
    count = 0
    for modulus in (0, 2, 4, 6, 8):
        size = 4 if modulus == 0 else modulus
        points = tuple((j,) for j in range(size))
        for seed in range(1, 17):
            weights = {p: Fraction((seed * (j + 1) + j * j) % 7, 1 + seed % 3) for j, p in enumerate(points)}
            if not any(weights.values()):
                continue
            result = parity_sos(Group((modulus,)), weights)
            require(result['energy'].ratio >= Fraction(3, 4), 'SOS lower bound')
            if not modulus:
                require(result['energy'].ratio > Fraction(3, 4), 'integer strict nonattainment')
            count += 1
    return dict(cases=count, finite_and_integer_domains=True)


def check_jensen():
    V = Group((2, 2)); target = Group((2,)); points = V.elements()
    q = {x: (x[0] * x[1],) for x in points}
    require(energy(V, target, dict.fromkeys(points, 1), q) == Energy(64, 40), 'F2^2 full counts')
    nonaffine_jensen_maps = 0
    for tail in product(range(2), repeat=3):
        values = dict(zip(points, (0,) + tail)); affine = True
        for x, y in product(points, repeat=2):
            require((values[V._add(x, y)] + values[V._sub(x, y)] - 2 * values[x]) % 2 == 0, 'Jensen F2^2')
            if (values[V._add(x, y)] - values[x] - values[y]) % 2:
                affine = False
        if not affine:
            measured = energy(V, target, dict.fromkeys(points, 1), {x: (v,) for x, v in values.items()})
            require(measured == Energy(64, 40), 'nonlinear Jensen count'); nonaffine_jensen_maps += 1
    weighted = 0
    for entries in product(range(4), repeat=4):
        if not any(entries):
            continue
        w = {x: weight for x, weight in zip(points, entries) if weight}
        measured = energy(V, target, w, {x: q[x] for x in w})
        a, b, c, d = entries
        polynomial = sum(t ** 4 for t in entries) + 6 * sum(u * u * v * v for u, v in combinations(entries, 2)) + 24 * a * b * c * d
        require(measured.ordinary == polynomial, 'F2^2 energy polynomial')
        require(measured.ordinary - measured.respected == 24 * a * b * c * d, 'F2^2 defect')
        require(measured.ratio >= Fraction(5, 8), 'weighted 5/8 endpoint'); weighted += 1
    return dict(normalized_maps=8, nonaffine_jensen_maps=nonaffine_jensen_maps, weighted_cases=weighted, full_ratio='5/8')


def check_boxes():
    intervals = cylinders = boxes = 0
    for m in range(1, 13):
        w = {(i,): 1 for i in range(2 * m)}
        result = parity_sos(Group((0,)), w)
        U = (2 * m ** 3 + m) // 3
        require(result['U'] == result['V'] == result['D'] == U and result['C'] == U - m, 'interval triangle')
        require(result['energy'].ratio == interval_ratio(m), 'interval exact ratio'); intervals += 1
    for m in range(1, 5):
        for q in range(1, 4):
            domain = Group((0, 2 * q)); w = dict.fromkeys(product(range(2 * m), range(2 * q)), 1)
            measured = energy(domain, Group((2,)), w, {x: ((x[0] % 2) * (x[1] % 2),) for x in w})
            require(measured.ratio == cylinder_ratio(m), 'cylinder exact ratio'); cylinders += 1
    for m1, m2 in product(range(1, 6), repeat=2):
        w = dict.fromkeys(product(range(2 * m1), range(2 * m2)), 1)
        measured = energy(Group((0, 0)), Group((2,)), w, {x: ((x[0] % 2) * (x[1] % 2),) for x in w})
        require(measured.ratio == box_ratio(m1, m2), 'box exact ratio')
        a, b = m1 * m1, m2 * m2
        require(measured.ratio - Fraction(5, 8) == Fraction(3 * (8 * a + 8 * b + 17), 8 * (8 * a + 1) * (8 * b + 1)), 'box +17 excess'); boxes += 1
    require(box_ratio(1, 2) == Fraction(23, 33) and box_ratio(2, 2) == Fraction(79, 121), 'small boxes')
    return dict(intervals=intervals, cylinders=cylinders, boxes=boxes, excess_constant=17)


def check_wrapping_and_support():
    wrapping = witnesses = 0
    for n in range(1, 17):
        for m in range(1, n + 1):
            w = {(j,): 1 for j in range(2 * m)}
            result = parity_sos(Group((2 * n,)), w)
            U0 = (2 * m ** 3 + m) // 3
            require(result['U'] - result['C'] == min(m, n - m), 'wrapped interval difference')
            require(result['U'] >= U0 and result['energy'].ratio <= interval_ratio(m), 'wrapped interval bound'); wrapping += 1
    six_rows = {}
    for N1, N2 in product((0, 2, 4, 6, 8, 10), repeat=2):
        lengths = (2, 2 if N2 == 2 else 3)
        w = dict.fromkeys(product(range(lengths[0]), range(lengths[1])), 1)
        result = energy(Group((N1, N2)), Group((2,)), w, {x: ((x[0] % 2) * (x[1] % 2),) for x in w})
        first = parity_sos(Group((N1,)), {(j,): 1 for j in range(lengths[0])})
        second = parity_sos(Group((N2,)), {(j,): 1 for j in range(lengths[1])})
        loss = 8 * (first['C'] * second['D'] + first['D'] * second['C'] + first['D'] * second['D'])
        require(result.ordinary == first['energy'].ordinary * second['energy'].ordinary, 'product ordinary energy')
        require(result.ordinary - result.respected == loss, 'general balanced-pattern loss')
        require(len(w) <= 6 and result.ratio <= Fraction(47, 63), 'six-point witness')
        category = (int(N1 == 2), '2' if N2 == 2 else '4' if N2 == 4 else 'at least 6 or infinite')
        six_rows[category] = (result.ordinary, result.respected, loss, str(result.ratio))
        witnesses += 1
    require(len(six_rows) == 6, 'six wrapping types')
    require(Fraction(3, 4) - Fraction(47, 63) == Fraction(1, 252), 'six-point strict margin')
    for epsilon in (Fraction(1, 1000000), Fraction(9, 128), Fraction(1, 10), Fraction(1), Fraction(10)):
        s = indicator_support_bound(epsilon); m = s // 2
        require(Fraction(9, 32 * m * m + 4) <= epsilon, 'exact support rounding')
    return dict(wrapped_intervals=wrapping, small_product_witnesses=witnesses, support_rounding_cases=5,
                jensen_support_upper=6, jensen_ratio_upper='47/63',
                six_wrapping_types=[dict(first_order_two=bool(k[0]), second_order_class=k[1],
                ordinary=v[0], respected=v[1], loss=v[2], ratio=v[3]) for k, v in sorted(six_rows.items())])


def check_indicator_lower_bound():
    count = 0; universe = tuple(range(-4, 6))
    for mask in range(1, 1 << len(universe)):
        A = tuple(x for j, x in enumerate(universe) if mask >> j & 1)
        result = parity_sos(Group((0,)), {(x,): 1 for x in A}); s = len(A)
        require(result['difference_norm'] >= s, 'indicator coefficient-parity lower bound')
        measured = result['energy']
        require(measured.ordinary <= s ** 3, 'indicator cubic energy bound')
        require(measured.ratio - Fraction(3, 4) >= Fraction(1, 4 * s * s), 'indicator support lower bound')
        count += 1
    return dict(cases=count, integer_universe=[-4, 5], nonempty_subsets=True)


def check_binomial():
    integer_cases = finite_cases = 0
    for m in range(1, 13):
        w = {(j,): comb(2 * m, j) for j in range(2 * m + 1)}
        result = parity_sos(Group((0,)), w)
        require(result['energy'].ordinary == comb(8 * m, 4 * m), 'binomial denominator')
        require(result['difference_norm'] == comb(4 * m, 2 * m), 'binomial signed norm')
        require(result['correlation_asymmetry'] == 0, 'binomial reflection')
        require(result['energy'].ratio == binomial_ratio(m), 'binomial exact ratio')
        require(comb(8 * m, 4 * m) >= comb(4 * m, 2 * m) ** 2 and comb(4 * m, 2 * m) >= 4 ** m, 'Vandermonde bounds')
        integer_cases += 1
        for N in range(2, 4 * m + 5, 2):
            if N <= 2 * m + 1:
                folded = {(j,): 1 for j in range(N)}
            else:
                folded = w
            finite = parity_sos(Group((N,)), folded)
            require(len(folded) <= 2 * m + 1, 'folded support')
            require(finite['energy'].ratio - Fraction(3, 4) <= Fraction(1, 2 * 4 ** m), 'folded binomial bound')
            if N > 2 * m + 1:
                require(finite['correlation_asymmetry'] == 0, 'folded reflection')
                require(finite['difference_norm'] <= 2 * comb(4 * m, 2 * m), 'folded signed norm bound')
                require(finite['energy'].ordinary >= comb(8 * m, 4 * m), 'folded nonnegative norm bound')
            else:
                require(finite['energy'].ratio == Fraction(3, 4), 'full finite endpoint')
            finite_cases += 1
    return dict(integer_cases=integer_cases, finite_cases=finite_cases, largest_m=12)


def run_checks():
    return dict(report=288, status='passed', arithmetic='exact integer and rational',
        scope='Bounded diagnostics, not a universal theorem proof or Lean kernel certificate',
        small_cycles=check_small_cycles(), four_points=check_four_points(),
        index_two_sos=check_sos(), jensen=check_jensen(), boxes=check_boxes(),
        wrapping_and_support=check_wrapping_and_support(), indicator_lower_bound=check_indicator_lower_bound(),
        binomial=check_binomial())


def main(argv=None):
    args = sys.argv[1:] if argv is None else argv
    if type(args) is not list or args:
        raise ValueError('this bounded diagnostic accepts no command-line arguments')
    print(json.dumps(run_checks(), indent=2, sort_keys=True))
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (ValueError, RuntimeError) as error:
        raise SystemExit('ERROR: ' + str(error))
