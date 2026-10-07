#!/usr/bin/env python3
"""Exact, bounded, offline diagnostics for Report289; not a universal proof checker."""
from __future__ import annotations

import argparse
from collections import defaultdict
from dataclasses import dataclass
from fractions import Fraction
from functools import total_ordering
from itertools import product
import json
from math import comb, gcd
import sys

sys.dont_write_bytecode = True
MAX_SUPPORT = 128
MAX_COORDINATE = 4096
MAX_WEIGHT_BITS = 256
MAX_DENOMINATOR_BITS = 128
MAX_BINOMIAL_M = 32


def require(condition, message):
    """A runtime check that remains active under python -O."""
    if not condition:
        raise RuntimeError(message)


def bounded_integer(value, name, low, high):
    if type(value) is not int or not low <= value <= high:
        raise ValueError(f'{name} must be an integer from {low} through {high}')
    return value


def rational(value):
    if type(value) not in (int, Fraction):
        raise ValueError('an exact integer or Fraction is required; bools and floats are forbidden')
    return Fraction(value)


@total_ordering
@dataclass(frozen=True, eq=False)
class Quadratic:
    """Exact a+b*sqrt(d), with d=2 or 6; comparisons use rational squares."""
    a: object = 0
    b: object = 0
    d: int = 2

    def __post_init__(self):
        if type(self.d) is not int or self.d not in (2, 6):
            raise ValueError('the supported quadratic radicands are 2 and 6')
        object.__setattr__(self, 'a', rational(self.a))
        object.__setattr__(self, 'b', rational(self.b))

    def _coerce(self, other):
        if type(other) is Quadratic:
            if other.d != self.d:
                raise ValueError('different quadratic fields cannot be mixed')
            return other
        return Quadratic(rational(other), 0, self.d)

    def __add__(self, other):
        v = self._coerce(other)
        return Quadratic(self.a + v.a, self.b + v.b, self.d)

    __radd__ = __add__

    def __neg__(self):
        return Quadratic(-self.a, -self.b, self.d)

    def __sub__(self, other):
        return self + (-self._coerce(other))

    def __rsub__(self, other):
        return self._coerce(other) - self

    def __mul__(self, other):
        v = self._coerce(other)
        return Quadratic(self.a * v.a + self.d * self.b * v.b,
                         self.a * v.b + self.b * v.a, self.d)

    __rmul__ = __mul__

    def __truediv__(self, other):
        v = self._coerce(other)
        denominator = v.a * v.a - self.d * v.b * v.b
        if not denominator:
            raise ZeroDivisionError('division by zero in a quadratic field')
        return self * Quadratic(v.a / denominator, -v.b / denominator, self.d)

    def __rtruediv__(self, other):
        return self._coerce(other) / self

    def __pow__(self, exponent):
        bounded_integer(exponent, 'exponent', -32, 32)
        if exponent < 0:
            return (1 / self) ** (-exponent)
        result = Quadratic(1, 0, self.d)
        factor = self
        while exponent:
            if exponent % 2:
                result = result * factor
            factor = factor * factor
            exponent //= 2
        return result

    def sign(self):
        a, b = self.a, self.b
        if not b:
            return (a > 0) - (a < 0)
        if not a:
            return (b > 0) - (b < 0)
        if a > 0 and b > 0:
            return 1
        if a < 0 and b < 0:
            return -1
        comparison = (a * a > self.d * b * b) - (a * a < self.d * b * b)
        return comparison if a > 0 else -comparison

    def __bool__(self):
        return bool(self.a or self.b)

    def __eq__(self, other):
        if type(other) is Quadratic:
            if self.d != other.d:
                return not self.b and not other.b and self.a == other.a
            return self.a == other.a and self.b == other.b
        if type(other) in (int, Fraction):
            return not self.b and self.a == other
        return False

    def __lt__(self, other):
        return (self - self._coerce(other)).sign() < 0

    def __hash__(self):
        return hash(self.a) if not self.b else hash((self.a, self.b, self.d))


@dataclass(frozen=True)
class Group:
    """At most four cyclic factors; 0 denotes Z; finite coordinates are canonical."""
    moduli: tuple

    def __post_init__(self):
        if type(self.moduli) is not tuple or not 1 <= len(self.moduli) <= 4:
            raise ValueError('moduli must be a tuple of one through four integers')
        size = 1
        for modulus in self.moduli:
            bounded_integer(modulus, 'modulus', 0, 128)
            size *= max(1, modulus)
        if size > 128:
            raise ValueError('the product of finite factor sizes must not exceed 128')

    @property
    def zero(self):
        return (0,) * len(self.moduli)

    def point(self, value):
        if type(value) is not tuple or len(value) != len(self.moduli):
            raise ValueError('a coordinate tuple of the correct dimension is required')
        for coordinate, modulus in zip(value, self.moduli):
            if type(coordinate) is not int or abs(coordinate) > MAX_COORDINATE:
                raise ValueError('coordinates must be bounded integers, not bools')
            if modulus and not 0 <= coordinate < modulus:
                raise ValueError('finite coordinates must be canonical residues')
        return value

    def _add(self, x, y):
        return tuple((a + b) % n if n else a + b for a, b, n in zip(x, y, self.moduli))

    def _sub(self, x, y):
        return tuple((a - b) % n if n else a - b for a, b, n in zip(x, y, self.moduli))

    def _neg(self, x):
        return tuple(-a % n if n else -a for a, n in zip(x, self.moduli))

    def add(self, x, y):
        self.point(x)
        self.point(y)
        return self._add(x, y)

    def elements(self):
        if 0 in self.moduli:
            raise ValueError('an infinite group cannot be enumerated')
        return tuple(product(*(range(n) for n in self.moduli)))


def _group(group):
    if type(group) is not Group:
        raise ValueError('a validated Group is required')


def parity_character(group, coefficients=None):
    """Validate a homomorphism to C2; it need not be surjective on this group."""
    _group(group)
    if coefficients is None:
        coefficients = (1,) + (0,) * (len(group.moduli) - 1)
    if type(coefficients) is not tuple or len(coefficients) != len(group.moduli):
        raise ValueError('parity coefficients must be a tuple of the correct dimension')
    for coefficient, modulus in zip(coefficients, group.moduli):
        if type(coefficient) is not int or coefficient not in (0, 1):
            raise ValueError('parity coefficients must be integers 0 or 1')
        if coefficient and modulus % 2:
            raise ValueError('nonzero parity is impossible on an odd cyclic factor')
    return coefficients


def _parity(point, coefficients):
    return sum(a * b for a, b in zip(point, coefficients)) % 2


def _weights(group, weights, allow_empty=False):
    _group(group)
    if type(weights) is not dict or len(weights) > MAX_SUPPORT:
        raise ValueError('weights must be a dictionary of at most 128 entries')
    result = {}
    fields = set()
    for point, weight in weights.items():
        group.point(point)
        if type(weight) is Quadratic:
            fields.add(weight.d)
            coefficients = (weight.a, weight.b)
        else:
            weight = rational(weight)
            coefficients = (weight,)
        if len(fields) > 1:
            raise ValueError('all algebraic weights must lie in the same quadratic field')
        if any(abs(q.numerator).bit_length() > MAX_WEIGHT_BITS or
               q.denominator.bit_length() > MAX_DENOMINATOR_BITS for q in coefficients):
            raise ValueError('weight coefficient bit limit exceeded')
        if weight < 0:
            raise ValueError('weights must be nonnegative')
        if weight:
            result[point] = weight
    if not result and not allow_empty:
        raise ValueError('a nonzero weight is required')
    return result


def _convolution(group, left, right):
    result = defaultdict(lambda: Fraction(0))
    for x, wx in left.items():
        for y, wy in right.items():
            result[group._add(x, y)] += wx * wy
    return {x: value for x, value in result.items() if value}


def convolution(group, left, right):
    left = _weights(group, left, True)
    right = _weights(group, right, True)
    fields = {w.d for weights in (left, right) for w in weights.values() if type(w) is Quadratic}
    if len(fields) > 1:
        raise ValueError('different quadratic fields cannot be mixed')
    return _convolution(group, left, right)


def _norm(values):
    return sum((x * x for x in values.values()), Fraction(0))


def _divide(a, b):
    return Fraction(a, b) if type(a) in (int, Fraction) and type(b) in (int, Fraction) else a / b


@dataclass(frozen=True)
class Energy:
    ordinary: object
    respected: object

    @property
    def ratio(self):
        return _divide(self.respected, self.ordinary)

    @property
    def defect(self):
        return self.ratio - Fraction(3, 4)


def energy(domain, target, weights, images):
    """Compute ordered-quadruple energies from exact ordered-pair buckets."""
    _group(target)
    weights = _weights(domain, weights)
    if type(images) is not dict or len(images) != len(weights) or set(images) != set(weights):
        raise ValueError('images must have exactly the positive-support keys')
    for image in images.values():
        target.point(image)
    ordinary = defaultdict(lambda: Fraction(0))
    respected = defaultdict(lambda: Fraction(0))
    for x, wx in weights.items():
        for y, wy in weights.items():
            s = domain._add(x, y)
            t = target._add(images[x], images[y])
            ordinary[s] += wx * wy
            respected[s, t] += wx * wy
    result = Energy(_norm(ordinary), _norm(respected))
    require(0 < result.respected <= result.ordinary, 'energy ordering failed')
    return result


def parity_sos(group, weights, coefficients=None):
    """Index-two identity; the image labels 0 and 1 are summed in Z, not C2."""
    coefficients = parity_character(group, coefficients)
    weights = _weights(group, weights)
    even = {x: w for x, w in weights.items() if not _parity(x, coefficients)}
    odd = {x: w for x, w in weights.items() if _parity(x, coefficients)}
    ee = _convolution(group, even, even)
    oo = _convolution(group, odd, odd)
    eo = _convolution(group, even, odd)
    correlation = defaultdict(lambda: Fraction(0))
    for x, wx in even.items():
        for y, wy in odd.items():
            correlation[group._sub(y, x)] += wx * wy
    U, V, D = _norm(ee), _norm(oo), _norm(eo)
    C = sum((value * oo.get(x, 0) for x, value in ee.items()), Fraction(0))
    difference = sum(((ee.get(x, 0) - oo.get(x, 0)) ** 2 for x in set(ee) | set(oo)), Fraction(0))
    shifts = set(correlation) | {group._neg(h) for h in correlation}
    asymmetry = sum(((correlation.get(h, 0) - correlation.get(group._neg(h), 0)) ** 2
                     for h in shifts), Fraction(0))
    measured = energy(group, Group((0,)), weights, {x: (_parity(x, coefficients),) for x in weights})
    require(C == sum((v * correlation.get(group._neg(h), 0) for h, v in correlation.items()), Fraction(0)), 'correlation C identity')
    require(D == _norm(correlation), 'correlation D identity')
    require(measured.ordinary == U + V + 2 * C + 4 * D, 'ordinary parity identity')
    require(measured.respected == U + V + 4 * D, 'respected parity identity')
    require(4 * measured.respected - 3 * measured.ordinary == difference + 2 * asymmetry, 'SOS identity')
    require((difference == 0) == (measured.defect == 0), 'endpoint convolution criterion')
    return dict(energy=measured, U=U, V=V, C=C, D=D, ee=ee, oo=oo, eo=eo,
                correlation=dict(correlation), difference_norm=difference,
                correlation_asymmetry=asymmetry)


def translate(group, weights, shift):
    weights = _weights(group, weights)
    group.point(shift)
    moved = {group._add(x, shift): w for x, w in weights.items()}
    # The public point bound must also hold for this reusable output.
    for point in moved:
        group.point(point)
    return moved


def _extended_gcd(a, b):
    old_r, r, old_s, s, old_t, t = a, b, 1, 0, 0, 1
    while r:
        quotient = old_r // r
        old_r, r = r, old_r - quotient * r
        old_s, s = s, old_s - quotient * s
        old_t, t = t, old_t - quotient * t
    return (old_r, old_s, old_t) if old_r >= 0 else (-old_r, -old_s, -old_t)


def integer_kernel(matrix, columns):
    """Return a full Z-kernel basis by unimodular column operations, not Q nullspace."""
    bounded_integer(columns, 'columns', 0, MAX_SUPPORT)
    if type(matrix) is not tuple or len(matrix) > 4:
        raise ValueError('matrix must be a tuple with at most four rows')
    for row in matrix:
        if type(row) is not tuple or len(row) != columns:
            raise ValueError('matrix rows must be tuples with the given column count')
        for value in row:
            bounded_integer(value, 'matrix entry', -2 * MAX_COORDINATE, 2 * MAX_COORDINATE)
    A = [list(row) for row in matrix]
    V = [[int(i == j) for j in range(columns)] for i in range(columns)]
    rank = 0
    for row in range(len(A)):
        pivot = next((j for j in range(rank, columns) if A[row][j]), None)
        if pivot is None:
            continue
        for M in (A, V):
            for values in M:
                values[rank], values[pivot] = values[pivot], values[rank]
        for j in range(rank + 1, columns):
            a, b = A[row][rank], A[row][j]
            if not b:
                continue
            g, u, v = _extended_gcd(a, b)
            for M in (A, V):
                for values in M:
                    old_p, old_j = values[rank], values[j]
                    values[rank] = u * old_p + v * old_j
                    values[j] = -(b // g) * old_p + (a // g) * old_j
        rank += 1
    basis = tuple(tuple(V[i][j] for i in range(columns)) for j in range(rank, columns))
    for vector in basis:
        require(all(sum(a * b for a, b in zip(row, vector)) == 0 for row in matrix), 'integer kernel identity')
    return rank, basis


def local_structure(group, weights, coefficients=None):
    """Analyze L=<support-support>; its torsion is the kernel of ambient free projection."""
    coefficients = parity_character(group, coefficients)
    weights = _weights(group, weights)
    base = min(weights)
    differences = tuple(group._sub(x, base) for x in sorted(weights) if x != base)
    free_indices = tuple(i for i, modulus in enumerate(group.moduli) if not modulus)
    matrix = tuple(tuple(x[i] for x in differences) for i in free_indices)
    rank, kernel = integer_kernel(matrix, len(differences))
    torsion_generators = []
    for relation in kernel:
        point = tuple(sum(c * x[i] for c, x in zip(relation, differences)) for i in range(len(group.moduli)))
        point = tuple(value % modulus if modulus else value for value, modulus in zip(point, group.moduli))
        require(all(point[i] == 0 for i in free_indices), 'local torsion has a free coordinate')
        if point != group.zero and point not in torsion_generators:
            torsion_generators.append(point)
    witnesses = tuple(x for x in torsion_generators if _parity(x, coefficients))
    projections = {tuple(x[i] for i in free_indices) for x in weights}
    return dict(basepoint=base, support_size=len(weights), free_rank=rank,
                free_projection_size=len(projections), torsion_generators=tuple(torsion_generators),
                parity_trivial_on_local_torsion=not witnesses,
                parity_one_torsion_witnesses=witnesses)


def central_lower_bound(projection_size):
    m = bounded_integer(projection_size, 'free projection size', 1, MAX_SUPPORT)
    return Fraction(1, 4 ** m * comb(2 * m - 2, m - 1))


def clean_lower_bound(projection_size):
    m = bounded_integer(projection_size, 'free projection size', 1, MAX_SUPPORT)
    return Fraction(1, 4 * 16 ** (m - 1))


def local_gap_check(group, weights, coefficients=None):
    local = local_structure(group, weights, coefficients)
    if not local['parity_trivial_on_local_torsion']:
        raise ValueError('the local-torsion parity hypothesis is false; the gap bound is inapplicable')
    measured = parity_sos(group, weights, coefficients)['energy']
    m = local['free_projection_size']
    central, clean = central_lower_bound(m), clean_lower_bound(m)
    require(measured.defect >= central >= clean > 0, 'local quantitative gap failed')
    return dict(local=local, energy=measured, central_lower=central, clean_lower=clean)


def binomial_weights(m):
    m = bounded_integer(m, 'm', 1, MAX_BINOMIAL_M)
    return {(j,): comb(2 * m, j) for j in range(2 * m + 1)}


def binomial_defect(m):
    m = bounded_integer(m, 'm', 1, MAX_BINOMIAL_M)
    return Fraction(comb(4 * m, 2 * m), 4 * comb(8 * m, 4 * m))


def binomial_upper_bound(m):
    m = bounded_integer(m, 'm', 1, MAX_BINOMIAL_M)
    return Fraction(1, 2 * 16 ** m)


def support_window(epsilon):
    """Integer-rounded necessary/constructive bounds, with no logarithms or floats."""
    epsilon = rational(epsilon)
    if not 0 < epsilon < Fraction(1, 4):
        raise ValueError('epsilon must lie strictly between 0 and 1/4')
    if max(epsilon.numerator.bit_length(), epsilon.denominator.bit_length()) > 128:
        raise ValueError('epsilon bit limit exceeded')
    lower = next(s for s in range(1, MAX_SUPPORT + 1) if central_lower_bound(s) <= epsilon)
    m = next(m for m in range(1, MAX_BINOMIAL_M + 1) if binomial_upper_bound(m) <= epsilon)
    return dict(necessary_support=lower, constructive_support=2 * m + 1, binomial_m=m)


def three_point_energy(a, b, c):
    a, b, c = (rational(x) for x in (a, b, c))
    if min(a, b, c) <= 0:
        raise ValueError('all three weights must be positive')
    if any(abs(v.numerator).bit_length() > MAX_WEIGHT_BITS or v.denominator.bit_length() > MAX_DENOMINATOR_BITS for v in (a, b, c)):
        raise ValueError('three-point weight bit limit exceeded')
    p, q, t = a * c, b * b, a * a + c * c
    ordinary = t * t + 2 * p * p + q * q + 4 * q * (t + p)
    return Energy(ordinary, ordinary - 4 * p * q)


def three_point_slack(p, q, t):
    """Certificate E-(12+2sqrt(6))*p*q=(t-2p)*(t+2p+4q)+(q-sqrt(6)*p)^2."""
    root = Quadratic(0, 1, 6)
    values = []
    for value in (p, q, t):
        value = root._coerce(value)
        if any(abs(v.numerator).bit_length() > MAX_WEIGHT_BITS or v.denominator.bit_length() > MAX_DENOMINATOR_BITS for v in (value.a, value.b)):
            raise ValueError('three-point invariant bit limit exceeded')
        values.append(value)
    p, q, t = values
    if p <= 0 or q <= 0 or t < 2 * p:
        raise ValueError('certificate requires p,q>0 and t>=2p')
    ordinary = t * t + 2 * p * p + q * q + 4 * q * (t + p)
    slack = ordinary - (12 + 2 * root) * p * q
    first = (t - 2 * p) * (t + 2 * p + 4 * q)
    second = (q - root * p) ** 2
    require(slack == first + second and first >= 0 and second >= 0, 'three-point exact certificate')
    return dict(ordinary=ordinary, slack=slack, endpoint_imbalance=first,
                middle_imbalance=second, ratio=1 - 4 * p * q / ordinary,
                minimum=Quadratic(Fraction(3, 5), Fraction(1, 15), 6))


def _poly_add(left, right):
    result = dict(left)
    for powers, value in right.items():
        result[powers] = result.get(powers, 0) + value
    return {powers: value for powers, value in result.items() if value}


def _poly_scale(poly, scalar):
    return {powers: value * scalar for powers, value in poly.items() if value * scalar}


def _poly_mul(left, right):
    result = {}
    for a, x in left.items():
        for b, y in right.items():
            powers = tuple(u + v for u, v in zip(a, b))
            result[powers] = result.get(powers, 0) + x * y
    return {powers: value for powers, value in result.items() if value}


def three_point_polynomial_certificate():
    """Compare every coefficient in Q(sqrt(6))[p,q,t]; return the zero residual."""
    p, q, t = ({powers: Fraction(1)} for powers in ((1, 0, 0), (0, 1, 0), (0, 0, 1)))
    root = Quadratic(0, 1, 6)
    lhs = {(0, 0, 2): 1, (2, 0, 0): 2, (0, 2, 0): 1,
           (0, 1, 1): 4, (1, 1, 0): -8 - 2 * root}
    first = _poly_mul(_poly_add(t, _poly_scale(p, -2)),
                      _poly_add(_poly_add(t, _poly_scale(p, 2)), _poly_scale(q, 4)))
    middle = _poly_add(q, _poly_scale(p, -root))
    rhs = _poly_add(first, _poly_mul(middle, middle))
    residual = _poly_add(lhs, _poly_scale(rhs, -1))
    require(not residual, 'three-point polynomial coefficient identity')
    return dict(variables=['p', 'q', 't'], coefficient_field='Q(sqrt(6))',
                lhs_monomials=len(lhs), rhs_monomials=len(rhs), residual=[])


def translation_periods(group, weights):
    weights = _weights(group, weights)
    points = group.elements()
    return tuple(h for h in points if all(weights.get(group._add(x, h), 0) == weights.get(x, 0) for x in points))


def c6_example():
    group = Group((6,))
    weights = dict(enumerate((6, 5, 3, 2, 3, 5)))
    weights = {(j,): value for j, value in weights.items()}
    result = parity_sos(group, weights)
    require(result['energy'] == Energy(55728, 41796), 'C6 energies')
    require(all(result[k] == 6966 for k in ('U', 'V', 'C', 'D')), 'C6 pair norms')
    require(translation_periods(group, weights) == ((0,),), 'C6 nonperiodicity')
    return dict(support_size=6, weights=[6, 5, 3, 2, 3, 5],
                ordinary=result['energy'].ordinary, respected=result['energy'].respected,
                ratio=result['energy'].ratio, ee=[result['ee'].get((j,), 0) for j in range(6)],
                eo=[result['eo'].get((j,), 0) for j in range(6)], periods=[[0]])


def c8_example():
    root_half = Quadratic(0, Fraction(1, 2), 2)
    entries = (2, 1 + root_half, 1, 1 - root_half, 0, 1 - root_half, 1, 1 + root_half)
    group = Group((8,))
    weights = {(j,): value for j, value in enumerate(entries) if value}
    result = parity_sos(group, weights)
    odd_orders = sorted({8 // gcd(8, j) for j in range(1, 8, 2)})
    require(len(weights) == 7 and all(value > 0 for value in weights.values()), 'C8 positive support')
    require(result['energy'].ratio == Fraction(3, 4), 'C8 endpoint')
    require(odd_orders == [8] and len(weights) < min(odd_orders), 'C8 support versus odd-element orders')
    return dict(support_size=7, weights=list(entries), ordinary=result['energy'].ordinary,
                respected=result['energy'].respected, ratio=result['energy'].ratio,
                difference_norm=result['difference_norm'], correlation_asymmetry=result['correlation_asymmetry'],
                parity_one_element_orders=odd_orders)




def cyclotomic_n2_example():
    """The exact n=2 polynomial 1+sqrt(2)z+z^2 has F(z)F(-z)=1+z^4."""
    root = Quadratic(0, 1, 2)
    weights = {(0,): 1, (1,): root, (2,): 1}
    integer = parity_sos(Group((0,)), weights)
    require(integer['energy'] == Energy(34, 26), 'cyclotomic n2 integer energies')
    require(integer['difference_norm'] == 2 and integer['energy'].defect == Fraction(1, 68), 'cyclotomic n2 integer defect')
    signed = {point: integer['ee'].get(point, 0) - integer['oo'].get(point, 0)
              for point in set(integer['ee']) | set(integer['oo'])
              if integer['ee'].get(point, 0) != integer['oo'].get(point, 0)}
    require(signed == {(0,): 1, (4,): 1}, 'cyclotomic n2 polynomial product')
    finite = []
    for modulus in range(4, 18, 2):
        result = parity_sos(Group((modulus,)), weights)
        expected = Energy(36, 28) if modulus == 4 else Energy(34, 26)
        require(result['energy'] == expected, 'cyclotomic n2 finite energies')
        require(result['difference_norm'] == (4 if modulus == 4 else 2), 'cyclotomic n2 finite signed norm')
        finite.append(dict(modulus=modulus, energy=result['energy'], signed_norm=result['difference_norm']))
    return dict(integer_energy=integer['energy'], integer_signed_norm=integer['difference_norm'],
                signed_polynomial=signed, finite_cases=finite,
                scope='Direct Q(sqrt(2)) arithmetic for n=2; n=4 has a separate polynomial-reduction certificate')



def cyclotomic_n4_certificate():
    """Reduce every calculation to Q(sqrt(2)) using a>0, a^2=2b, b=2+sqrt(2).

    Write w=e+a*u with e on even indices and u on odd indices. Pair buckets
    then involve only 1, a and a^2; squared norms lie in Q(sqrt(2)). This is
    an exact polynomial reduction, not a general implementation of Q(a).
    """
    b = Quadratic(2, 1, 2)
    square_a = 2 * b
    require(b * b == 4 * b - 2 and square_a > 0, 'n4 defining identities')
    records = []
    for modulus in (0, 6, 8, 10):
        group = Group((modulus,))
        even = {(0,): Fraction(1), (2,): b, (4,): Fraction(1)}
        odd_factor = {(1,): Fraction(1), (3,): Fraction(1)}
        ee = _convolution(group, even, even)
        uu = _convolution(group, odd_factor, odd_factor)
        eu = _convolution(group, even, odd_factor)
        U, V, D = _norm(ee), square_a ** 2 * _norm(uu), square_a * _norm(eu)
        C = square_a * sum((value * uu.get(point, 0) for point, value in ee.items()), Fraction(0))
        measured = Energy(U + V + 2 * C + 4 * D, U + V + 4 * D)
        signed = {point: ee.get(point, 0) - square_a * uu.get(point, 0)
                  for point in set(ee) | set(uu)
                  if ee.get(point, 0) != square_a * uu.get(point, 0)}
        signed_norm = _norm(signed)
        correlation_factor = defaultdict(lambda: Fraction(0))
        for x, wx in even.items():
            for y, uy in odd_factor.items():
                correlation_factor[group._sub(y, x)] += wx * uy
        shifts = set(correlation_factor) | {group._neg(h) for h in correlation_factor}
        asymmetry = square_a * sum(((correlation_factor.get(h, 0) - correlation_factor.get(group._neg(h), 0)) ** 2
                                    for h in shifts), Fraction(0))
        require(asymmetry == 0, 'n4 reflection symmetry')
        require(4 * measured.respected - 3 * measured.ordinary == signed_norm + 2 * asymmetry, 'n4 reduced SOS')
        records.append(dict(modulus=modulus, energy=measured, signed_convolution=signed,
                            signed_norm=signed_norm, correlation_asymmetry=asymmetry))
    integer = records[0]
    expected_energy = 768 * b - 382
    require(integer['energy'].ordinary == expected_energy == Quadratic(1154, 768, 2), 'n4 exact ordinary energy')
    require(expected_energy == 2 + 32 * b + 128 * b * b + 16 * b ** 3, 'n4 energy polynomial')
    require(integer['signed_convolution'] == {(0,): 1, (8,): 1}, 'n4 signed polynomial identity')
    require(integer['signed_norm'] == 2 and integer['energy'].defect == 1 / (2 * expected_energy), 'n4 exact defect')
    for record in records[1:]:
        require(record['energy'].defect <= 2 * integer['energy'].defect, 'n4 finite wrapping upper bound')
    return dict(b=b, square_a=square_a, positive_a_description='a=sqrt(4+2sqrt(2))',
                scope='Polynomial reduction with a^2=2b; no floating-point or general quartic-field arithmetic',
                cases=records)


def cross_fiber_example():
    """Two attaining torsion fibers need not have an attaining union of spectra."""
    group = Group((0, 6))
    entries = ((6, 5, 3, 2, 3, 5), (6, 3, 3, 6, 3, 3))
    fibers = [{(n, j): value for j, value in enumerate(row)} for n, row in enumerate(entries)]
    separate = [parity_sos(group, fiber, (0, 1))['energy'] for fiber in fibers]
    require(all(measured.ratio == Fraction(3, 4) for measured in separate), 'separate fiber endpoints')
    weights = {point: value for fiber in fibers for point, value in fiber.items()}
    combined = parity_sos(group, weights, (0, 1))
    signed = {point: combined['ee'].get(point, 0) - combined['oo'].get(point, 0)
              for point in set(combined['ee']) | set(combined['oo'])
              if combined['ee'].get(point, 0) != combined['oo'].get(point, 0)}
    require(signed == {(1, 0): 24, (1, 2): -12, (1, 4): -12}, 'cross-fiber obstruction')
    require(combined['energy'].defect > 0, 'fiberwise endpoint is not sufficient')
    return dict(separate_energies=separate, combined_energy=combined['energy'],
                signed_convolution=signed, difference_norm=combined['difference_norm'])


def check_sos():
    cases = 0
    samples = ((Group((0,)), (1,)), (Group((2,)), (1,)), (Group((4,)), (1,)),
               (Group((6,)), (1,)), (Group((8,)), (1,)), (Group((0, 3)), (1, 0)),
               (Group((2, 0)), (1, 0)), (Group((0, 0)), (1, 1)))
    for group, parity in samples:
        points = tuple(product(*(range(n) if n else range(-1, 3) for n in group.moduli)))
        for seed in range(1, 13):
            weights = {x: Fraction((seed * (i + 1) + i * i) % 7, 1 + seed % 3) for i, x in enumerate(points)}
            if not any(weights.values()):
                continue
            result = parity_sos(group, weights, parity)
            require(result['energy'].defect >= 0, 'nonnegative defect')
            cases += 1
    return dict(cases=cases, group_character_pairs=len(samples), seeds_per_pair=12)


def check_integer_lower_bounds():
    universe = tuple(range(-3, 5))
    cases = 0
    for mask in range(1, 1 << len(universe)):
        weights = {(x,): Fraction(j + 1, 1 + mask % 3) for j, x in enumerate(universe) if mask >> j & 1}
        local_gap_check(Group((0,)), weights)
        cases += 1
    return dict(cases=cases, universe=list(universe), all_nonempty_support_subsets=True,
                one_deterministic_rational_weight_per_support=True)


def check_binomial():
    cases = 0
    for m in range(1, 13):
        result = parity_sos(Group((0,)), binomial_weights(m))
        require(result['energy'].ordinary == comb(8 * m, 4 * m), 'binomial ordinary energy')
        require(result['difference_norm'] == comb(4 * m, 2 * m), 'binomial signed norm')
        require(result['correlation_asymmetry'] == 0, 'binomial reflection')
        require(result['energy'].defect == binomial_defect(m) < binomial_upper_bound(m), 'refined binomial upper bound')
        product_value = Fraction(1)
        sum_value = Fraction(0)
        for k in range(2 * m + 1, 4 * m + 1):
            product_value *= 1 - Fraction(1, 2 * k)
            sum_value += Fraction(1, 2 * k)
        require(product_value == Fraction(comb(8 * m, 4 * m), 16 ** m * comb(4 * m, 2 * m)), 'central-binomial product')
        require(product_value >= 1 - sum_value > Fraction(1, 2), 'elementary product lower bound')
        cases += 1
    return dict(cases=cases, m_range=[1, 12], refined_strict_upper='1/(2*16^m)',
                m1_defect=binomial_defect(1), m12_defect=binomial_defect(12))


def check_three_points():
    polynomial = three_point_polynomial_certificate()
    cases = 0
    for a, b, c in product(range(1, 5), repeat=3):
        exact = three_point_energy(a, b, c)
        measured = parity_sos(Group((0,)), {(0,): a, (1,): b, (2,): c})['energy']
        require(exact == measured, 'three-point energy polynomial')
        certificate = three_point_slack(a * c, b * b, a * a + c * c)
        require(certificate['ratio'] == exact.ratio and certificate['ratio'] > certificate['minimum'], 'rational three-point lower bound')
        cases += 1
    root = Quadratic(0, 1, 6)
    optimum = three_point_slack(1, root, 2)
    require(optimum['slack'] == 0 and optimum['ratio'] == optimum['minimum'], 'exact three-point optimum')
    return dict(rational_weight_cases=cases, polynomial_certificate=polynomial,
                minimum=optimum['minimum'], minimum_defect=optimum['minimum'] - Fraction(3, 4),
                optimum_invariants=dict(p=1, q=root, t=2),
                middle_weight_description='6^(1/4); q=b^2=sqrt(6)')


def check_torsion_indicators():
    cases = 0
    for n in range(1, 17):
        group = Group((2 * n,))
        result = parity_sos(group, dict.fromkeys(group.elements(), 1))
        require(all(result[k] == n ** 3 for k in ('U', 'V', 'C', 'D')), 'finite indicator pair energies')
        require(result['energy'] == Energy(8 * n ** 3, 6 * n ** 3), 'finite indicator energies')
        cases += 1
    return dict(cases=cases, even_orders=[2 * n for n in range(1, 17)])


def check_local_examples():
    group = Group((2, 0))
    diagonal = {(0, 0): 1, (1, 1): 2, (0, 2): 1}
    first = local_gap_check(group, diagonal, (1, 0))
    shifted = translate(group, diagonal, (1, -3))
    second = local_gap_check(group, shifted, (1, 0))
    require(first['energy'] == second['energy'], 'translated energies')
    require(first['local']['free_rank'] == 1 and first['local']['torsion_generators'] == (), 'diagonal torsion-free local subgroup')
    require(first['local']['free_projection_size'] == 3, 'diagonal projection size')
    finite_group = Group((0, 3))
    fibers = {(j, t): (j + 1) * (t + 1) for j in range(3) for t in range(3)}
    fiber_result = local_gap_check(finite_group, fibers, (1, 0))
    require(fiber_result['local']['support_size'] == 9 and fiber_result['local']['free_projection_size'] == 3, 'free projection, not full support')
    endpoint = {(0, 0): 1, (1, 0): 1}
    endpoint_local = local_structure(group, endpoint, (1, 0))
    require(not endpoint_local['parity_trivial_on_local_torsion'], 'parity-one local torsion')
    require(parity_sos(group, endpoint, (1, 0))['energy'].ratio == Fraction(3, 4), 'local torsion indicator endpoint')
    # Equal total even/odd mass is insufficient: here ee and oo differ.
    balanced = {(0,): 1, (1,): 1}
    negative = parity_sos(Group((4,)), balanced)
    require(negative['energy'].ratio == 1 and negative['difference_norm'] > 0, 'mass balance alone is insufficient')
    return dict(cases=5, diagonal=first, translated_diagonal=second,
                torsion_fibers=fiber_result, parity_one_torsion_endpoint=endpoint_local,
                balanced_nonendpoint_ratio=negative['energy'].ratio)


def jsonable(value):
    if type(value) is Fraction:
        return str(value)
    if type(value) is Quadratic:
        return dict(a=str(value.a), b=str(value.b), radicand=value.d)
    if type(value) is Energy:
        return dict(ordinary=jsonable(value.ordinary), respected=jsonable(value.respected),
                    ratio=jsonable(value.ratio), defect=jsonable(value.defect))
    if type(value) is dict:
        if not all(type(key) is str for key in value):
            return [dict(point=list(key), value=jsonable(v)) for key, v in sorted(value.items())]
        return {key: jsonable(v) for key, v in value.items()}
    if type(value) in (tuple, list):
        return [jsonable(v) for v in value]
    return value


def run_checks():
    return dict(report=289, schema_version=1, status='passed',
                arithmetic='exact integers, fractions, Q(sqrt(2)), Q(sqrt(6)); no floating point',
                scope='Bounded diagnostics and polynomial identities, not a proof-assistant certificate or a proof of the imported Mahler-measure theorem',
                index_two_sos=check_sos(), integer_lower_bounds=check_integer_lower_bounds(),
                binomial=check_binomial(), three_points=check_three_points(),
                finite_torsion_indicators=check_torsion_indicators(), c6=c6_example(), c8=c8_example(),
                cross_fiber=cross_fiber_example(), cyclotomic_n2=cyclotomic_n2_example(),
                cyclotomic_n4=cyclotomic_n4_certificate(),
                local_examples=check_local_examples())


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args(argv)
    print(json.dumps(jsonable(run_checks()), indent=2, sort_keys=True))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
