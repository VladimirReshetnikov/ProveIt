"""Reusable exact source kernel and monotone positive support descent.

For a feasible positive vector, normalize sum(x)=1 and work in one fixed
free-coordinate chart x=Kz of the matching kernel.  Tangent directions satisfy
the initially zero coordinate forms and sum(Kz)=0.  A step along a direction
of nonnegative objective slope reaches a new coordinate face.  Each new zero
restricts the tangent chart by one rank-one elimination, or is redundant.

Chart rows retain an identity submatrix at their surviving free coordinates;
they are never individually rescaled to primitive integer rows.  Therefore
they remain the canonical solutions associated with a subsystem of the
accumulated constraints, with determinant-bounded rational bit lengths.  Only
the emitted direction in original source coordinates is made primitive.

The number of steps is at most the initial tangent dimension, at most h-1
for matching nullity h.  Kernel preparation and each query use polynomial
exact arithmetic.  This finds a positive admissible extreme ray from a given
positive vector; it makes no claim about essentiality or finding that vector.
"""
from collections.abc import Mapping, Set
from dataclasses import dataclass
from fractions import Fraction as Q
from math import gcd, lcm

from .port_subspace import _q as _exact_q, _dot, _rref


def _items(values):
    if isinstance(values, (str, bytes, bytearray, Mapping, Set)):
        raise ValueError('ordered coordinate iterable required')
    return iter(values)


def _q(value):
    try:
        return _exact_q(value)
    except (ZeroDivisionError, OverflowError) as exc:
        raise ValueError('invalid exact rational') from exc


def _zeros(values):
    if isinstance(values, (str, bytes, bytearray, Mapping)):
        raise ValueError('coordinate-zero index iterable required')
    return tuple(values)


def _chart(rows, width, check):
    """Kernel basis with an identity submatrix at the returned free columns."""
    reduced, pivots = _rref(rows, width, check)
    pivot_set = set(pivots)
    free = tuple(j for j in range(width) if j not in pivot_set)
    basis = []
    for j in free:
        check()
        v = [Q(0)]*width
        v[j] = Q(1)
        for row, p in zip(reduced, pivots):
            v[p] = -row[j]
        basis.append(tuple(v))
    return tuple(basis), free


def _restrict_chart(basis, free, form, check):
    """Intersect an identity-chart basis with one homogeneous linear form."""
    coefficients = []
    for row in basis:
        check()
        coefficients.append(_dot(form, row))
    pivot = next((i for i, a in enumerate(coefficients) if a), None)
    if pivot is None:
        return basis, free
    updated = []
    for i, row in enumerate(basis):
        check()
        if i != pivot:
            scale = coefficients[i]/coefficients[pivot]
            updated.append(tuple(a-scale*b for a, b in zip(row, basis[pivot])))
    return tuple(updated), free[:pivot]+free[pivot+1:]


def _primitive(vector, check):
    denominator = 1
    for x in vector:
        check()
        denominator = lcm(denominator, x.denominator)
    integers = tuple(int(x*denominator) for x in vector)
    divisor = 0
    for x in integers:
        check()
        divisor = gcd(divisor, abs(x))
    return tuple(x//divisor for x in integers) if divisor else integers


@dataclass(frozen=True, init=False)
class SourceKernel:
    """Immutable validated source snapshot and reusable matching kernel.

    Source input supplies ``n``, ``equations`` and ``conflicts`` attributes.
    Exact coefficients may be integers, rational strings or Fractions;
    booleans and floating-point values are rejected.
    """
    n: int
    equations: tuple
    conflicts: tuple
    basis: tuple
    free_coordinates: tuple
    forms: tuple
    sum_form: tuple

    def __init__(self, source, *, check=lambda: None):
        check()
        try:
            n, source_rows, source_conflicts = source.n, source.equations, source.conflicts
        except AttributeError as exc:
            raise ValueError('source must supply n, equations and conflicts') from exc
        if type(n) is not int or n < 1:
            raise ValueError('positive source coordinate count required')
        equations = []
        for row in _items(source_rows):
            check()
            row = tuple(_q(x) for x in _items(row))
            if len(row) != n:
                raise ValueError('source matrix width mismatch')
            equations.append(row)
        conflicts = set()
        for pair in _items(source_conflicts):
            check()
            pair = tuple(_items(pair))
            if (len(pair) != 2 or any(type(j) is not int or not 0 <= j < n for j in pair)
                    or pair[0] == pair[1]):
                raise ValueError('invalid source conflict pair')
            conflicts.add(tuple(sorted(pair)))
        basis, free = _chart(tuple(equations), n, check)
        forms = []
        for j in range(n):
            check()
            forms.append(tuple(row[j] for row in basis))
        values = dict(n=n, equations=tuple(equations), conflicts=tuple(sorted(conflicts)),
                      basis=basis, free_coordinates=free, forms=tuple(forms),
                      sum_form=tuple(sum(row, Q(0)) for row in basis))
        for name, value in values.items():
            object.__setattr__(self, name, value)

    @property
    def nullity(self):
        return len(self.basis)

    def extreme_witness(self, x, objective, *, zeros=(), check=lambda: None):
        """Return a positive primitive extreme ray inside the supplied support.

        The positive input is checked against the cached exact source chart.
        All initial coordinate zeros, including requested zeros, are retained.
        Compatibility is retained by decreasing support.  Callback exceptions
        propagate unchanged from preparation, validation and descent.
        """
        check()
        x = tuple(_q(v) for v in _items(x))
        c = tuple(_q(v) for v in _items(objective))
        zeros = _zeros(zeros)
        if (len(x) != self.n or len(c) != self.n or not any(x) or any(v < 0 for v in x)):
            raise ValueError('invalid source vector or objective dimension')
        if any(type(j) is not int or not 0 <= j < self.n for j in zeros):
            raise ValueError('invalid source zero coordinate')
        if any(x[j] for j in zeros):
            raise ValueError('requested source zero does not vanish')
        parameters = tuple(x[j] for j in self.free_coordinates)
        for row, coordinate in zip(self.forms, x):
            check()
            if _dot(row, parameters) != coordinate:
                raise ValueError('source matching equations fail')
        for a, b in self.conflicts:
            check()
            if x[a] and x[b]:
                raise ValueError('source compatibility fails')
        if _dot(c, x) <= 0:
            raise ValueError('positive source objective required')
        total = sum(x, Q(0))
        x = tuple(v/total for v in x)
        constraints = tuple(self.forms[j] for j, v in enumerate(x) if not v)+(self.sum_form,)
        directions, free = _chart(constraints, self.nullity, check)
        initial_dimension = len(directions)
        steps = 0
        while directions:
            check()
            direction = []
            for row in self.forms:
                check()
                direction.append(_dot(row, directions[0]))
            direction = _primitive(direction, check)
            if _dot(c, direction) < 0:
                direction = tuple(-v for v in direction)
            step = min(x[j]/(-v) for j, v in enumerate(direction) if v < 0)
            updated = tuple(a+step*v for a, v in zip(x, direction))
            killed = tuple(j for j, (a, b) in enumerate(zip(x, updated)) if a and not b)
            old_dimension = len(directions)
            for j in killed:
                check()
                directions, free = _restrict_chart(directions, free, self.forms[j], check)
            if len(directions) >= old_dimension:
                raise ArithmeticError('support step failed to decrease tangent dimension')
            x = updated
            steps += 1
        check()
        return dict(coordinates=_primitive(x, check), descent_steps=steps,
                    nullity=self.nullity, initial_direction_dimension=initial_dimension)
