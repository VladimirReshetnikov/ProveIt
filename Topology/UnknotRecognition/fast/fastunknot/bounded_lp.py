"""Polynomial exact bounded feasibility with rational outward rounding.

The determinant gap, dyadic containment, iteration bound, and exact face
recovery are proved in synthesis/exact_polynomial_lp.tex. Relaxed ellipsoid
centres are never returned as original-system witnesses. This module uses
only standard-library exact arithmetic and shares caller limits across all
feasibility decisions and recovery cuts.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from math import gcd, isqrt, lcm


def rational(value):
    if type(value) not in (int, F):
        raise ValueError('exact int or Fraction required')
    return F(value)


def dot(left, right):
    return sum((a*b for a, b in zip(left, right)), F(0))


def ceil_log2(value):
    value = F(value)
    if value <= 0:
        raise ValueError('positive argument required')
    a, b = value.numerator, value.denominator
    result = a.bit_length()-b.bit_length()
    below = a > (b << result) if result >= 0 else (a << -result) > b
    return result+int(below)


def integer_row(row, rhs, *, check=lambda: None):
    values = []
    denominator = 1
    for value in (*row, rhs):
        check()
        value = rational(value)
        values.append(value)
        denominator = lcm(denominator, value.denominator)
    integers, divisor = [], 0
    for value in values:
        check()
        value = int(value*denominator)
        integers.append(value)
        divisor = gcd(divisor, abs(value))
    divisor = divisor or 1
    return tuple(x//divisor for x in integers[:-1]), integers[-1]//divisor


@dataclass
class Budget:
    maximum: int | None = None
    iterations: int = 0
    decisions: int = 0
    check: object = lambda: None
    maximum_decisions: int | None = None
    maximum_precision: int = 0
    maximum_dimension: int = 0
    maximum_planned_iterations: int = 0

    def __post_init__(self):
        for name in ('maximum', 'maximum_decisions'):
            value = getattr(self, name)
            if value is not None and (type(value) is not int or value < 0):
                raise ValueError(name+' must be a nonnegative integer or None')
        if not callable(self.check):
            raise ValueError('check must be callable')


@dataclass(frozen=True)
class System:
    dimension: int
    radius: F
    rows: tuple


def prepare(matrix, rhs, dimension, radius, *, check=lambda: None):
    check()
    if type(dimension) is not int or dimension < 0:
        raise ValueError('nonnegative dimension required')
    radius = rational(radius)
    if radius < 0 or len(matrix) != len(rhs):
        raise ValueError('invalid bounds or row count')
    rows = []
    for row, value in zip(matrix, rhs):
        check()
        if len(row) != dimension:
            raise ValueError('wrong row width')
        rows.append(integer_row(row, value, check=check))
    for j in range(dimension):
        check()
        for sign in (1, -1):
            row = [0]*dimension
            row[j] = sign
            rows.append(integer_row(row, radius, check=check))
    return System(dimension, radius, tuple(rows))


def ceil_divide_sqrt(value, square):
    """Exact ceil(value/sqrt(square)) using integer square root only."""
    if square <= 0:
        raise ArithmeticError('positive square required')
    if not value:
        return 0
    ratio = value*value/square
    floor = isqrt(ratio.numerator//ratio.denominator)
    if value < 0:
        return -floor
    exact = floor*floor*ratio.denominator == ratio.numerator
    return floor+int(not exact)


def decide(system, budget=None, *, observer=None):
    """Exact FEASIBLE/INFEASIBLE decision, or INCONCLUSIVE under shared caps.

    The relaxed_point, when present, belongs only to the perturbed system.
    It is never advertised as an exact original feasible point.
    """
    budget = Budget() if budget is None else budget
    budget.check()
    if budget.maximum_decisions is not None and budget.decisions >= budget.maximum_decisions:
        return dict(status='INCONCLUSIVE', iterations=0,
                    reason='shared feasibility decision allowance exhausted')
    budget.decisions += 1
    d, radius, rows = system.dimension, system.radius, system.rows
    budget.maximum_dimension = max(d, budget.maximum_dimension)
    height = 1
    for row, rhs in rows:
        budget.check()
        if not any(row) and rhs < 0:
            return dict(status='INFEASIBLE', iterations=0, reason='constant contradiction')
        height = max(height, max((abs(a) for a in row), default=0))
    if d == 0:
        return dict(status='FEASIBLE', relaxed_point=[], iterations=0)
    if d == 1:
        lower, upper = -radius, radius
        for row, rhs in rows:
            budget.check()
            if row[0] > 0:
                upper = min(upper, F(rhs, row[0]))
            elif row[0] < 0:
                lower = max(lower, F(rhs, row[0]))
        return (dict(status='INFEASIBLE', iterations=0, reason='empty interval')
                if lower > upper else
                dict(status='FEASIBLE', relaxed_point=[lower], iterations=0))

    determinant = ((d+1)*height)**(d+1)
    epsilon = F(1, 2*determinant)
    inner = epsilon/(d*height)
    outer = d*(radius+1)
    limit = 4*d*d*(ceil_log2(outer/inner)+1)
    budget.maximum_planned_iterations = max(limit, budget.maximum_planned_iterations)
    precision_offset = ceil_log2(200*d**3)
    rho = F(1, 100*d*d)
    inflation = (1+rho)**2
    center = [F(0)]*d
    shape = [[outer*outer if i == j else F(0) for j in range(d)] for i in range(d)]
    # Initial shape need not be dyadic; every subsequent shape is rounded.
    start, precision = budget.iterations, 0
    for step in range(limit):
        budget.check()
        separating = None
        for row, rhs in rows:
            budget.check()
            if dot(row, center) > rhs+epsilon:
                separating = row
                break
        if separating is None:
            return dict(status='FEASIBLE', relaxed_point=center,
                        iterations=budget.iterations-start, planned_iterations=limit,
                        precision=precision, epsilon=epsilon)
        if budget.maximum is not None and budget.iterations >= budget.maximum:
            return dict(status='INCONCLUSIVE', iterations=budget.iterations-start,
                        reason='shared ellipsoid iteration allowance exhausted')
        # At cut i, lambda_min(Q*) >= R^2 4^(-(i+1)). Nested grids
        # make the old dyadic center integral on this finer grid.
        precision = 2*(step+1)+precision_offset
        budget.maximum_precision = max(precision, budget.maximum_precision)
        scale, grid = 1 << precision, F(1, 1 << precision)
        normal = separating
        image = []
        for row in shape:
            budget.check()
            image.append(dot(row, normal))
        square = dot(normal, image)
        if square <= 0:
            raise ArithmeticError('ellipsoid lost positive definiteness')
        next_center = []
        for i in range(d):
            budget.check()
            old = center[i]*scale
            if old.denominator != 1:
                raise ArithmeticError('nested dyadic center invariant failed')
            change = ceil_divide_sqrt(scale*image[i]/(d+1), square)
            next_center.append(F(old.numerator-change, scale))
        next_shape, ideal_shape = [], []
        for i in range(d):
            budget.check()
            next_row, ideal_row = [], []
            for j in range(d):
                budget.check()
                ideal = F(d*d, d*d-1)*(shape[i][j]-F(2, d+1)*image[i]*image[j]/square)
                ideal_row.append(ideal)
                inflated = inflation*ideal
                rounded = (inflated.numerator*scale)//inflated.denominator
                if i == j:
                    rounded += d
                next_row.append(F(rounded, scale))
            next_shape.append(next_row)
            ideal_shape.append(ideal_row)
        if observer is not None:
            observer(dict(step=step, old_shape=shape, ideal_shape=ideal_shape,
                          new_shape=next_shape, old_center=center,
                          new_center=next_center, rho=rho, grid=grid,
                          spectral_floor=outer*outer/F(4)**(step+1)))
        center, shape = next_center, next_shape
        budget.iterations += 1
    budget.check()
    return dict(status='INFEASIBLE', iterations=budget.iterations-start,
                planned_iterations=limit, precision=precision, epsilon=epsilon,
                reason='certified volume cutoff')


def independent_equations(equations, dimension, *, check=lambda: None):
    pivots = {}
    for coefficients, rhs in equations:
        check()
        row = list(map(F, coefficients))+[F(rhs)]
        for j, pivot in pivots.items():
            check()
            if row[j]:
                multiple = row[j]
                row = [a-multiple*b for a, b in zip(row, pivot)]
        column = next((j for j in range(dimension) if row[j]), None)
        if column is None:
            if row[-1]:
                raise ArithmeticError('retained equalities are inconsistent')
            continue
        multiple = row[column]
        row = [x/multiple for x in row]
        pivots[column] = row
    return pivots


def find_point(system, budget=None):
    """Recover an exact vertex by a maximal feasible tight-row face."""
    budget = Budget() if budget is None else budget
    first = decide(system, budget)
    if first['status'] != 'FEASIBLE':
        return first
    if system.dimension == 0:
        return dict(status='FEASIBLE', point=[], retained_equalities=[])
    rows, equalities, pivots = list(system.rows), [], {}
    for row, rhs in system.rows:
        budget.check()
        opposite = (tuple(-x for x in row), -rhs)
        answer = decide(System(system.dimension, system.radius, tuple(rows+[opposite])), budget)
        if answer['status'] == 'INCONCLUSIVE':
            return answer
        if answer['status'] == 'FEASIBLE':
            rows.append(opposite)
            equalities.append((row, rhs))
            pivots = independent_equations(equalities, system.dimension, check=budget.check)
            if len(pivots) == system.dimension:
                break
    if len(pivots) != system.dimension:
        raise ArithmeticError('maximal tight-row face did not become a point')
    point = [F(0)]*system.dimension
    for column, row in reversed(tuple(pivots.items())):
        budget.check()
        point[column] = row[-1]-dot(row[:system.dimension], point)
    for row, rhs in system.rows:
        budget.check()
        if dot(row, point) > rhs:
            raise ArithmeticError('recovered vertex is not feasible')
    budget.check()
    return dict(status='FEASIBLE', point=point, retained_equalities=equalities)
