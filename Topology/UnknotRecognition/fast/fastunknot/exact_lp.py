"""Exact feasibility certificates for a nonnegative rational kernel.

The producer uses a feasible slack basis and Bland's simplex rule.  It is
finite in exact arithmetic, but no polynomial pivot bound is claimed.
All returned rational numbers use JSON pairs [numerator, denominator].
"""

from fractions import Fraction
from math import gcd, lcm

from .integer_codec import encoded_integer


def _fraction(value):
    if type(value) is Fraction:
        return value
    if type(value) in (list, tuple):
        if len(value) != 2:
            raise ValueError('a rational pair has two integer entries')
        numerator, denominator = map(encoded_integer, value)
        if denominator <= 0:
            raise ValueError('a rational denominator must be positive')
        return Fraction(numerator, denominator)
    return Fraction(encoded_integer(value))


def _pair(value):
    value = Fraction(value)
    return [value.numerator, value.denominator]


def _primitive(vector):
    denominator = 1
    for value in vector:
        denominator = lcm(denominator, value.denominator)
    integers = [int(value * denominator) for value in vector]
    common = 0
    for value in integers:
        common = gcd(common, abs(value))
    return [value // common for value in integers] if common else integers


def _independent_rows(matrix, check):
    """Select original rows spanning the same rational row space.

    Elimination is only the independence test. The simplex receives selected
    original rows, so its dual lifts by inserting zeroes rather than applying
    an unchecked or numerically recovered row transformation.
    """
    echelon, selected = [], []
    for index, original in enumerate(matrix):
        check()
        row = original[:]
        for column, pivot in echelon:
            check()
            factor = row[column]
            if factor:
                row = [x-factor*y for x, y in zip(row, pivot)]
        column = next((j for j, value in enumerate(row) if value), None)
        if column is not None:
            divisor = row[column]
            echelon.append((column, [value/divisor for value in row]))
            selected.append(index)
    return selected


def solve_nonnegative_kernel(matrix, objective, *, max_pivots=None,
                             reduce_rows=True, check=lambda: None):
    """Decide whether C x=0, x>=0 has a point with objective*x>0.

    POSITIVE returns a basic feasible rational vector of the normalized
    polytope C x=0, x>=0, sum(x)<=1 and its primitive integral ray vector.
    NONPOSITIVE returns y with C^T y>=objective.  This homogeneous Farkas
    certificate is enough to exclude positive values on the whole cone.
    INCONCLUSIVE means the shared caller's pivot allowance was exhausted.

    Coefficients may be integers, Fractions, or JSON rational pairs.  The
    method uses C,-C,sum(x)<=1 with a feasible all-slack initial basis.  A
    positive basic solution terminates the search early; it need not attain
    the maximum.  No numerical solver or normal-surface code is used.

    By default an exact original-row basis replaces redundant equalities
    before tableau construction. ``reduce_rows=False`` retains all input rows
    for comparison. Returned duals always have the original row dimension;
    ``equation_rows`` identifies the selected original rows in tableau order.
    Basis slack indices refer to these rows, their negatives, then the sum
    inequality. This polynomial preprocessing does not bound Bland pivots.
    """
    if max_pivots is not None and (type(max_pivots) is not int or max_pivots < 0):
        raise ValueError('max_pivots must be a nonnegative integer or None')
    if type(reduce_rows) is not bool:
        raise ValueError('reduce_rows must be a boolean')
    if type(matrix) not in (list, tuple) or type(objective) not in (list, tuple):
        raise ValueError('matrix and objective must be lists or tuples')
    check()
    c = [_fraction(value) for value in objective]
    n = len(c)
    source = []
    for row in matrix:
        check()
        if type(row) not in (list, tuple) or len(row) != n:
            raise ValueError('matrix rows must have the objective width')
        source.append([_fraction(value) for value in row])
    selected = _independent_rows(source, check) if reduce_rows else list(range(len(source)))
    retained = [source[i] for i in selected]
    r = len(retained)
    inequalities = retained + [[-value for value in row] for row in retained]
    inequalities.append([Fraction(1)] * n)
    m, width = len(inequalities), n + len(inequalities)
    tableau = []
    for i, row in enumerate(inequalities):
        check()
        tableau.append(row + [Fraction(int(i == j)) for j in range(m)])
    rhs = [Fraction(0)] * (m - 1) + [Fraction(1)]
    basis = list(range(n, width))
    reduced = c + [Fraction(0)] * m
    value = Fraction(0)
    pivots = updates = 0

    def stats():
        largest = max((max(abs(x.numerator).bit_length(), x.denominator.bit_length())
                       for row in tableau for x in row), default=0)
        return dict(pivots=pivots, tableau_updates=updates,
                    variables=n, equations=len(source), retained_equations=r, tableau_rows=m,
                    tableau_columns=width, maximum_tableau_bits=largest)

    while True:
        check()
        if value > 0:
            vector = [Fraction(0)] * n
            for i, variable in enumerate(basis):
                if variable < n:
                    vector[variable] = rhs[i]
            if (any(x < 0 for x in vector) or sum(vector) > 1
                    or any(sum(a*x for a, x in zip(row, vector)) for row in source)
                    or sum(a*x for a, x in zip(c, vector)) != value):
                raise ArithmeticError('simplex produced an invalid positive basic point')
            check()
            return dict(status='POSITIVE', x=[_pair(x) for x in vector],
                        primitive_x=_primitive(vector), objective=_pair(value),
                        basis=basis, equation_rows=selected, stats=stats())
        entering = next((j for j, coefficient in enumerate(reduced)
                         if coefficient > 0), None)
        if entering is None:
            dual = [-reduced[n+i] for i in range(m)]
            y = [Fraction(0)]*len(source)
            for i, original in enumerate(selected):
                y[original] = dual[i] - dual[r+i]
            if (value != 0 or any(x < 0 for x in dual) or dual[-1] != 0
                    or any(sum(source[i][j]*y[i] for i in range(len(source))) < c[j]
                           for j in range(n))):
                raise ArithmeticError('simplex produced an invalid homogeneous dual')
            check()
            return dict(status='NONPOSITIVE', y=[_pair(x) for x in y],
                        equation_rows=selected, stats=stats())
        if max_pivots is not None and pivots >= max_pivots:
            check()
            return dict(status='INCONCLUSIVE', reason='LP pivot allowance exhausted',
                        equation_rows=selected, stats=stats())
        candidates = [i for i in range(m) if tableau[i][entering] > 0]
        if not candidates:
            raise ArithmeticError('the normalized kernel LP cannot be unbounded')
        leaving = min(candidates, key=lambda i: (rhs[i]/tableau[i][entering], basis[i]))
        pivot = tableau[leaving][entering]
        tableau[leaving] = [x/pivot for x in tableau[leaving]]
        rhs[leaving] /= pivot
        updates += width + 1
        for i in range(m):
            check()
            if i == leaving:
                continue
            factor = tableau[i][entering]
            if factor:
                tableau[i] = [x-factor*y for x, y
                              in zip(tableau[i], tableau[leaving])]
                rhs[i] -= factor*rhs[leaving]
                updates += width + 1
        factor = reduced[entering]
        reduced = [x-factor*y for x, y in zip(reduced, tableau[leaving])]
        value += factor*rhs[leaving]
        updates += width + 1
        basis[leaving] = entering
        pivots += 1
