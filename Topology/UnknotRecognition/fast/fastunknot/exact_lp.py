"""Exact feasibility certificates for a nonnegative rational kernel.

The default caps a Dantzig/full-slack-lex feasible-basis prefix polynomially,
then uses a rational ellipsoid fallback with exact point/ray/dual recovery.
The explicit policy='bland' comparison mode retains legacy pivot behavior.
All returned rational numbers use JSON pairs [numerator, denominator].
"""

from dataclasses import dataclass
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


F = Fraction


@dataclass(frozen=True, slots=True)
class _PreparedKernelMatrix:
    """Private immutable input shared by objectives of one kernel problem.

    These are the parsed original rows, not their row-reduced replacements.
    The public solver accepts raw matrices only; callers inside this package
    obtain this context through _prepare_kernel_matrix.
    """
    width: int
    source: tuple
    selected: tuple
    reduce_rows: bool


def _parse_kernel_matrix(matrix, width, reduce_rows, check):
    """Parse rows after the caller's entry checks, preserving their order."""
    source = []
    for row in matrix:
        check()
        if type(row) not in (list, tuple) or len(row) != width:
            raise ValueError('matrix rows must have the objective width')
        source.append(tuple(_fraction(value) for value in row))
    selected = _independent_rows(source, check) if reduce_rows else list(range(len(source)))
    return _PreparedKernelMatrix(width, tuple(source), tuple(selected), reduce_rows)


def _prepare_kernel_matrix(matrix, width, *, reduce_rows=True, check=lambda: None):
    """Validate and select original rows once, without solving an objective."""
    if type(width) is not int or width < 0:
        raise ValueError('matrix width must be a nonnegative integer')
    if type(reduce_rows) is not bool:
        raise ValueError('reduce_rows must be a boolean')
    if not callable(check):
        raise ValueError('check must be callable')
    if type(matrix) not in (list, tuple):
        raise ValueError('matrix must be a list or tuple')
    check()
    return _parse_kernel_matrix(matrix, width, reduce_rows, check)


def _dantzig_entering(reduced, check):
    """Largest positive real reduced cost, with the least-index tie break."""
    entering = None
    for j, coefficient in enumerate(reduced):
        check()
        if coefficient > 0 and (entering is None or coefficient > reduced[entering]):
            entering = j
    return entering


def _lexicographic_leaving(candidates, tableau, rhs, column, n, check):
    """Compare RHS then the full original slack block, divided by the pivot.

    The original slack block is B^-1, including currently basic slacks.
    Positive entering coefficients allow exact cross multiplication of each
    component. Only the first unequal component matters; no Fraction ratios
    or entire key tuples are allocated. The state is local to this call.
    """
    best = None
    m = len(tableau)
    for i in candidates:
        check()
        if best is None:
            best = i
            continue
        a, b = tableau[i][column], tableau[best][column]
        an, ad = a.numerator, a.denominator
        bn, bd = b.numerator, b.denominator
        for j in range(-1, m):
            check()
            x = rhs[i] if j < 0 else tableau[i][n+j]
            y = rhs[best] if j < 0 else tableau[best][n+j]
            # x/a < y/b iff xn*ad*yd*bn < yn*bd*xd*an;
            # every denominator and both pivot numerators are positive.
            left = x.numerator * ad * y.denominator * bn
            right = y.numerator * bd * x.denominator * an
            if left < right:
                best = i
                break
            if left > right:
                break
    return best


def _solve_prepared_kernel(source, c, selected, *, max_pivots, check,
                           pivot_rule='bland'):
    """Run one fresh exact tableau with a call-local pivot rule."""
    if type(pivot_rule) is not str or pivot_rule not in ('bland', 'dantzig_lex'):
        raise ValueError('unsupported private pivot rule')
    n = len(c)
    retained = [source[i] for i in selected]
    r = len(retained)
    inequalities = retained + [[-value for value in row] for row in retained]
    inequalities.append([Fraction(1)] * n)
    m, width = len(inequalities), n + len(inequalities)
    tableau = []
    for i, row in enumerate(inequalities):
        check()
        tableau.append([*row, *(Fraction(int(i == j)) for j in range(m))])
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
        if pivot_rule == 'bland':
            entering = next((j for j, coefficient in enumerate(reduced)
                         if coefficient > 0), None)
        else:
            entering = _dantzig_entering(reduced, check)
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
        if pivot_rule == 'bland':
            leaving = min(candidates, key=lambda i: (rhs[i]/tableau[i][entering], basis[i]))
        else:
            leaving = _lexicographic_leaving(candidates, tableau, rhs, entering, n, check)
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


def dot(left, right):
    return sum((a*b for a, b in zip(left, right)), F(0))


def _cap(name, value):
    if value is not None and (type(value) is not int or value < 0):
        raise ValueError(name+' must be a nonnegative integer or None')


def _integer_vector(values, check):
    scale = 1
    for value in values:
        check()
        scale = lcm(scale, value.denominator)
    integers = []
    for value in values:
        check()
        integers.append(int(value*scale))
    return integers, scale


def _complete_basis(retained, n, support, check):
    inequalities = retained+[[ -a for a in row] for row in retained]+[[F(1)]*n]
    m = len(inequalities)
    columns = []
    for j in range(n+m):
        check()
        columns.append([row[j] if j < n else F(int(j-n == i))
                        for i, row in enumerate(inequalities)])
    seen = set(support)
    order = list(support)+[j for j in range(n+m) if j not in seen]
    indices = _independent_rows([columns[j] for j in order], check)
    basis = [order[i] for i in indices]
    if len(basis) != m or not seen.issubset(basis):
        raise ArithmeticError('positive support did not complete to a slack basis')
    return basis


def _replay_fallback(source, cost, answer, check):
    """Exact checks, including the full cone extremality postcondition."""
    check()
    n = len(cost)
    if answer['status'] == 'NONPOSITIVE':
        y = [_fraction(value) for value in answer['y']]
        if len(y) != len(source):
            raise ArithmeticError('dual dimension mismatch')
        for j in range(n):
            check()
            if sum((row[j]*a for row, a in zip(source, y)), F(0)) < cost[j]:
                raise ArithmeticError('original-row dual inequality failed')
        return
    if answer['status'] != 'POSITIVE':
        return
    x = [_fraction(value) for value in answer['x']]
    ray = answer['primitive_x']
    if (len(x) != n or len(ray) != n or any(a < 0 for a in x)
            or sum(x, F(0)) != 1 or any(type(a) is not int or a < 0 for a in ray)
            or not any(ray)):
        raise ArithmeticError('invalid normalized positive vector')
    total, divisor = sum(ray), 0
    for value, coordinate in zip(ray, x):
        check()
        divisor = gcd(divisor, value)
        if coordinate != F(value, total):
            raise ArithmeticError('primitive ray and normalized point disagree')
    if divisor != 1:
        raise ArithmeticError('ray is not primitive')
    for row in source:
        check()
        if dot(row, x):
            raise ArithmeticError('original-row primal equation failed')
    value = dot(cost, x)
    if value <= 0 or value != _fraction(answer['objective']):
        raise ArithmeticError('positive objective replay failed')
    support = [j for j, a in enumerate(x) if a]
    restricted = []
    for row in source:
        check()
        restricted.append([row[j] for j in support])
    if len(support)-len(_independent_rows(restricted, check)) != 1:
        raise ArithmeticError('positive output is not an extreme kernel ray')
    selected = answer['equation_rows']
    m = 2*len(selected)+1
    basis = answer['basis']
    if (len(basis) != m or len(set(basis)) != m
            or any(type(j) is not int or not 0 <= j < n+m for j in basis)
            or not set(support).issubset(basis)):
        raise ArithmeticError('positive basis has wrong support or dimension')
    inequalities = [source[i] for i in selected]
    inequalities += [[-a for a in row] for row in inequalities]
    inequalities.append([F(1)]*n)
    columns = []
    for j in basis:
        check()
        columns.append([row[j] if j < n else F(int(j-n == i))
                        for i, row in enumerate(inequalities)])
    if len(_independent_rows(columns, check)) != m:
        raise ArithmeticError('positive slack basis is singular')
    check()


def _ellipsoid_kernel(source, cost, selected, stats, *, reduce_rows,
                      max_ellipsoid_iterations, max_feasibility_calls, check):
    # Keep fallback-only dependencies off the common simplex path.
    from types import SimpleNamespace
    from .bounded_lp import Budget, find_point, prepare
    from .source_kernel import SourceKernel

    independent = selected if reduce_rows else _independent_rows(source, check)
    n, r = len(cost), len(independent)
    stats['fallback_used'] = 1
    budget = Budget(maximum=max_ellipsoid_iterations,
                    maximum_decisions=max_feasibility_calls, check=check)

    def finish(result):
        stats.update(ellipsoid_iterations=budget.iterations,
                     feasibility_calls=budget.decisions,
                     maximum_ellipsoid_precision=budget.maximum_precision,
                     maximum_ellipsoid_dimension=budget.maximum_dimension,
                     maximum_planned_ellipsoid_iterations=budget.maximum_planned_iterations)
        result.update(stats=stats, equation_rows=selected)
        _replay_fallback(source, cost, result, check)
        return result

    integer_matrix, row_scales = [], []
    height = 1
    for index in independent:
        check()
        row, scale = _integer_vector(source[index], check)
        integer_matrix.append(row)
        row_scales.append(scale)
        height = max(height, max(map(abs, row), default=0))
    integer_cost, cost_scale = _integer_vector(cost, check)
    height = max(height, max(map(abs, integer_cost), default=0))
    # The equality system Cx=0,cx=1 has a nonnegative basic feasible point
    # with at most min(n,r+1) nonzero variables and determinant-bounded size.
    k = min(n, r+1)
    primal_radius = (max(k, 1)*height)**k
    lhs, rhs = [], []
    for row in integer_matrix:
        check()
        lhs.extend((row, [-a for a in row]))
        rhs.extend((0, 0))
    for j in range(n):
        check()
        row = [0]*n
        row[j] = -1
        lhs.append(row)
        rhs.append(0)
    lhs.extend((integer_cost, [-a for a in integer_cost]))
    rhs.extend((1, -1))
    primal = find_point(prepare(lhs, rhs, n, primal_radius, check=check), budget)
    if primal['status'] == 'INCONCLUSIVE':
        return finish(dict(status='INCONCLUSIVE', reason=primal['reason']))
    if primal['status'] == 'FEASIBLE':
        check()
        kernel = SourceKernel(SimpleNamespace(n=n, equations=integer_matrix,
                                              conflicts=()), check=check)
        witness = kernel.extreme_witness(primal['point'], cost, check=check)
        ray = list(witness['coordinates'])
        total = sum(ray)
        x = [F(value, total) for value in ray]
        stats['support_descent_steps'] = witness['descent_steps']
        support = [j for j, value in enumerate(ray) if value]
        basis = _complete_basis([source[i] for i in selected], n, support, check)
        return finish(dict(status='POSITIVE', x=[_pair(a) for a in x],
                           primitive_x=ray, objective=_pair(dot(cost, x)), basis=basis))
    # C has independent rows, so its dual inequality polyhedron is pointed.
    # A feasible vertex uses r independent tight inequalities. Cramer's rule
    # gives radius (rH)^r. Row/cost scales map its dual back to original C.
    dual_radius = (max(r, 1)*height)**r
    lhs, rhs = [], []
    for j in range(n):
        check()
        lhs.append([-row[j] for row in integer_matrix])
        rhs.append(-integer_cost[j])
    dual = find_point(prepare(lhs, rhs, r, dual_radius, check=check), budget)
    if dual['status'] == 'INCONCLUSIVE':
        return finish(dict(status='INCONCLUSIVE', reason=dual['reason']))
    if dual['status'] != 'FEASIBLE':
        raise ArithmeticError('both exact homogeneous alternatives were infeasible')
    y = [F(0)]*len(source)
    for i, index in enumerate(independent):
        check()
        y[index] = dual['point'][i]*F(row_scales[i], cost_scale)
    return finish(dict(status='NONPOSITIVE', y=[_pair(a) for a in y]))


def _validate_kernel_controls(*, max_pivots, reduce_rows, policy,
                              fast_path_pivots, max_ellipsoid_iterations,
                              max_feasibility_calls, check):
    for name, value in (('max_pivots', max_pivots),
                        ('fast_path_pivots', fast_path_pivots),
                        ('max_ellipsoid_iterations', max_ellipsoid_iterations),
                        ('max_feasibility_calls', max_feasibility_calls)):
        _cap(name, value)
    if type(reduce_rows) is not bool:
        raise ValueError('reduce_rows must be a boolean')
    if type(policy) is not str or policy not in ('polynomial', 'bland'):
        raise ValueError('policy must be polynomial or bland')
    if not callable(check):
        raise ValueError('check must be callable')
    if policy == 'bland' and any(value is not None for value in (
            fast_path_pivots, max_ellipsoid_iterations, max_feasibility_calls)):
        raise ValueError('fallback controls require polynomial policy')


def _run_kernel_policy(prepared, cost, *, max_pivots, policy,
                       fast_path_pivots, max_ellipsoid_iterations,
                       max_feasibility_calls, check):
    """Run one fresh tableau/fallback; only immutable matrix data are shared."""
    source, n = prepared.source, prepared.width
    # Returned equation_rows must be a fresh literal list, never context data.
    selected = list(prepared.selected)
    if policy == 'bland':
        return _solve_prepared_kernel(source, cost, selected,
                                     max_pivots=max_pivots, check=check)
    polynomial_limit = (n+len(selected)+1)**2
    fast_limit = polynomial_limit
    if fast_path_pivots is not None:
        fast_limit = min(fast_limit, fast_path_pivots)
    actual_limit = fast_limit if max_pivots is None else min(fast_limit, max_pivots)
    answer = _solve_prepared_kernel(source, cost, selected,
                                   max_pivots=actual_limit, check=check,
                                   pivot_rule='dantzig_lex')
    stats = answer['stats']
    stats.update(polynomial_pivot_limit=polynomial_limit,
                 fast_path_pivot_limit=fast_limit, fallback_used=0,
                 ellipsoid_iterations=0, feasibility_calls=0,
                 maximum_ellipsoid_precision=0, maximum_ellipsoid_dimension=0,
                 maximum_planned_ellipsoid_iterations=0, support_descent_steps=0)
    if answer['status'] != 'INCONCLUSIVE':
        return answer
    if max_pivots is not None and stats['pivots'] >= max_pivots:
        return answer
    return _ellipsoid_kernel(source, cost, selected, stats, reduce_rows=prepared.reduce_rows,
                             max_ellipsoid_iterations=max_ellipsoid_iterations,
                             max_feasibility_calls=max_feasibility_calls, check=check)


def _solve_prepared_nonnegative_kernel(prepared, objective, *, max_pivots=None,
                                       policy='polynomial', fast_path_pivots=None,
                                       max_ellipsoid_iterations=None,
                                       max_feasibility_calls=None, check=lambda: None):
    """Private objective solve against one previously validated matrix.

    Controls, objective coefficients, tableau, budgets and result data are
    fresh for every call. No row selection or mutable solver state is reused
    across a different prepared matrix.
    """
    if type(prepared) is not _PreparedKernelMatrix:
        raise ValueError('expected a prepared kernel matrix')
    _validate_kernel_controls(max_pivots=max_pivots, reduce_rows=prepared.reduce_rows,
        policy=policy, fast_path_pivots=fast_path_pivots,
        max_ellipsoid_iterations=max_ellipsoid_iterations,
        max_feasibility_calls=max_feasibility_calls, check=check)
    if type(objective) not in (list, tuple):
        raise ValueError('objective must be a list or tuple')
    check()
    cost = [_fraction(value) for value in objective]
    if len(cost) != prepared.width:
        raise ValueError('objective must have the prepared matrix width')
    return _run_kernel_policy(prepared, cost, max_pivots=max_pivots, policy=policy,
        fast_path_pivots=fast_path_pivots,
        max_ellipsoid_iterations=max_ellipsoid_iterations,
        max_feasibility_calls=max_feasibility_calls, check=check)


def solve_nonnegative_kernel(matrix, objective, *, max_pivots=None,
                             reduce_rows=True, policy='polynomial',
                             fast_path_pivots=None,
                             max_ellipsoid_iterations=None,
                             max_feasibility_calls=None, check=lambda: None):
    """Decide Cx=0,x>=0,cx>0 with an exact extreme ray or original-row dual.

    Coefficients accept the existing exact integer/Fraction/JSON-pair forms.
    POSITIVE retains the normalized basic-point, primitive-ray, and slack
    basis fields; NONPOSITIVE retains C^T y>=c on all original input rows.

    The default caps Dantzig/full-slack lex at (n+retained_rows+1)^2 pivots,
    optionally lowered by fast_path_pivots, then invokes polynomial exact
    bounded feasibility.
    policy='bland' preserves the legacy uncapped comparison implementation.
    max_pivots is always a hard USER allowance: exhausting it prevents a
    fallback. The internal polynomial prefix limit is not a user allowance.
    Ellipsoid updates and feasibility calls have separate shared per-query
    caps/counters; neither is charged as a simplex pivot. Finite exhausted
    work caps return INCONCLUSIVE with no partial mathematical certificate.

    Parsing and original-row selection occur once. Conclusive fast-path
    results use the existing tableau invariant and full original-source
    checks. Only fallback results perform additional support-rank/basis
    replay. Caller callback exceptions propagate unchanged.
    """
    _validate_kernel_controls(max_pivots=max_pivots, reduce_rows=reduce_rows,
        policy=policy, fast_path_pivots=fast_path_pivots,
        max_ellipsoid_iterations=max_ellipsoid_iterations,
        max_feasibility_calls=max_feasibility_calls, check=check)
    if type(matrix) not in (list, tuple) or type(objective) not in (list, tuple):
        raise ValueError('matrix and objective must be lists or tuples')
    check()
    cost = [_fraction(value) for value in objective]
    prepared = _parse_kernel_matrix(matrix, len(cost), reduce_rows, check)
    return _run_kernel_policy(prepared, cost, max_pivots=max_pivots, policy=policy,
        fast_path_pivots=fast_path_pivots,
        max_ellipsoid_iterations=max_ellipsoid_iterations,
        max_feasibility_calls=max_feasibility_calls, check=check)
