"""Opt-in maximal matching support from exact primal/dual certificates.

The feasibility system Ax=0, y=A^T*lambda, x,y>=0, x+y>=1 always has a
rational solution. Its supports partition all coordinates and identify the
maximal support of the nonnegative matching cone. A polynomial-time rational
LP oracle would make this a polynomial preprocessing theorem. The optional
SciPy/HiGHS proposal and SymPy rational simplex used here do NOT establish a
polynomial worst-case bound for this implementation. Numerical proposals are
reconstructed in exact rational subspaces and independently checked; exact
solver output is also checked. Solver failure returns INCONCLUSIVE.

No existing default is changed. The opt-in discovery adapter falls back to
the incumbent on unproved reduction, and preserves original-sector proofs.
Our loops honor check. Third-party LP calls honor check immediately before
and after a call, but cannot call it during their internal solve. No result
or cache is published before the post-solver cancellation check.
"""

from copy import deepcopy
from fractions import Fraction
from hashlib import sha256
import json
from math import gcd, isfinite, lcm

from .integer_codec import json_safe
from .normal_sector import _nullspace, _rref, _source_hash
from .sector_matching_support import _kernel_equations, _source_constraints
from .sector_sparse import PreparedSectorSource
from .sector_window_basis import canonical_matching_basis


def _input_matrix(matrix, width):
    if type(matrix) not in (list, tuple):
        raise ValueError('matrix must be a sequence of rational rows')
    if width is None:
        width = len(matrix[0]) if matrix else 0
    if type(width) is not int or width < 0:
        raise ValueError('invalid matrix width')
    rows = []
    for row in matrix:
        if (type(row) not in (list, tuple) or len(row) != width
                or any(type(x) not in (int, Fraction) for x in row)):
            raise ValueError('matrix must have fixed-width exact rational rows')
        rows.append(tuple(Fraction(x) for x in row))
    return tuple(rows), width


def _matrix_hash(rows, width):
    data = [width, [[[hex(x.numerator), hex(x.denominator)] for x in row]
                    for row in rows]]
    return sha256(json.dumps(data, separators=(',', ':')).encode()).hexdigest()


def _encode(values):
    return json_safe([[Fraction(x).numerator, Fraction(x).denominator] for x in values])


def _basis(reduced, width):
    pivots = [next(j for j, x in enumerate(row[:width]) if x) for row in reduced]
    result = []
    for j in range(width):
        if j in pivots:
            continue
        vector = [Fraction(i == j) for i in range(width)]
        for p, row in zip(pivots, reduced):
            vector[p] = -row[j]
        result.append(tuple(vector))
    return tuple(result)


def _valid(rows, x, y, multipliers, check):
    if any(a < 0 or b < 0 or a+b < 1 or a*b for a, b in zip(x, y)):
        return False
    for row in rows:
        check()
        if sum(a*b for a, b in zip(row, x)):
            return False
    for j, value in enumerate(y):
        check()
        if value != sum(a*row[j] for a, row in zip(multipliers, rows)):
            return False
    return True


def _integer_vector(values):
    values = [Fraction(x) for x in values]
    denominator = lcm(*(x.denominator for x in values)) if values else 1
    integers = [int(x*denominator) for x in values]
    divisor = gcd(*integers) if integers else 0
    return [Fraction(x // divisor) for x in integers] if divisor else values


def _restricted_reconstruction(basis, allowed, approximate, width, check):
    """Produce a strictly positive vector in a prescribed coordinate face.

    Zero coordinates are imposed exactly before rounding any parameters.
    The floating proposal therefore cannot certify an almost-zero matching
    constraint. Every resulting coordinate is an exact rational combination.
    """
    if not allowed:
        return [Fraction(0)]*width
    allowed = set(allowed)
    conditions = [[row[j] for row in basis] for j in range(width) if j not in allowed]
    parameters = _nullspace(conditions, len(basis), check)
    restricted = [tuple(sum(z*row[j] for z, row in zip(parameter, basis))
                        for j in range(width)) for parameter in parameters]
    canonical = canonical_matching_basis(restricted, width, check)
    if not canonical:
        return None
    free = [next(j for j in range(width-1, -1, -1) if row[j]) for row in canonical]
    for denominator in (1, 1000, 1000000, 2**30, None):
        check()
        values = [Fraction(float(approximate[j])) for j in free]
        if denominator is not None:
            values = [x.limit_denominator(denominator) for x in values]
        vector = [sum(z*row[j] for z, row in zip(values, canonical)) for j in range(width)]
        if all((value > 0 if j in allowed else value == 0)
               for j, value in enumerate(vector)):
            return _integer_vector(vector)
    return None


def _lp_data(rows, width, check):
    # Variables are x, lambda_plus, lambda_minus, all nonnegative. y is
    # eliminated: y=A^T(lambda_plus-lambda_minus). There is no big-M bound.
    rank = len(rows)
    inequalities = []
    rhs = []
    for j in range(width):
        check()
        dual = [-row[j] for row in rows] + [row[j] for row in rows]
        inequalities.append([0]*width + dual)
        rhs.append(0)
        inequalities.append([-int(i == j) for i in range(width)] + dual)
        rhs.append(-1)
    equalities = [list(row) + [0]*(2*rank) for row in rows]
    return [0]*(width+2*rank), inequalities, rhs, equalities, [0]*rank


def _scipy_solve(data):
    from scipy.optimize import linprog
    c, a, b, eq, rhs = data
    result = linprog(c, A_ub=[[float(x) for x in row] for row in a], b_ub=b,
                     A_eq=[[float(x) for x in row] for row in eq] if eq else None,
                     b_eq=rhs if eq else None, bounds=(0, None), method='highs')
    if not result.success or result.x is None:
        return None
    return list(result.x)


def _sympy_solve(data):
    from sympy import Rational
    from sympy.solvers.simplex import linprog
    c, a, b, eq, rhs = data
    convert = lambda rows: [[Rational(Fraction(x).numerator, Fraction(x).denominator)
                             for x in row] for row in rows]
    _, answer = linprog(c, convert(a), b, convert(eq) if eq else None,
                       rhs if eq else None)
    return [Fraction(int(Rational(x).p), int(Rational(x).q)) for x in answer]


def _partition(rows, basis, width, solver, check, stats):
    if solver not in ('auto', 'scipy', 'sympy'):
        raise ValueError('solver must be auto, scipy or sympy')
    check()
    stats.update(solver_attempts=[], numerical_reconstructions=0,
                 polynomial_solver_guarantee=False)
    pivots = [next(j for j, x in enumerate(row) if x) for row in rows]

    def finish(x, y):
        x, y = _integer_vector(x), _integer_vector(y)
        multipliers = [y[j] for j in pivots]
        if _valid(rows, x, y, multipliers, check):
            return x, y, multipliers
        return None

    if not width:
        stats['solver'] = 'empty'
        return [], [], []
    if not rows or all(sum(row) == 0 for row in rows):
        stats['solver'] = 'positive-unit-vector'
        return finish([1]*width, [0]*width)
    if not basis:
        stats['solver'] = 'zero-kernel'
        return finish([0]*width, [1]*width)
    if len(basis) == 1:
        vector = basis[0]
        if all(x >= 0 for x in vector):
            result = finish(vector, [int(x == 0) for x in vector])
        else:
            positive = sum(x for x in vector if x > 0)
            negative = -sum(x for x in vector if x < 0)
            result = finish([0]*width,
                            [negative if x > 0 else positive if x < 0 else 1
                             for x in vector])
        if result is not None:
            stats['solver'] = 'one-dimensional'
            return result
    data = _lp_data(rows, width, check)
    for method in (('scipy', 'sympy') if solver == 'auto' else (solver,)):
        check()
        # Dependency exceptions mean no proposed witness. Caller callbacks are
        # outside this try block and are never converted into INCONCLUSIVE.
        try:
            proposal = (_scipy_solve if method == 'scipy' else _sympy_solve)(data)
        except Exception as error:
            proposal = None
            reason = type(error).__name__
        else:
            reason = 'no feasible proposal' if proposal is None else 'proposed'
        check()
        attempt = dict(solver=method, outcome=reason)
        stats['solver_attempts'].append(attempt)
        if proposal is None or len(proposal) != width+2*len(rows):
            continue
        if method == 'sympy':
            x = proposal[:width]
            multipliers = [proposal[width+j]-proposal[width+len(rows)+j]
                           for j in range(len(rows))]
            y = [sum(a*row[j] for a, row in zip(multipliers, rows))
                 for j in range(width)]
            result = finish(x, y) if _valid(rows, x, y, multipliers, check) else None
        else:
            if not all(isfinite(float(x)) for x in proposal):
                attempt['outcome'] = 'nonfinite proposal'
                continue
            x_guess = proposal[:width]
            multipliers = [proposal[width+j]-proposal[width+len(rows)+j]
                           for j in range(len(rows))]
            y_guess = [sum(float(a)*float(row[j]) for a, row in zip(multipliers, rows))
                       for j in range(width)]
            if not all(isfinite(value) for value in y_guess):
                attempt['outcome'] = 'nonfinite dual proposal'
                continue
            keep = [j for j in range(width) if x_guess[j] > y_guess[j]]
            x = _restricted_reconstruction(basis, keep, x_guess, width, check)
            y = _restricted_reconstruction(rows, [j for j in range(width) if j not in keep],
                                           y_guess, width, check)
            stats['numerical_reconstructions'] += 1
            result = finish(x, y) if x is not None and y is not None else None
        if result is not None:
            attempt['outcome'] = 'exact witness accepted'
            stats['solver'] = method
            return result
        attempt['outcome'] = 'exact witness rejected'
    return None


def certify_nonnegative_kernel_support(matrix, *, width=None, solver='auto',
                                       check=lambda: None, stats=None):
    """Certify the exact maximal support of a rational nonnegative kernel.

    An empty row list accepts an explicit width. Booleans and floating-point
    input coefficients are rejected. Third-party solver output is a proposal;
    a returned COMPLETE record always passed the independent exact checker.
    """
    check()
    rows, width = _input_matrix(matrix, width)
    if stats is None:
        stats = {}
    else:
        stats.clear()
    augmented = [list(row) + [Fraction(i == j) for j in range(len(rows))]
                 for i, row in enumerate(rows)]
    reduced, pivots = _rref(augmented, width, check)
    equations = [row[:width] for row in reduced]
    basis = _basis(reduced, width)
    stats.update(coordinates=width, matching_rank=len(pivots), raw_dimension=len(basis))
    solution = _partition(equations, basis, width, solver, check, stats)
    if solution is None:
        return dict(status='INCONCLUSIVE', reason='no exact primal-dual witness', stats=stats)
    x, y, multipliers = solution
    original = [sum(a*row[width+j] for a, row in zip(multipliers, reduced))
                for j in range(len(rows))]
    retained = [j for j, value in enumerate(x) if value]
    proof = dict(schema='rational-kernel-maximal-support-v1',
                 input_sha256=_matrix_hash(rows, width), primal=_encode(x), dual=_encode(y),
                 multipliers=_encode(original), retained_indices=retained)
    from .sector_maximal_support_verify import verify_nonnegative_kernel_support_certificate
    if not verify_nonnegative_kernel_support_certificate(rows, proof, width=width, check=check):
        raise ArithmeticError('independent rational support replay rejected')
    effective = len(_nullspace([[row[j] for j in retained] for row in equations],
                              len(retained), check))
    stats.update(retained_coordinates=len(retained), forced_coordinates=width-len(retained),
                 effective_dimension=effective)
    return dict(status='COMPLETE', retained_indices=retained, certificate=proof, stats=stats)


def _certify_kernel(kernel, solver, check, stats):
    width = len(kernel.support)
    equations = _kernel_equations(kernel.basis, width, check)
    stats.update(coordinates=width, raw_dimension=len(kernel.basis),
                 matching_rank=len(equations))
    solution = _partition(equations, kernel.basis, width, solver, check, stats)
    if solution is None:
        return dict(status='INCONCLUSIVE', reason='no exact primal-dual witness', stats=stats)
    x, y, multipliers = solution
    coordinates = kernel.lift([int(value) for value in x], check)
    retained = [j for j, value in enumerate(x) if value]
    combination = []
    if any(y):
        augmented = _source_constraints(kernel.prepared, kernel.support, check)
        if [row[:width] for row in augmented] != equations:
            raise ArithmeticError('source provenance disagrees with matching constraints')
        for j in range(len(kernel.prepared['matching'])):
            check()
            value = sum(a*row[width+j] for a, row in zip(multipliers, augmented))
            if value:
                combination.append([j, value.numerator, value.denominator])
    proof = json_safe(dict(schema='normal-sector-maximal-support-v1',
        source_sha256=_source_hash(kernel.triangulation),
        allowed_types=[list(x) for x in kernel.support],
        primal_coordinates=coordinates, row_combination=combination,
        retained_indices=retained))
    from .sector_maximal_support_verify import verify_maximal_support_certificate
    if not verify_maximal_support_certificate(kernel.triangulation, kernel.support,
                                               proof, check=check):
        raise ArithmeticError('independent source support replay rejected')
    effective = len(_nullspace([[row[j] for j in retained] for row in equations],
                              len(retained), check))
    stats.update(retained_coordinates=len(retained), forced_coordinates=width-len(retained),
                 effective_dimension=effective)
    return dict(status='COMPLETE', retained_indices=retained, certificate=proof, stats=stats)


def _source(triangulation, source, check):
    check()
    if source is None:
        return PreparedSectorSource(triangulation, check=check)
    if source.source_sha256 != _source_hash(triangulation):
        raise ValueError('prepared source does not match triangulation')
    return source


def certify_maximal_support(triangulation, allowed_types, *, source=None, solver='auto',
                            check=lambda: None, stats=None):
    """Return maximal source support with an independent primal/dual proof."""
    source = _source(triangulation, source, check)
    kernel = source.build(allowed_types, check=check)
    if stats is None:
        stats = {}
    else:
        stats.clear()
    return _certify_kernel(kernel, solver, check, stats)


def discover_in_maximal_support_sector(triangulation, allowed_types, *, source=None,
        solver='auto', phase='standard', method='auto', max_bases=None,
        max_orbit_cycles=None, check=lambda: None):
    """Opt-in discovery with complete support reduction and incumbent fallback.

    A successful maximal-support certificate is separate from the discovery
    proof. The latter retains the original allowed support and is accepted by
    the existing independent witness/exhaustion verifiers. Solver failure is
    a fallback, not a deletion. This source-sector API proves no diagram-wide
    absence or new global recognition complexity bound.
    """
    if phase not in ('standard', 'quadrilateral'):
        raise ValueError('unknown search phase')
    if method not in ('auto', 'arrangement', 'supports', 'envelope', 'planar'):
        raise ValueError('unknown ray method')
    if phase == 'quadrilateral' and method in ('supports', 'envelope', 'planar'):
        raise ValueError('this method requires the standard phase')
    for value in (max_bases, max_orbit_cycles):
        if value is not None and (type(value) is not int or value < 0):
            raise ValueError('allowances must be nonnegative integers or None')
    source = _source(triangulation, source, check)
    kernel = source.build(allowed_types, check=check)
    reduction = _certify_kernel(kernel, solver, check, {})
    from .normal_sector import _discover_in_kernel
    if reduction['status'] != 'COMPLETE':
        answer = _discover_in_kernel(kernel, phase=phase, method=method, max_bases=max_bases,
                                    max_orbit_cycles=max_orbit_cycles, check=check)
        answer['stats']['maximal_support'] = reduction['stats']
        return answer
    retained = reduction['retained_indices']
    reduced = (kernel if len(retained) == len(kernel.support) else
               source.build([kernel.support[j] for j in retained], check=check))
    answer = _discover_in_kernel(reduced, phase=phase, method=method, max_bases=max_bases,
                                max_orbit_cycles=max_orbit_cycles, check=check,
                                matching_first=False)
    proof = answer.get('certificate')
    if proof is not None and len(retained) != len(kernel.support):
        proof['allowed_types'] = [list(x) for x in kernel.support]
        if proof['schema'] == 'normal-sector-exhaustion-v1':
            if 'q_support_certificate' in proof or 'matching_support_certificate' in proof:
                raise ArithmeticError('maximal support unexpectedly admitted further zeros')
            for entry in proof['rays']:
                check()
                full = [0]*len(kernel.support)
                for j, value in zip(retained, entry['quadrilaterals']):
                    full[j] = value
                entry['quadrilaterals'] = full
            forced = [j for j in range(len(kernel.support)) if j not in retained]
            proof['matching_support_certificate'] = dict(
                schema='normal-sector-matching-support-v1',
                source_sha256=reduction['certificate']['source_sha256'],
                allowed_types=deepcopy(proof['allowed_types']),
                steps=[dict(row_combination=reduction['certificate']['row_combination'],
                            forced_indices=forced)])
    answer['maximal_support_certificate'] = reduction['certificate']
    answer['stats']['maximal_support'] = reduction['stats']
    return answer
