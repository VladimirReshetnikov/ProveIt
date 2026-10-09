"""Certified maximal-support cones and adaptive quadrilateral face search.

One lifted nonnegative-kernel LP returns either a positive-Euler vector with
the entire active support and one exposing dual, or an ordinary negative
dual.  The positive vector is generally *not* quadrilateral admissible.
The optional search resolves incompatible active pairs by binary face splits.

This is an exact research producer.  Its inherited Bland simplex backend is
finite without caps, but has no polynomial worst-case pivot bound.  Neither a
positive relaxed cone nor a positive-Euler surface is an unknot verdict.
"""

from fractions import Fraction
from hashlib import sha256
from itertools import combinations, product
from math import gcd, lcm, prod
import json

from .exact_lp import solve_nonnegative_kernel
from .integer_codec import encoded_integer


def _fraction(value):
    if type(value) is Fraction:
        return value
    if type(value) in (list, tuple):
        if len(value) != 2:
            raise ValueError('rational values require a numerator and denominator')
        numerator, denominator = map(encoded_integer, value)
        if denominator <= 0:
            raise ValueError('rational denominators must be positive')
        return Fraction(numerator, denominator)
    return Fraction(encoded_integer(value))


def _pair(value):
    value = Fraction(value)
    return [value.numerator, value.denominator]


def _input(matrix, objective):
    if type(matrix) not in (list, tuple) or type(objective) not in (list, tuple):
        raise ValueError('matrix and objective must be sequences')
    c = [_fraction(value) for value in objective]
    if any(type(row) not in (list, tuple) or len(row) != len(c) for row in matrix):
        raise ValueError('matrix width differs from objective length')
    return [[_fraction(value) for value in row] for row in matrix], c


def _limit(name, value):
    if value is not None and (type(value) is not int or value < 0):
        raise ValueError(name + ' must be a nonnegative integer or None')


def _rank(rows, width, check):
    """Exact rank, used only for explanatory search statistics."""
    a = [[Fraction(x) for x in row] for row in rows if any(row)]
    result = 0
    for column in range(width):
        check()
        pivot = next((i for i in range(result, len(a)) if a[i][column]), None)
        if pivot is None:
            continue
        a[result], a[pivot] = a[pivot], a[result]
        scale = a[result][column]
        a[result] = [x / scale for x in a[result]]
        for i in range(result + 1, len(a)):
            scale = a[i][column]
            if scale:
                a[i] = [x-scale*y for x, y in zip(a[i], a[result])]
        result += 1
        if result == len(a):
            break
    return result


def _primitive(vector):
    denominator = lcm(*(x.denominator for x in vector)) if vector else 1
    answer = [int(x*denominator) for x in vector]
    common = 0
    for value in answer:
        common = gcd(common, value)
    return [value//common for value in answer] if common else answer


def active_positive_cone(matrix, objective, *, max_pivots=100000,
                         check=lambda: None):
    """Return ACTIVE_POSITIVE, NONPOSITIVE, or INCONCLUSIVE for Ax=0, x>=0.

    ACTIVE_POSITIVE supplies x>=0, Ax=0, c*x>=1 and y such that s=A^T*y>=0
    and x+s>=1.  Exact orthogonality forces complementary supports: x_j>=1
    precisely on the active coordinates of the full cone, and s_j>=1 on its
    identically-zero coordinates.  A single ordinary dual certifies a
    NONPOSITIVE result.  The independent checker imports no producer or LP.

    The lifted variables are x, y+, y-, s, u, v, tau, all nonnegative, with
    Ax=0; s-A^T(y+-y-)=0; x+s-u-tau=0; c*x-v-tau=0.  Positivity of tau is
    equivalent to the requested strictly complementary positive certificate.
    There is exactly one call to the inherited homogeneous LP oracle.
    """
    _limit('max_pivots', max_pivots)
    a, c = _input(matrix, objective)
    check()
    m, n = len(a), len(c)
    plus, minus, slack, surplus = n, n+m, n+2*m, 2*n+2*m
    value, tau = 3*n+2*m, 3*n+2*m+1
    width = tau+1
    lifted = [row + [Fraction(0)]*(width-n) for row in a]
    for j in range(n):
        check()
        row = [Fraction(0)]*width
        row[slack+j] = 1
        for i in range(m):
            row[plus+i], row[minus+i] = -a[i][j], a[i][j]
        lifted.append(row)
    for j in range(n):
        row = [Fraction(0)]*width
        row[j] = row[slack+j] = 1
        row[surplus+j] = row[tau] = -1
        lifted.append(row)
    row = c + [Fraction(0)]*(width-n)
    row[value] = row[tau] = -1
    lifted.append(row)
    target = [0]*width
    target[tau] = 1
    answer = solve_nonnegative_kernel(lifted, target, max_pivots=max_pivots,
                                     check=check)
    statistics = dict(answer['stats'], input_variables=n, input_equations=m,
                      lp_calls=1)
    if answer['status'] == 'INCONCLUSIVE':
        return dict(status='INCONCLUSIVE', reason=answer['reason'], stats=statistics)
    if answer['status'] == 'POSITIVE':
        full = [_fraction(v) for v in answer['x']]
        scaling = full[tau]
        x = [v/scaling for v in full[:n]]
        y = [(full[plus+i]-full[minus+i])/scaling for i in range(m)]
        certificate = dict(schema='active-positive-cone-v1', status='ACTIVE_POSITIVE',
                           x=[_pair(v) for v in x], y=[_pair(v) for v in y])
        active = [j for j, v in enumerate(x) if v > 0]
        statistics['active_coordinates'] = len(active)
        return dict(status='ACTIVE_POSITIVE', active=active, x=certificate['x'],
                    y=certificate['y'], primitive_x=_primitive(x),
                    certificate=certificate, stats=statistics)

    # The final lifted-row multiplier delta is strictly negative.  If delta
    # were zero, its inequalities force gamma<=0, beta>=-gamma>=0, A beta=0,
    # and A^T alpha+gamma>=0.  Their dot product forces gamma=0, contradicting
    # the required tau-column inequality -sum(gamma)-delta>=1.
    multipliers = [_fraction(v) for v in answer['y']]
    delta = multipliers[-1]
    if delta >= 0:
        raise ArithmeticError('lifted negative proof has no negative objective multiplier')
    y = [v/(-delta) for v in multipliers[:m]]
    if any(sum(a[i][j]*y[i] for i in range(m)) < c[j] for j in range(n)):
        raise ArithmeticError('lifted negative proof failed projection to the source')
    certificate = dict(schema='active-positive-cone-v1', status='NONPOSITIVE',
                       y=[_pair(v) for v in y])
    return dict(status='NONPOSITIVE', y=certificate['y'], certificate=certificate,
                stats=statistics)


def _groups(groups, width):
    if type(groups) not in (list, tuple):
        raise ValueError('conflict groups must be a sequence')
    answer = []
    for group in groups:
        if (type(group) not in (list, tuple) or len(group) < 2
                or any(type(j) is not int or not 0 <= j < width for j in group)
                or len(group) != len(set(group))):
            raise ValueError('each conflict group must have distinct valid indices')
        answer.append(tuple(group))
    return tuple(answer)


def search_admissible_positive_cone(matrix, objective, conflict_groups, *,
                                    max_nodes=1000, max_branch_depth=12,
                                    max_pivots=100000, precheck=True,
                                    check=lambda: None):
    """Search for c*x>0 with at most one positive coordinate per conflict group.

    An active-support query at each node deletes every universally zero
    coordinate.  An active incompatible pair i,j has the complete binary
    disjunction x_i=0 or x_j=0.  Positive certificates contain an admissible
    vector; negative certificates retain every active-support pair and both
    children.  All caps return INCONCLUSIVE.  Inputs are generic rational
    cones; a triangulation wrapper below supplies normal matching equations.
    By default a smaller ordinary LP handles negative cones and already
    admissible basic witnesses before the lifted active-support query.  Set
    precheck=False to exercise the pure maximal-support face search.
    """
    for name, limit in (('max_nodes', max_nodes),
                        ('max_branch_depth', max_branch_depth),
                        ('max_pivots', max_pivots)):
        _limit(name, limit)
    if type(precheck) is not bool:
        raise ValueError('precheck must be a Boolean')
    a, c = _input(matrix, objective)
    n = len(c)
    groups = _groups(conflict_groups, n)
    statistics = dict(nodes=0, branches=0, lp_calls=0, lp_pivots=0,
                      maximum_branch_depth=0, removed_zero_coordinates=0,
                      root_dimension=None, root_ambiguity_rank=None,
                      prechecks=0, active_queries=0, early_admissible=0)

    def visit(columns, depth):
        check()
        if max_nodes is not None and statistics['nodes'] >= max_nodes:
            return dict(status='INCONCLUSIVE', reason='node allowance exhausted')
        statistics['nodes'] += 1
        statistics['maximum_branch_depth'] = max(depth, statistics['maximum_branch_depth'])
        remaining = None if max_pivots is None else max_pivots-statistics['lp_pivots']
        restricted = [[row[j] for j in columns] for row in a]
        if precheck:
            proposal = solve_nonnegative_kernel(restricted, [c[j] for j in columns],
                                                max_pivots=remaining, check=check)
            statistics['prechecks'] += 1
            statistics['lp_calls'] += 1
            statistics['lp_pivots'] += proposal['stats']['pivots']
            if proposal['status'] == 'INCONCLUSIVE':
                return dict(status='INCONCLUSIVE', reason=proposal['reason'])
            if proposal['status'] == 'NONPOSITIVE':
                return dict(status='NO_ADMISSIBLE_POSITIVE',
                            tree=dict(kind='NONPOSITIVE', dual=proposal['y']))
            vector = [0]*n
            for j, v in zip(columns, proposal['primitive_x']):
                vector[j] = v
            if all(sum(vector[j] > 0 for j in group) <= 1 for group in groups):
                statistics['early_admissible'] += 1
                return dict(status='ADMISSIBLE_POSITIVE', vector=vector)
            remaining = None if max_pivots is None else max_pivots-statistics['lp_pivots']
        result = active_positive_cone(restricted, [c[j] for j in columns],
                                      max_pivots=remaining, check=check)
        statistics['active_queries'] += 1
        statistics['lp_calls'] += 1
        statistics['lp_pivots'] += result['stats']['pivots']
        if result['status'] == 'INCONCLUSIVE':
            return dict(status='INCONCLUSIVE', reason=result['reason'])
        if result['status'] == 'NONPOSITIVE':
            return dict(status='NO_ADMISSIBLE_POSITIVE',
                        tree=dict(kind='NONPOSITIVE', dual=result['y']))
        active = [columns[j] for j in result['active']]
        active_set = set(active)
        statistics['removed_zero_coordinates'] += len(columns)-len(active)
        live_groups = [tuple(j for j in group if j in active_set) for group in groups]
        ambiguous = {j for group in live_groups if len(group) > 1 for j in group}
        if depth == 0:
            small = [[row[j] for j in active] for row in a]
            rank = _rank(small, len(active), check)
            selector = [[int(j == k) for k in active] for j in sorted(ambiguous)]
            statistics['root_dimension'] = len(active)-rank
            statistics['root_ambiguity_rank'] = _rank(small+selector, len(active), check)-rank
        if not ambiguous:
            vector = [0]*n
            for j, v in zip(columns, result['primitive_x']):
                vector[j] = v
            return dict(status='ADMISSIBLE_POSITIVE', vector=vector)
        if max_branch_depth is not None and depth >= max_branch_depth:
            return dict(status='INCONCLUSIVE', reason='branch depth allowance exhausted')
        group = next(group for group in live_groups if len(group) > 1)
        pair = list(group[:2])
        statistics['branches'] += 1
        children = []
        for forbidden in pair:
            child = visit([j for j in active if j != forbidden], depth+1)
            if child['status'] != 'NO_ADMISSIBLE_POSITIVE':
                return child
            children.append(child['tree'])
        return dict(status='NO_ADMISSIBLE_POSITIVE', tree=dict(
            kind='PAIR', active_certificate=result['certificate'],
            pair=pair, children=children))

    result = visit(list(range(n)), 0)
    result['stats'] = statistics
    if result['status'] == 'ADMISSIBLE_POSITIVE':
        result['certificate'] = dict(schema='active-face-search-v1',
                                     status=result['status'], x=result['vector'])
    elif result['status'] == 'NO_ADMISSIBLE_POSITIVE':
        result['certificate'] = dict(schema='active-face-search-v1',
                                     status=result['status'], tree=result.pop('tree'))
    return result


def _normal_model(triangulation, check):
    # F-E+V construction adapted from the separately delivered dual-certificate
    # continuation.  The checker rebuilds coefficients disk by disk instead.
    from .normal_surface_geometry import _prepare, _quad
    prepared = _prepare(triangulation, check)
    t = len(prepared['tetrahedra'])
    matrix = [[row.get(j, 0) for j in range(7*t)] for row in prepared['matching']]
    euler = [1]*(7*t)
    faces = prepared['boundary_faces'] + [(a, f) for a, f, _, _, _ in prepared['pairs']]
    for a, f in faces:
        for v in range(4):
            if v != f:
                euler[7*a+v] -= 1
        for q in range(3):
            euler[7*a+4+q] -= 1
    seen = set()
    for a in range(t):
        check()
        for j, (u, v) in enumerate(combinations(range(4), 2)):
            edge = prepared['edge_roots'][6*a+j]
            if edge in seen:
                continue
            seen.add(edge)
            euler[7*a+u] += 1
            euler[7*a+v] += 1
            for q in range(3):
                if q != _quad(u, v):
                    euler[7*a+4+q] += 1
    grouped = {}
    for corner, vertex in enumerate(prepared['vertex_roots']):
        grouped.setdefault(vertex, []).append(7*(corner//4)+corner % 4)
    return prepared, matrix, euler, [grouped[v] for v in sorted(grouped)]


def search_active_normal_positive(triangulation, *, max_nodes=1000,
                                  max_branch_depth=12, max_pivots=100000,
                                  precheck=True, check=lambda: None):
    """Search all triangle anchors in a validated finite torus-boundary source.

    Returns POSITIVE_EULER, NO_POSITIVE_EULER, or INCONCLUSIVE.  The positive
    case is a canonical admissible normal vector; its components and essential
    boundary still require the maintained geometric endpoint.  The negative
    case excludes exactly canonical admissible positive-Euler vectors.  This
    does not establish diagram provenance or perform the complete crushing
    procedure required for general unknot recognition.
    """
    from .normal_surface_geometry import _coordinates
    for name, limit in (('max_nodes', max_nodes),
                        ('max_branch_depth', max_branch_depth),
                        ('max_pivots', max_pivots)):
        _limit(name, limit)
    prepared, matrix, euler, anchor_groups = _normal_model(triangulation, check)
    t, width = len(prepared['tetrahedra']), len(euler)
    statistics = dict(nodes=0, branches=0, lp_calls=0, lp_pivots=0,
                      anchors_started=0, anchors_completed=0,
                      anchor_assignments=prod(map(len, anchor_groups)),
                      maximum_branch_depth=0, maximum_root_ambiguity_rank=0,
                      prechecks=0, active_queries=0, early_admissible=0)
    digest = sha256(json.dumps(triangulation, sort_keys=True,
                               separators=(',', ':')).encode()).hexdigest()
    trees = []
    for anchors in product(*anchor_groups):
        check()
        statistics['anchors_started'] += 1
        zero = set(anchors)
        columns = [j for j in range(width) if j not in zero]
        position = {j: k for k, j in enumerate(columns)}
        groups = [[position[7*a+4+q] for q in range(3)] for a in range(t)]
        nodes = None if max_nodes is None else max_nodes-statistics['nodes']
        pivots = None if max_pivots is None else max_pivots-statistics['lp_pivots']
        result = search_admissible_positive_cone(
            [[row[j] for j in columns] for row in matrix],
            [euler[j] for j in columns], groups, max_nodes=nodes,
            max_branch_depth=max_branch_depth, max_pivots=pivots,
            precheck=precheck, check=check)
        for key in ('nodes', 'branches', 'lp_calls', 'lp_pivots', 'prechecks',
                    'active_queries', 'early_admissible'):
            statistics[key] += result['stats'][key]
        statistics['maximum_branch_depth'] = max(
            statistics['maximum_branch_depth'], result['stats']['maximum_branch_depth'])
        # Maximum over the active queries actually run.  Zero with no active
        # query is an empty-observation convention, not a rank-zero theorem.
        statistics['maximum_root_ambiguity_rank'] = max(
            statistics['maximum_root_ambiguity_rank'],
            result['stats']['root_ambiguity_rank'] or 0)
        if result['status'] == 'INCONCLUSIVE':
            return dict(status='INCONCLUSIVE', reason=result['reason'], stats=statistics)
        if result['status'] == 'ADMISSIBLE_POSITIVE':
            flat = [0]*width
            for j, value in zip(columns, result['vector']):
                flat[j] = value
            rows = [flat[7*a:7*a+7] for a in range(t)]
            analysed = _coordinates(prepared, rows, check)
            if analysed['euler_characteristic'] <= 0:
                raise ArithmeticError('normal Euler count disagrees with the positive objective')
            certificate = dict(schema='active-normal-search-v1', source_sha256=digest,
                               status='POSITIVE_EULER', anchors=list(anchors),
                               coordinates=rows)
            return dict(status='POSITIVE_EULER', coordinates=rows,
                        euler_characteristic=analysed['euler_characteristic'],
                        certificate=certificate, stats=statistics)
        statistics['anchors_completed'] += 1
        trees.append(dict(anchors=list(anchors), proof=result['certificate']))
    certificate = dict(schema='active-normal-search-v1', source_sha256=digest,
                       status='NO_POSITIVE_EULER', anchor_trees=trees)
    return dict(status='NO_POSITIVE_EULER', certificate=certificate, stats=statistics)
