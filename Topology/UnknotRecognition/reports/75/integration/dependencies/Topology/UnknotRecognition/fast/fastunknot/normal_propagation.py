"""Exact positive-Euler search with certified quadrilateral propagation.

This bounded research prototype searches standard normal coordinates with at
least one zero triangle at every global vertex.  Thus vertex-link components
are excluded.  A positive result is a normal surface witness, not an unknot
verdict; a negative result concerns exactly this class of normal surfaces.

The relaxation allows all remaining quadrilateral types.  If forbidding one
type makes positive Euler characteristic impossible, every admissible positive
solution must use that type and must discard the other types in its tetrahedron.
When this implication no longer applies, exhaustive singleton-type branches
cover the admissible solutions, including those using no quad in that tetrahedron.

The exact LP engine uses Bland simplex.  The operational pivot allowance is
explicit; no polynomial worst-case bound for this implementation is claimed.
"""

from hashlib import sha256
from itertools import combinations, product
from math import prod
import json

from .exact_lp import solve_nonnegative_kernel
from .normal_surface_geometry import _prepare, _coordinates, _quad


_SCHEMA = 'normal-positive-euler-propagation-v1'
_EDGES = tuple(combinations(range(4), 2))


def _digest(triangulation):
    data = json.dumps(triangulation, sort_keys=True, separators=(',', ':')).encode()
    return sha256(data).hexdigest()


def build_standard_model(triangulation, *, check=lambda: None):
    """Build integer matching and F-E+V coefficients in all 7t coordinates.

    A global normal vertex is counted at one representative local edge; a
    normal edge is counted at one representative face.  Matching makes these
    choices agree on the solution space, even in the quadrilateral relaxation.
    Anchor groups contain standard coordinate indices, grouped by global vertex.
    """
    prepared = _prepare(triangulation, check)
    t = len(prepared['tetrahedra'])
    width = 7*t
    matrix = [[row.get(j, 0) for j in range(width)]
              for row in prepared['matching']]
    euler = [1]*width
    faces = prepared['boundary_faces'] + [(a, f) for a, f, _, _, _ in prepared['pairs']]
    for a, f in faces:
        check()
        for v in range(4):
            if v != f:
                euler[7*a+v] -= 1
        for q in range(3):
            euler[7*a+4+q] -= 1
    seen = set()
    for a in range(t):
        check()
        for j, (u, v) in enumerate(_EDGES):
            edge = prepared['edge_roots'][6*a+j]
            if edge in seen:
                continue
            seen.add(edge)
            euler[7*a+u] += 1
            euler[7*a+v] += 1
            omitted = _quad(u, v)
            for q in range(3):
                if q != omitted:
                    euler[7*a+4+q] += 1
    grouped = {}
    for corner, vertex in enumerate(prepared['vertex_roots']):
        grouped.setdefault(vertex, []).append(7*(corner//4)+corner % 4)
    groups = [grouped[v] for v in sorted(grouped)]
    return dict(prepared=prepared, matrix=matrix, euler=euler, anchor_groups=groups,
                tetrahedra=t, vertices=len(groups), variables=width)


def _limit(name, value):
    if value is not None and (type(value) is not int or value < 0):
        raise ValueError(name + ' must be a nonnegative integer or None')


def search_positive_euler(triangulation, *, max_branch_depth=12, max_nodes=1000,
                          max_pivots=100000, allowed_branch_tetrahedra=None,
                          check=lambda: None):
    """Return POSITIVE_EULER, NO_POSITIVE_EULER, or INCONCLUSIVE.

    Every LP call shares ``max_pivots``.  ``max_nodes`` counts nodes across all
    triangle-anchor assignments; ``max_branch_depth`` counts only actual
    quadrilateral branching, not deterministic propagation.  A limit prevents
    a negative conclusion and yields INCONCLUSIVE, never a knot verdict.

    ``allowed_branch_tetrahedra`` optionally restricts guesses to a supplied
    distinct list of tetrahedron indices.  Mandatory implications still apply
    everywhere.  Remaining allowed tetrahedra are branched even if the current
    relaxed witness happens to have only one quad type there; this is needed
    for complete exploration of a supplied strong backdoor.

    Positive certificates contain primitive integer standard coordinates.
    Negative certificates contain one complete dual-certified tree for every
    anchor tuple.  The independent verifier reconstructs the source model and
    checks those trees without calling this search or an LP solver.
    """
    for name, value in (('max_branch_depth', max_branch_depth),
                        ('max_nodes', max_nodes), ('max_pivots', max_pivots)):
        _limit(name, value)
    check()
    model = build_standard_model(triangulation, check=check)
    t, width = model['tetrahedra'], model['variables']
    if allowed_branch_tetrahedra is not None and (
            type(allowed_branch_tetrahedra) is not list
            or any(type(a) is not int or not 0 <= a < t for a in allowed_branch_tetrahedra)
            or len(set(allowed_branch_tetrahedra)) != len(allowed_branch_tetrahedra)):
        raise ValueError('allowed_branch_tetrahedra must be a distinct list of tetrahedron indices or None')
    branchable = set(range(t) if allowed_branch_tetrahedra is None else allowed_branch_tetrahedra)
    source = _digest(triangulation)
    stats = dict(tetrahedra=t, vertices=model['vertices'], variables=width,
                 equations=len(model['matrix']),
                 anchor_assignments=prod(map(len, model['anchor_groups'])),
                 anchors_started=0, anchors_completed=0, nodes=0, branches=0,
                 propagations=0, lp_calls=0, lp_pivots=0, tableau_updates=0,
                 maximum_tableau_bits=0, maximum_branch_depth=0,
                 branched_tetrahedra=[])
    limits = dict(max_branch_depth=max_branch_depth, max_nodes=max_nodes,
                  max_pivots=max_pivots,
                  allowed_branch_tetrahedra=None if allowed_branch_tetrahedra is None
                  else sorted(allowed_branch_tetrahedra))

    def finish(status, **fields):
        return dict(status=status, stats=dict(stats), limits=limits, **fields)

    def relaxed(anchors, allowed, forbidden=None):
        check()
        zeros = set(anchors)
        columns = [j for j in range(width) if j not in zeros
                   and (j % 7 < 4 or j % 7-4 in allowed[j//7])
                   and j != forbidden]
        matrix = [[row[j] for j in columns] for row in model['matrix']]
        objective = [model['euler'][j] for j in columns]
        remaining = None if max_pivots is None else max_pivots-stats['lp_pivots']
        answer = solve_nonnegative_kernel(matrix, objective,
                                         max_pivots=remaining, check=check)
        stats['lp_calls'] += 1
        measured = answer['stats']
        stats['lp_pivots'] += measured['pivots']
        stats['tableau_updates'] += measured['tableau_updates']
        stats['maximum_tableau_bits'] = max(stats['maximum_tableau_bits'],
                                            measured['maximum_tableau_bits'])
        if answer['status'] == 'POSITIVE':
            flat = [0]*width
            for j, value in zip(columns, answer['primitive_x']):
                flat[j] = value
            answer['coordinates'] = [flat[7*a:7*a+7] for a in range(t)]
        return answer

    def visit(anchors, allowed, depth):
        check()
        if max_nodes is not None and stats['nodes'] >= max_nodes:
            return dict(status='INCONCLUSIVE', reason='node allowance exhausted')
        stats['nodes'] += 1
        stats['maximum_branch_depth'] = max(stats['maximum_branch_depth'], depth)
        steps = []
        while True:
            current = relaxed(anchors, allowed)
            if current['status'] == 'INCONCLUSIVE':
                return dict(status='INCONCLUSIVE', reason=current['reason'])
            if current['status'] == 'NONPOSITIVE':
                tree = dict(propagations=steps,
                            terminal=dict(kind='NONPOSITIVE', y=current['y']))
                return dict(status='NO_POSITIVE_EULER', tree=tree)
            rows = current['coordinates']
            conflicts = [a for a, row in enumerate(rows)
                         if sum(value > 0 for value in row[4:]) > 1]
            if not conflicts:
                analysed = _coordinates(model['prepared'], rows, check)
                if analysed['euler_characteristic'] <= 0:
                    raise ArithmeticError('positive LP witness has nonpositive Euler characteristic')
                return dict(status='POSITIVE_EULER', coordinates=rows,
                            euler_characteristic=analysed['euler_characteristic'])
            forced = False
            for a in range(t):
                if len(allowed[a]) < 2:
                    continue
                for q in allowed[a]:
                    test = relaxed(anchors, allowed, forbidden=7*a+4+q)
                    if test['status'] == 'INCONCLUSIVE':
                        return dict(status='INCONCLUSIVE', reason=test['reason'])
                    if test['status'] == 'NONPOSITIVE':
                        steps.append(dict(tetrahedron=a, type=q, y=test['y']))
                        stats['propagations'] += 1
                        allowed = allowed[:a] + ((q,),) + allowed[a+1:]
                        forced = True
                        break
                if forced:
                    break
            if forced:
                continue
            candidates = [a for a in conflicts if a in branchable]
            if not candidates:
                candidates = [a for a in sorted(branchable) if len(allowed[a]) >= 2]
            if not candidates:
                return dict(status='INCONCLUSIVE', reason='allowed branch tetrahedra exhausted')
            if max_branch_depth is not None and depth >= max_branch_depth:
                return dict(status='INCONCLUSIVE', reason='branch depth allowance exhausted')
            a = candidates[0]
            stats['branches'] += 1
            stats['branched_tetrahedra'] = sorted(set(stats['branched_tetrahedra']) | {a})
            children = []
            for q in allowed[a]:
                child_allowed = allowed[:a] + ((q,),) + allowed[a+1:]
                child = visit(anchors, child_allowed, depth+1)
                if child['status'] != 'NO_POSITIVE_EULER':
                    return child
                children.append(dict(type=q, tree=child['tree']))
            return dict(status='NO_POSITIVE_EULER', tree=dict(propagations=steps,
                        terminal=dict(kind='BRANCH', tetrahedron=a, children=children)))

    trees = []
    for anchors in product(*model['anchor_groups']):
        check()
        stats['anchors_started'] += 1
        answer = visit(anchors, ((0, 1, 2),)*t, 0)
        if answer['status'] == 'INCONCLUSIVE':
            return finish('INCONCLUSIVE', reason=answer['reason'])
        if answer['status'] == 'POSITIVE_EULER':
            certificate = dict(schema=_SCHEMA, source_sha256=source,
                               status='POSITIVE_EULER', anchors=list(anchors),
                               coordinates=answer['coordinates'])
            return finish('POSITIVE_EULER', coordinates=answer['coordinates'],
                          euler_characteristic=answer['euler_characteristic'],
                          certificate=certificate)
        stats['anchors_completed'] += 1
        trees.append(dict(anchors=list(anchors), tree=answer['tree']))
    certificate = dict(schema=_SCHEMA, source_sha256=source,
                       status='NO_POSITIVE_EULER', anchor_trees=trees)
    return finish('NO_POSITIVE_EULER', certificate=certificate)
