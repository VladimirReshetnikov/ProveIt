"""Complete bounded positive-Euler search through partial quadrilateral masks.

A mask may retain incompatible Q types. Exact Q matching elimination and the
canonical Euler objectives then describe a relaxation, not an embedded normal
surface. A genuinely positive formal point either supplies compatible normal
coordinates or selects an unresolved tetrahedron for complete branching.
Nonpositive duals exclude whole partial masks and are independently replayable.

This supplied-source search does not authenticate a knot exterior. Complete
search is finite, but the tree has no general quasi-polynomial bound. The
default LP policy is polynomial; legacy Bland remains an explicit comparison.
Finite allowances return no negative certificate.
"""
from fractions import Fraction
from itertools import product

from .exact_lp import solve_nonnegative_kernel
from .euler_lp_budget import (fallback_statistics, validate_lp_controls,
                              lp_options, record_fallback)
from .integer_codec import json_safe
from .normal_euler import _euler_model
from .normal_sector import _assemble_sector_kernel, _source_hash
from .normal_surface_geometry import _prepare, _coordinates, _EDGES, _quad


def _mask(value, count):
    if value is None:
        return tuple((t, q) for t in range(count) for q in range(3))
    if type(value) not in (list, tuple):
        raise ValueError('allowed_types must be an ordered list or tuple')
    mask = []
    for pair in value:
        if (type(pair) not in (list, tuple) or len(pair) != 2 or
                any(type(x) is not int for x in pair) or
                not 0 <= pair[0] < count or not 0 <= pair[1] < 3):
            raise ValueError('allowed_types must contain exact in-range integer pairs')
        mask.append(tuple(pair))
    if mask != sorted(mask) or len(set(mask)) != len(mask):
        raise ValueError('allowed_types must be sorted and unique')
    return tuple(mask)


def _formal_lift(kernel, quadrilaterals, check):
    """Validate matching and the linear Euler extension without embeddedness."""
    q = tuple(quadrilaterals)
    if (len(q) != len(kernel.support) or any(type(x) is not int or x < 0 for x in q)
            or any(sum(a*b for a, b in zip(row, q)) for row in kernel.cycle_rows)):
        raise ArithmeticError('LP point is outside its Q matching cone')
    values = {c: sum(a*b for a, b in zip(kernel.potentials[c], q)) for c in kernel.classes}
    for group in kernel.groups:
        check()
        minimum = min(values[c] for c in group)
        for c in group:
            values[c] -= minimum
    prepared = kernel.prepared
    rows = [[0]*7 for _ in prepared['tetrahedra']]
    for corner, c in enumerate(kernel.corner_class):
        check()
        rows[corner//4][corner % 4] = values.get(c, 0)
    for (t, typ), value in zip(kernel.support, q):
        rows[t][4+typ] = value
    flat = [x for row in rows for x in row]
    if any(type(x) is not int or x < 0 for x in flat):
        raise ArithmeticError('formal canonical lift is not nonnegative integral')
    for equation in prepared['matching']:
        check()
        if sum(a*flat[j] for j, a in equation.items()):
            raise ArithmeticError('formal lift violates original matching equations')
    minima, edge_weights = {}, {}
    for t, row in enumerate(rows):
        check()
        for v in range(4):
            vertex = prepared['vertex_roots'][4*t+v]
            minima[vertex] = min(minima.get(vertex, row[v]), row[v])
        for e, (a, b) in enumerate(_EDGES):
            edge = prepared['edge_roots'][6*t+e]
            value = row[a]+row[b]+sum(row[4:])-row[4+_quad(a, b)]
            if edge in edge_weights and edge_weights[edge] != value:
                raise ArithmeticError('formal edge weights disagree across source faces')
            edge_weights[edge] = value
    if any(minima.values()):
        raise ArithmeticError('formal lift did not remove vertex-link factors')
    faces = prepared['boundary_faces'] + [(t, f) for t, f, _, _, _ in prepared['pairs']]
    arcs = 0
    for t, f in faces:
        check()
        arcs += sum(rows[t][v] for v in range(4) if v != f)+sum(rows[t][4:])
    chi = sum(edge_weights.values())-arcs+sum(flat)
    conflicts = [t for t, row in enumerate(rows) if sum(bool(x) for x in row[4:]) > 1]
    return rows, chi, conflicts


def _euler_search_stats():
    return dict(fallback_statistics(), nodes_attempted=0, branch_splits=0, negative_leaves=0,
                 lp_calls=0, lp_pivots=0, anchors_tested=0, reused_anchors=0,
                 envelope_calls=0, reused_envelopes=0,
                 lp_tableau_updates=0, maximum_tableau_bits=0,
                 positive_relaxations=0, incompatible_positive_points=0,
                 nonpositive_envelope_points=0, maximum_depth=0,
                 kernel_preparations=0)


class _EulerMaskOracle:
    """Shared exact mask oracle; one cache and shared caps per search call."""

    def __init__(self, triangulation, prepared, *, strategy, model,
                 max_pivots, max_anchors, check, stats, lp_policy='polynomial',
                 lp_fast_path_pivots=None, max_ellipsoid_iterations=None,
                 max_feasibility_calls=None):
        self.triangulation, self.prepared = triangulation, prepared
        self.strategy, self.model, self.check = strategy, model, check
        self.max_pivots, self.max_anchors = max_pivots, max_anchors
        self.lp_policy, self.lp_fast_path_pivots = lp_policy, lp_fast_path_pivots
        self.max_ellipsoid_iterations = max_ellipsoid_iterations
        self.max_feasibility_calls = max_feasibility_calls
        self.stats, self.digest = stats, _source_hash(triangulation)
        self.source_context, self.source_cache = None, None

    def attempt(self, mask):
        triangulation, prepared = self.triangulation, self.prepared
        strategy, model, check = self.strategy, self.model, self.check
        max_pivots, max_anchors = self.max_pivots, self.max_anchors
        stats, digest = self.stats, self.digest
        source_context, source_cache = self.source_context, self.source_cache
        if model == 'source':
            if source_context is None:
                full = tuple((t, q) for t in range(len(prepared['tetrahedra'])) for q in range(3))
                kernel = _assemble_sector_kernel(triangulation, prepared, full, check)
                linear, weights = _euler_model(kernel, check)
                source_context = kernel, linear, weights
                source_cache = [(tuple(0 for _ in full), [[0, 1] for _ in kernel.cycle_rows])]
                self.source_context, self.source_cache = source_context, source_cache
                stats['kernel_preparations'] += 1
            kernel, linear, weights = source_context
            active = tuple(3*t+q for t, q in mask)
            cache = source_cache
        else:
            kernel = _assemble_sector_kernel(triangulation, prepared, mask, check)
            linear, weights = _euler_model(kernel, check)
            active = tuple(range(len(mask)))
            cache = [(tuple(0 for _ in mask), [[0, 1] for _ in kernel.cycle_rows])]
            stats['kernel_preparations'] += 1
        # Keep the full row list in source mode, including zero restrictions:
        # a returned multiplier then has the same source-row interpretation at
        # every node. Only its required coordinate inequalities change.
        matrix = tuple(tuple(row[j] for j in active) for row in kernel.cycle_rows)
        duals = []

        def cached(objective):
            for bound, dual in reversed(cache):
                check()
                if all(objective[j] <= bound[j] for j in active):
                    return dual
            return None

        def remember(dual):
            multipliers = [Fraction(*pair) for pair in dual]
            bound = tuple(sum(row[j]*y for row, y in zip(kernel.cycle_rows, multipliers))
                          for j in range(len(kernel.support)))
            cache.append((bound, dual))
            if len(cache) > 256:
                del cache[1]

        def solve(objective):
            result = solve_nonnegative_kernel(matrix, [objective[j] for j in active],
                **lp_options(stats, policy=self.lp_policy,
                    fast_path_pivots=self.lp_fast_path_pivots, max_pivots=max_pivots,
                    max_ellipsoid_iterations=self.max_ellipsoid_iterations,
                    max_feasibility_calls=self.max_feasibility_calls), check=check)
            stats['lp_calls'] += 1
            stats['lp_pivots'] += result['stats']['pivots']
            record_fallback(stats, result['stats'])
            stats['lp_tableau_updates'] += result['stats']['tableau_updates']
            stats['maximum_tableau_bits'] = max(stats['maximum_tableau_bits'],
                                                 result['stats']['maximum_tableau_bits'])
            return result

        def point(result):
            q = [0]*len(kernel.support)
            for j, value in zip(active, result['primitive_x']):
                q[j] = value
            rows, chi, conflicts = _formal_lift(kernel, q, check)
            value = sum(a*b for a, b in zip(linear, q))
            for group, weight in zip(kernel.groups, weights):
                check()
                value -= weight*min(sum(a*b for a, b in zip(kernel.potentials[c], q))
                                    for c in group)
            if chi != value:
                raise ArithmeticError('canonical Euler formula disagrees with original incidence')
            return dict(status='POSITIVE', coordinates=rows,
                        euler_characteristic=chi, conflicts=conflicts)

        def negative(kind, proof):
            schema = 'normal-euler-relaxation-v2' if model == 'source' else 'normal-euler-relaxation-v1'
            packet = dict(schema=schema, status='NO_POSITIVE_EULER',
                source_sha256=digest, allowed_types=[list(p) for p in mask], proof_kind=kind)
            packet.update(proof)
            return dict(status='NEGATIVE', certificate=json_safe(packet))

        if strategy == 'envelope':
            envelope = list(linear)
            for group, weight in zip(kernel.groups, weights):
                check()
                for j in range(len(kernel.support)):
                    envelope[j] -= weight*min(kernel.potentials[c][j] for c in group)
            stats['envelope_calls'] += 1
            reused = cached(envelope)
            if reused is not None:
                stats['reused_envelopes'] += 1
                return negative('envelope', dict(multipliers=reused))
            result = solve(envelope)
            if result['status'] == 'INCONCLUSIVE':
                return result
            if result['status'] == 'NONPOSITIVE':
                remember(result['y'])
                return negative('envelope', dict(multipliers=result['y']))
            lifted = point(result)
            if lifted['euler_characteristic'] > 0:
                return lifted
            # The coefficient envelope may be positive on a formal point
            # where the actual canonical Euler maximum is zero or negative.
            stats['nonpositive_envelope_points'] += 1

        for anchors in product(*kernel.groups):
            check()
            if max_anchors is not None and stats['anchors_tested'] >= max_anchors:
                return dict(status='INCONCLUSIVE', reason='shared anchor allowance exhausted')
            stats['anchors_tested'] += 1
            objective = list(linear)
            for anchor, weight in zip(anchors, weights):
                for j, height in enumerate(kernel.potentials[anchor]):
                    objective[j] -= weight*height
            reused = cached(objective)
            if reused is not None:
                stats['reused_anchors'] += 1
                duals.append(dict(anchors=list(anchors), multipliers=reused))
                continue
            result = solve(objective)
            if result['status'] == 'INCONCLUSIVE':
                return result
            if result['status'] == 'POSITIVE':
                lifted = point(result)
                if lifted['euler_characteristic'] <= 0:
                    raise ArithmeticError('positive anchor lost canonical positive Euler')
                return lifted
            duals.append(dict(anchors=list(anchors), multipliers=result['y']))
            remember(result['y'])
        return negative('anchors', dict(duals=duals))


def search_euler_tree(triangulation, allowed_types=None, *, strategy='envelope', model='source',
                      max_nodes=None, max_pivots=None, max_anchors=None,
                      lp_policy='polynomial', lp_fast_path_pivots=None,
                      max_ellipsoid_iterations=None, max_feasibility_calls=None,
                      check=lambda: None):
    """Return a compatible positive point, a full exclusion tree, or a cap.

    All node, pivot, anchor, ellipsoid and feasibility-call allowances are
    shared across the entire tree. The default LP policy has a polynomial
    prefix and exact fallback; lp_policy='bland' ignores fallback caps.
    Nodes are explored in deterministic depth-first order with an explicit
    stack. At a conflicting tetrahedron, every currently allowed singleton
    type gets a child; its zero-Q possibility is covered in every child.
    Positive output may be nonextreme and requires support extraction before
    crushing. Negative output is only about this supplied source and root mask.
    Caller cancellation exceptions propagate unchanged.

    model='source' builds the all-3t source algebra once. Every node restricts
    its columns, and up to 256 source-row dual bounds are reused across nodes.
    Its v2 negative leaves retain every full-source anchor objective.
    model='restricted' rebuilds and contracts the algebra on each node mask,
    using a local dual cache and the original v1 negative leaf format.
    """
    for name, cap in (('max_nodes', max_nodes), ('max_pivots', max_pivots),
                      ('max_anchors', max_anchors)):
        if cap is not None and (type(cap) is not int or cap < 0):
            raise ValueError(name+' must be a nonnegative integer or None')
    if strategy not in ('envelope', 'anchors'):
        raise ValueError('strategy must be envelope or anchors')
    if model not in ('source', 'restricted'):
        raise ValueError('model must be source or restricted')
    validate_lp_controls(lp_policy, lp_fast_path_pivots,
                         max_ellipsoid_iterations, max_feasibility_calls)
    prepared = _prepare(triangulation, check)
    root = _mask(allowed_types, len(prepared['tetrahedra']))
    digest = _source_hash(triangulation)
    stats = _euler_search_stats()
    oracle = _EulerMaskOracle(triangulation, prepared, strategy=strategy, model=model,
                              max_pivots=max_pivots, max_anchors=max_anchors,
                              check=check, stats=stats, lp_policy=lp_policy,
                              lp_fast_path_pivots=lp_fast_path_pivots,
                              max_ellipsoid_iterations=max_ellipsoid_iterations,
                              max_feasibility_calls=max_feasibility_calls)

    def inconclusive(reason):
        return dict(status='INCONCLUSIVE', reason=reason, stats=stats)


    pending, nodes = [(root, 0)], []
    while pending:
        check()
        if max_nodes is not None and stats['nodes_attempted'] >= max_nodes:
            return inconclusive('shared node allowance exhausted')
        mask, depth = pending.pop()
        stats['nodes_attempted'] += 1
        stats['maximum_depth'] = max(stats['maximum_depth'], depth)
        result = oracle.attempt(mask)
        if result['status'] == 'INCONCLUSIVE':
            return inconclusive(result['reason'])
        if result['status'] == 'NEGATIVE':
            stats['negative_leaves'] += 1
            nodes.append(dict(kind='negative', certificate=result['certificate']))
            continue
        stats['positive_relaxations'] += 1
        if not result['conflicts']:
            checked = _coordinates(prepared, result['coordinates'], check)
            if checked['euler_characteristic'] != result['euler_characteristic']:
                raise ArithmeticError('normal Euler check disagrees with formal lift')
            check()
            return dict(status='POSITIVE_EULER', coordinates=result['coordinates'],
                        euler_characteristic=result['euler_characteristic'], stats=stats)
        stats['incompatible_positive_points'] += 1
        t = result['conflicts'][0]
        choices = [q for tet, q in mask if tet == t]
        if len(choices) < 2:
            raise ArithmeticError('positive point conflicts in a resolved tetrahedron')
        stats['branch_splits'] += 1
        nodes.append(dict(kind='split', tetrahedron=t))
        for q in reversed(choices):
            child = tuple(pair for pair in mask if pair[0] != t or pair[1] == q)
            pending.append((child, depth+1))

    certificate = dict(schema='normal-euler-branch-tree-v1', status='NO_POSITIVE_EULER',
        source_sha256=digest, allowed_types=[list(p) for p in root], nodes=nodes)
    check()
    return dict(status='NO_POSITIVE_EULER', certificate=certificate, stats=stats)
