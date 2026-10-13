"""Learn a uniform resolving set from incompatible positive Q extreme rays.

This additive supplied-source search shares the exact fixed-source mask oracle
with the ordinary Euler tree. It does not authenticate a knot exterior. Negative
output uses the existing complete tree certificate; failed candidates never
become negative evidence. Tree size, hitting-set search and Bland pivots have no
general polynomial or quasi-polynomial bound.
"""
from itertools import combinations

from .normal_euler_tree import _EulerMaskOracle, _euler_search_stats, _mask
from .normal_sector import _source_hash
from .normal_surface_geometry import _prepare, _coordinates


def search_euler_transversal(triangulation, allowed_types=None, *,
                             strategy='envelope', max_nodes=None,
                             max_pivots=None, max_anchors=None,
                             max_hitting_subsets=10000, check=lambda: None):
    """Return a positive canonical vector, complete negative tree, or a cap.

    Each incompatible positive basic ray supplies a necessary conflict-hitting
    constraint. Candidates are tested in increasing size, then lexicographic
    order. A candidate restricts branching to its tetrahedra; a ray whose full
    conflict set misses that candidate refutes it. Source algebra and at most
    256 source-row dual bounds are shared across every candidate restart.

    All oracle nodes, LP pivots and anchors count against shared allowances.
    max_hitting_subsets separately charges each unique candidate subset tested
    against the learned constraints, including subsets rejected before an LP.
    None removes any allowance. Callback exceptions propagate unchanged.

    The positive oracle returns a basic point of a normalized coordinate face
    of the fixed Q cone, hence a root extreme ray. The returned canonical
    standard vector may still require positive-ray extraction before crushing.
    """
    for name, cap in (('max_nodes', max_nodes), ('max_pivots', max_pivots),
                      ('max_anchors', max_anchors),
                      ('max_hitting_subsets', max_hitting_subsets)):
        if cap is not None and (type(cap) is not int or cap < 0):
            raise ValueError(name+' must be a nonnegative integer or None')
    if strategy not in ('envelope', 'anchors'):
        raise ValueError('strategy must be envelope or anchors')
    prepared = _prepare(triangulation, check)
    root = _mask(allowed_types, len(prepared['tetrahedra']))
    digest = _source_hash(triangulation)
    stats = _euler_search_stats()
    stats.update(hitting_subsets_tested=0, transversal_candidates=0,
                 transversal_restarts=0, learned_conflicts=0,
                 maximum_transversal_size=0)
    oracle = _EulerMaskOracle(triangulation, prepared, strategy=strategy,
                              model='source', max_pivots=max_pivots,
                              max_anchors=max_anchors, check=check, stats=stats)
    choices = {}
    for t, q in root:
        choices.setdefault(t, []).append(q)
    unresolved = tuple(t for t, qs in choices.items() if len(qs) > 1)
    conflicts = []

    def inconclusive(reason):
        return dict(status='INCONCLUSIVE', reason=reason, stats=stats)

    # Constraints only accumulate. A previously skipped subset remains invalid,
    # and a failed candidate is invalidated by its new disjoint conflict. Thus
    # one increasing-size stream tests every subset at most once, while every
    # explored candidate is minimum for the hypergraph known at that time.
    for size in range(len(unresolved)+1):
        for candidate in combinations(unresolved, size):
            check()
            if (max_hitting_subsets is not None and
                    stats['hitting_subsets_tested'] >= max_hitting_subsets):
                return inconclusive('shared hitting-subset allowance exhausted')
            stats['hitting_subsets_tested'] += 1
            B = frozenset(candidate)
            misses = False
            for edge in conflicts:
                check()
                if B.isdisjoint(edge):
                    misses = True
                    break
            if misses:
                continue
            stats['transversal_candidates'] += 1
            stats['maximum_transversal_size'] = max(stats['maximum_transversal_size'], size)
            pending, nodes = [(root, 0)], []
            refuted = False
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
                edge = frozenset(result['conflicts'])
                already_known = edge in conflicts
                if not already_known:
                    conflicts.append(edge)
                    stats['learned_conflicts'] += 1
                available = sorted(B.intersection(edge))
                if not available:
                    # This is the complete conflict set, not merely the first
                    # offending tetrahedron. It is necessary for every uniform
                    # root-ray transversal and excludes this candidate forever.
                    if already_known:
                        raise ArithmeticError('a previously hit conflict refuted its candidate')
                    stats['transversal_restarts'] += 1
                    refuted = True
                    break
                t = available[0]
                types = [q for tet, q in mask if tet == t]
                if len(types) < 2:
                    raise ArithmeticError('positive point conflicts in a resolved tetrahedron')
                stats['branch_splits'] += 1
                nodes.append(dict(kind='split', tetrahedron=t))
                for q in reversed(types):
                    child = tuple(pair for pair in mask if pair[0] != t or pair[1] == q)
                    pending.append((child, depth+1))
            if refuted:
                continue
            certificate = dict(schema='normal-euler-branch-tree-v1',
                status='NO_POSITIVE_EULER', source_sha256=digest,
                allowed_types=[list(p) for p in root], nodes=nodes)
            check()
            return dict(status='NO_POSITIVE_EULER', certificate=certificate,
                        resolving_set=list(candidate), stats=stats)
    raise ArithmeticError('all ambiguous tetrahedra failed to resolve their own Q conflicts')
