"""Learn a uniform resolving set from incompatible positive Q extreme rays.

This additive supplied-source search shares the exact fixed-source mask oracle
with the ordinary Euler tree. It does not authenticate a knot exterior. Negative
output uses the existing complete tree certificate; failed candidates never
become negative evidence. Tree size and hitting-set search have no general
quasi-polynomial bound, even with the default polynomial exact LP policy.
"""
from itertools import combinations

from .normal_euler_tree import _EulerMaskOracle, _euler_search_stats, _mask
from .normal_sector import _source_hash
from .normal_surface_geometry import _prepare, _coordinates
from .euler_lp_budget import validate_lp_controls


# A fixed cache bounds candidate filtering independently of the number of
# learned rays. Forgetting constraints affects work, never proof acceptance.
_CONFLICT_CACHE_LIMIT = 256


def _charge_candidate(stats, cap, check):
    check()
    if cap is not None and stats['hitting_subsets_tested'] >= cap:
        return False
    stats['hitting_subsets_tested'] += 1
    return True


def _subset_candidates(unresolved, conflicts, stats, cap, check):
    """Retain the original increasing-cardinality, unique-subset stream."""
    for size in range(len(unresolved)+1):
        for candidate in combinations(unresolved, size):
            if not _charge_candidate(stats, cap, check):
                yield None
                return
            chosen = frozenset(candidate)
            for edge in conflicts:
                check()
                if chosen.isdisjoint(edge):
                    break
            else:
                yield candidate


def _missed_conflict(chosen, excluded, conflicts, check):
    """Smallest available missed edge; empty means this state is impossible."""
    missed = None
    for edge in conflicts:
        check()
        if chosen.isdisjoint(edge):
            available = tuple(sorted(edge-excluded))
            if missed is None or (len(available), available) < (len(missed), missed):
                missed = available
    return missed


def _conflict_candidates(unresolved, conflicts, stats, cap, check):
    """Iterative deepening on disjoint conflict choices, with FIFO forgetting.

    The consumer must append a missed conflict before resuming a yielded
    candidate. Excluded tetrahedra constrain candidate selection only: the
    Euler oracle always starts from the unchanged full root Q mask.
    """
    for limit in range(len(unresolved)+1):
        pending = [(frozenset(), frozenset())]
        while pending:
            if not _charge_candidate(stats, cap, check):
                yield None
                return
            chosen, excluded = pending.pop()
            edge = _missed_conflict(chosen, excluded, conflicts, check)
            if edge is None:
                yield tuple(sorted(chosen))
                # A failed full candidate query supplies a necessary missed
                # edge. Resume this already charged state, without creating
                # an uncharged extra candidate or restarting its depth pass.
                edge = _missed_conflict(chosen, excluded, conflicts, check)
                if edge is None:
                    raise ArithmeticError('candidate resumed without a missed conflict')
            if not edge or len(chosen) == limit:
                continue
            # These children partition extensions by their first chosen
            # member of edge. The excluded prefix avoids duplicate subsets
            # in one depth pass without storing all previously visited sets.
            children, forbidden = [], excluded
            for vertex in edge:
                check()
                children.append((chosen | {vertex}, forbidden))
                forbidden = forbidden | {vertex}
            pending.extend(reversed(children))


def search_euler_transversal(triangulation, allowed_types=None, *,
                             strategy='envelope', candidate_policy='subsets', max_nodes=None,
                             max_pivots=None, max_anchors=None,
                             max_hitting_subsets=10000,
                             lp_policy='polynomial', lp_fast_path_pivots=None,
                             max_ellipsoid_iterations=None, max_feasibility_calls=None,
                             check=lambda: None):
    """Return a positive canonical vector, complete negative tree, or a cap.

    Each incompatible positive basic ray supplies a necessary conflict-hitting
    constraint. Default candidates are tested in increasing size, then lexicographic
    order. A candidate restricts branching to its tetrahedra; a ray whose full
    conflict set misses that candidate refutes it. Source algebra and at most
    256 source-row dual bounds are shared across every candidate restart.

    All oracle nodes, LP pivots, anchors, ellipsoid updates and feasibility
    calls count against shared allowances across every candidate restart.
    lp_policy='bland' retains the comparison solver and ignores fallback caps.
    max_hitting_subsets separately charges each unique candidate subset tested
    against the learned constraints, including subsets rejected before an LP.
    candidate_policy='subsets' retains the increasing-cardinality stream.
    candidate_policy='conflicts' instead deepens a search on missed conflict
    choices, retaining at most 256 constraints. Here hitting_subsets_tested
    charges partial candidate-search states, including repeats at new depths;
    learned_conflicts counts cache insertions, including relearning after
    eviction. Excluded candidate choices never restrict the oracle Q mask.
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
    if type(candidate_policy) is not str or candidate_policy not in ('subsets', 'conflicts'):
        raise ValueError('candidate_policy must be subsets or conflicts')
    if strategy not in ('envelope', 'anchors'):
        raise ValueError('strategy must be envelope or anchors')
    validate_lp_controls(lp_policy, lp_fast_path_pivots,
                         max_ellipsoid_iterations, max_feasibility_calls)
    prepared = _prepare(triangulation, check)
    root = _mask(allowed_types, len(prepared['tetrahedra']))
    digest = _source_hash(triangulation)
    stats = _euler_search_stats()
    stats.update(hitting_subsets_tested=0, transversal_candidates=0,
                 transversal_restarts=0, learned_conflicts=0,
                 maximum_transversal_size=0, maximum_conflict_size=0,
                 peak_cached_conflicts=0, conflict_cache_evictions=0)
    oracle = _EulerMaskOracle(triangulation, prepared, strategy=strategy,
                              model='source', max_pivots=max_pivots,
                              max_anchors=max_anchors, check=check, stats=stats,
                              lp_policy=lp_policy, lp_fast_path_pivots=lp_fast_path_pivots,
                              max_ellipsoid_iterations=max_ellipsoid_iterations,
                              max_feasibility_calls=max_feasibility_calls)
    choices = {}
    for t, q in root:
        choices.setdefault(t, []).append(q)
    unresolved = tuple(t for t, qs in choices.items() if len(qs) > 1)
    conflicts = []

    def inconclusive(reason):
        return dict(status='INCONCLUSIVE', reason=reason, stats=stats)

    candidates = (_subset_candidates if candidate_policy == 'subsets' else _conflict_candidates)
    for candidate in candidates(unresolved, conflicts, stats, max_hitting_subsets, check):
        if candidate is None:
            return inconclusive('shared hitting-subset allowance exhausted')
        B, size = frozenset(candidate), len(candidate)
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
            stats['maximum_conflict_size'] = max(stats['maximum_conflict_size'], len(edge))
            if not already_known:
                if candidate_policy == 'conflicts' and len(conflicts) == _CONFLICT_CACHE_LIMIT:
                    del conflicts[0]
                    stats['conflict_cache_evictions'] += 1
                conflicts.append(edge)
                stats['learned_conflicts'] += 1
                stats['peak_cached_conflicts'] = max(stats['peak_cached_conflicts'], len(conflicts))
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
