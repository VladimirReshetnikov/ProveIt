"""Complete bounded native recognition by positive-ray crushing and restart.

This additive driver authenticates the diagram exterior, searches all maximal
quadrilateral sectors, and consumes every positive canonical Q-corner lift by
crushing. Each such lift is a non-link standard extreme ray; each nonterminal
crush strictly decreases the tetrahedron count. Canonical Euler characteristic
is convex on the normalized Q cone, so Q corners suffice for positive discovery.
No rejected-surface list or geometric rejection allowance is needed.

An optional exact Euler tree closes whole partial-sector masks with checked
Farkas duals. With allowances removed the algorithm terminates, but the
worst-case search and complete negative certificate can remain exponential. This module does
not change the default recognition dispatcher or claim quasi-polynomial time.
"""
from itertools import product
from random import Random

from .diagram import Diagram
from .integer_codec import json_safe
from .normal_crushing_chain import verify_crushing_chain
from .normal_sector_verify import verify_sector_exhaustion
from .normal_euler_verify import verify_sector_euler_certificate
from .normal_euler_tree_verify import verify_euler_branch_tree
from .euler_lp_budget import (fallback_statistics, validate_lp_controls, merge_fallback)


class _CallbackRaised(BaseException):
    def __init__(self, error):
        self.error = error
        self.traceback = error.__traceback__


def _safe_call(function, check, *args, **kwargs):
    def guarded():
        try:
            check()
        except BaseException as error:
            raise _CallbackRaised(error) from None
    try:
        return function(*args, check=guarded, **kwargs)
    except _CallbackRaised as interruption:
        raise interruption.error.with_traceback(interruption.traceback) from None


def _sector_assignments(count, order, check):
    """A fixed diversified prefix, then complete lexicographic coverage once.

    Sixteen seeded draws are a bounded heuristic, not a probability assumption.
    Every remaining assignment follows in canonical order. The negative proof
    is separately sorted into canonical order and independently checked there.
    """
    seen = set()
    if order == 'diversified':
        random = Random(37)
        for _ in range(16):
            check()
            assignment = tuple(random.randrange(3) for _ in range(count))
            if assignment not in seen:
                seen.add(assignment)
                yield assignment
    for assignment in product(range(3), repeat=count):
        check()
        if assignment not in seen:
            yield assignment


def _sector_schedule(count, order, quantum, finished, check):
    """Grow both the explored prefix and each unfinished job's allowance.

    ``finished`` is the caller's live mapping of completed negative sectors.
    A round visits the first min(16*2**r, 3**count) assignments, allowing
    quantum*2**r candidates per unfinished job.  It does not wait for a full
    exponential first pass before revisiting early expensive sectors.
    """
    assignments = _sector_assignments(count, order, check)
    if quantum is None:
        for assignment in assignments:
            yield assignment, None
        return
    total = 3**count
    prefix, width, allowance = [], min(16, total), quantum
    while len(finished) < total:
        for i in range(width):
            check()
            if i == len(prefix):
                prefix.append(next(assignments))
            assignment = prefix[i]
            if assignment not in finished:
                yield assignment, allowance
        width = min(total, 2*width)
        allowance *= 2


def verify_crushing_recognition(diagram, certificate, *, check=lambda: None):
    """Replay source provenance, all crushes, and every final negative sector.

    The verifier imports no source constructor, sheller, ray enumerator or
    crushing producer. UNKNOT requires a terminal authenticated chain. KNOTTED
    requires a reduced chain and complete final-source coverage, either all
    3**t maximal sectors in canonical product order (v1) or an independently
    checked Euler relaxation branch tree covering their union (v2). Missing sectors,
    partial discovery, and finite search allowances never certify knottedness.
    Malformed packets return False; all caller exceptions propagate unchanged.
    """
    return _safe_call(_verify_crushing_recognition, check, diagram, certificate)


def _verify_crushing_recognition(diagram, certificate, *, check):
    check()
    try:
        if (type(certificate) is not dict or
                set(certificate) != {'schema', 'status', 'chain', 'exhaustion'} or
                certificate['schema'] not in ('diagram-crushing-recognition-v1',
                                              'diagram-crushing-recognition-v2') or
                certificate['status'] not in ('UNKNOT', 'KNOTTED')):
            return False
        tree_proof = certificate['schema'] == 'diagram-crushing-recognition-v2'
        if tree_proof:
            if certificate['status'] != 'KNOTTED' or type(certificate['exhaustion']) is not dict:
                return False
        elif type(certificate['exhaustion']) is not list:
            return False
        chain = certificate['chain']
        if not verify_crushing_chain(diagram, chain, check=check):
            return False
        if certificate['status'] == 'UNKNOT':
            return chain['status'] == 'UNKNOT' and not certificate['exhaustion']
        if chain['status'] != 'REDUCED':
            return False
        triangulation = chain['triangulation']
        count = len(triangulation['tetrahedra'])
        packets = certificate['exhaustion']
        if tree_proof:
            allowed = [[t, q] for t in range(count) for q in range(3)]
            return (packets.get('allowed_types') == allowed and
                    verify_euler_branch_tree(triangulation, packets, check=check))
        if len(packets) != 3**count:
            return False
        fields = {'schema', 'source_sha256', 'allowed_types', 'phase', 'status', 'rays'}
        for assignment, packet in zip(product(range(3), repeat=count), packets):
            check()
            allowed = [[t, q] for t, q in enumerate(assignment)]
            if (type(packet) is not dict or
                    type(packet.get('allowed_types')) is not list or
                    any(type(pair) is not list or len(pair) != 2 or
                        any(type(value) is not int for value in pair)
                        for pair in packet['allowed_types']) or
                    packet['allowed_types'] != allowed or
                    packet.get('status') != 'NO_POSITIVE_EULER'):
                return False
            if packet.get('schema') == 'normal-sector-exhaustion-v1':
                if (set(packet) not in (fields, fields | {'matching_support_certificate'})
                        or packet.get('phase') != 'quadrilateral'
                        or not verify_sector_exhaustion(triangulation, packet, check=check)):
                    return False
            elif packet.get('schema') in ('normal-sector-euler-lp-v1',
                                          'normal-sector-euler-reduction-v1'):
                if not verify_sector_euler_certificate(triangulation, packet, check=check):
                    return False
            else:
                return False
        return True
    except (ValueError, TypeError, KeyError, IndexError, AttributeError, OverflowError):
        return False


def recognize_by_crushing(diagram, *, max_sectors=256, max_bases=10000,
                          max_crushes=None, sector_order='diversified',
                          sector_quantum=64, sector_method='corners',
                          max_pivots=10000, max_anchors=10000,
                          lp_strategy='envelope', reduce_vertices=True,
                          max_tree_nodes=256, tree_model='source',
                          max_hitting_subsets=10000,
                          transversal_candidate_policy='subsets',
                          lp_policy='polynomial', lp_fast_path_pivots=None,
                          max_ellipsoid_iterations=10000, max_feasibility_calls=10000,
                          check=lambda: None):
    """Recognize with globally shared search caps, returning three-way status.

    ``max_sectors`` counts distinct begun maximal sectors across smaller sources;
    ``max_bases`` counts every begun enumerator candidate, including work repeated
    by restarting an unfinished sector with a larger allowance.
    ``max_crushes`` counts performed strict reductions, including a terminal
    crush. Each allowance is a nonnegative integer or None (unbounded).
    Configured exhaustion returns INCONCLUSIVE with an authenticated partial
    chain. In particular, a caller-raised SearchLimit is not a local allowance.
    Polynomial source validation, forced-zero matching preprocessing, and
    independent certificate replay are outside the candidate-basis allowance.
    ``sector_order='diversified'`` first tries sixteen deterministic seeded
    assignments, then every remaining assignment canonically; ``'canonical'``
    provides ordinary lexicographic order for comparisons. ``sector_quantum``
    starts a fair sequence of rounds: visit sixteen assignments with this many
    candidates each, then double both prefix length and per-sector allowance.
    Completed negatives are skipped. Source kernels and matching reductions are
    cached for unfinished jobs, then discarded on crushing. ``None`` preserves
    sequential traversal. Final negative proof order is always canonical.

    ``sector_method='lp'`` uses exact Euler feasibility and support extraction
    instead of corner enumeration. Its separate global ``max_pivots`` and
    ``max_anchors`` allowances count every repeated pivot and anchor; bases are
    unused. The per-attempt quantum applies to each LP count separately.
    ``lp_strategy`` selects 'envelope' (actual-point check then anchors) or
    'anchors'. The default LP policy uses a polynomially capped Bland prefix
    and exact rational ellipsoid recovery; ``lp_policy='bland'`` retains the
    legacy comparison policy. Negative recognition may mix independently checked Euler-LP
    and corner-exhaustion packets, always on all full final-source assignments.

    ``reduce_vertices=True`` first constructs expanded-edge-link positive rays
    on each source with multiple vertices, without sector search. Their crushes
    use the same independent verifier and shared ``max_crushes`` allowance.
    Strict tetrahedron descent reaches a one-vertex source or a terminal unknot
    chain in polynomially many such steps. This does not bound the remaining
    sector family. ``False`` retains the search-only policy for comparisons.

    ``sector_method='tree'`` replaces the flat assignment loop with a verified
    tree of possibly incompatible Q masks. Negative relaxation certificates
    close whole subfamilies; an incompatible positive point selects a complete
    quadrilateral split. ``max_tree_nodes`` counts all begun nodes across
    successors, while pivots and anchors retain their shared global limits.
    Sector and corner allowances are unused in this mode. Complete negative
    trees use the v2 recognition schema; terminal positive chains keep v1.
    ``tree_model='source'`` retains one full-source Q model across nodes and
    rechecks cached duals on each current mask. ``'restricted'`` rebuilds the
    algebra per mask and retains separate node caches for comparison.

    ``sector_method='transversal'`` learns full conflict sets from incompatible
    positive Q rays, then searches with splits confined to a candidate hitting
    set. Failed candidates count toward the same global node, pivot and anchor
    caps. ``max_hitting_subsets`` counts every tested subset, including those
    filtered without an LP, across all candidates and crushing successors.
    Learning and dual caches restart on each new source. This policy requires
    ``tree_model='source'`` and uses the same independently checked v2 negative
    recognition schema. No general small-transversal bound is assumed.

    ``transversal_candidate_policy='conflicts'`` selects iterative deepening
    on missed conflict choices with a 256-edge cache. The default 'subsets'
    retains the unique-subset comparison stream. In conflicts mode the shared
    max_hitting_subsets limit charges every partial candidate-search state,
    including repeat visits at larger depths, before any candidate LP work.

    ``max_ellipsoid_iterations`` and ``max_feasibility_calls`` count fallback
    work across all anchors, nodes, candidate restarts and crushing successors.
    Both default to 10000; None removes a cap. Flat LP scheduling also applies
    its per-attempt quantum to these counts. ``lp_fast_path_pivots`` can lower
    the internal polynomial prefix limit, useful for fallback comparisons.
    The user's max_pivots remains a hard simplex-work cap and prevents fallback
    when exhausted. The Bland comparison ignores unused fallback budgets.
    """
    for name, value in (('max_sectors', max_sectors), ('max_bases', max_bases),
                        ('max_crushes', max_crushes), ('max_pivots', max_pivots),
                        ('max_anchors', max_anchors), ('max_tree_nodes', max_tree_nodes),
                        ('max_hitting_subsets', max_hitting_subsets)):
        if value is not None and (type(value) is not int or value < 0):
            raise ValueError(name + ' must be a nonnegative integer or None')
    if sector_order not in ('diversified', 'canonical'):
        raise ValueError('sector_order must be diversified or canonical')
    if sector_quantum is not None and (type(sector_quantum) is not int or sector_quantum <= 0):
        raise ValueError('sector_quantum must be a positive integer or None')
    if sector_method not in ('corners', 'lp', 'tree', 'transversal'):
        raise ValueError('sector_method must be corners, lp, tree or transversal')
    if lp_strategy not in ('anchors', 'envelope'):
        raise ValueError('lp_strategy must be anchors or envelope')
    if type(reduce_vertices) is not bool:
        raise ValueError('reduce_vertices must be a boolean')
    if tree_model not in ('source', 'restricted'):
        raise ValueError('tree_model must be source or restricted')
    if sector_method == 'transversal' and tree_model != 'source':
        raise ValueError('transversal search requires tree_model=source')
    if (type(transversal_candidate_policy) is not str
            or transversal_candidate_policy not in ('subsets', 'conflicts')):
        raise ValueError('transversal_candidate_policy must be subsets or conflicts')
    validate_lp_controls(lp_policy, lp_fast_path_pivots,
                         max_ellipsoid_iterations, max_feasibility_calls)
    return _safe_call(_recognize_by_crushing, check, diagram,
                      max_sectors=max_sectors, max_bases=max_bases,
                      max_crushes=max_crushes, sector_order=sector_order,
                      sector_quantum=sector_quantum, sector_method=sector_method,
                      max_pivots=max_pivots, max_anchors=max_anchors,
                      lp_strategy=lp_strategy, reduce_vertices=reduce_vertices,
                      max_tree_nodes=max_tree_nodes, tree_model=tree_model,
                      max_hitting_subsets=max_hitting_subsets,
                      transversal_candidate_policy=transversal_candidate_policy,
                      lp_policy=lp_policy, lp_fast_path_pivots=lp_fast_path_pivots,
                      max_ellipsoid_iterations=max_ellipsoid_iterations,
                      max_feasibility_calls=max_feasibility_calls)


def _recognize_by_crushing(diagram, *, max_sectors, max_bases, max_crushes,
                          sector_order, sector_quantum, sector_method,
                          max_pivots, max_anchors, lp_strategy, reduce_vertices,
                          max_tree_nodes, tree_model, max_hitting_subsets,
                          transversal_candidate_policy,
                          lp_policy, lp_fast_path_pivots,
                          max_ellipsoid_iterations, max_feasibility_calls, check):
    # Keep producer imports outside the independent verifier's import path.
    from .diagram_exterior import diagram_exterior
    from .diagram_exterior_verify import verify_diagram_exterior
    from .boundary_shellings import shell_boundary
    from .boundary_shellings_verify import verify_boundary_shellings
    from .normal_crushing import crush_normal_ray
    from .normal_crushing_verify import verify_normal_crushing
    from .normal_sector import build_sector_kernel, sector_rays, SearchLimit, _source_hash
    from .sector_matching_support import matching_support
    from .normal_surface_geometry import _coordinates
    from .normal_euler import decide_sector_euler
    from .positive_ray import extract_positive_ray
    from .normal_vertex_reduction import vertex_reduction_ray
    from .normal_euler_tree import search_euler_tree
    from .normal_euler_transversal import search_euler_transversal

    check()
    source = Diagram.from_pd(diagram.pd)
    initial = diagram_exterior(source, check=check)
    if not verify_diagram_exterior(source, initial, check=check):
        raise ArithmeticError('independent diagram exterior replay failed')
    shelled = shell_boundary(initial, check=check)
    shelling = {key: shelled[key] for key in ('triangulation', 'moves')}
    current = shelling['triangulation']
    if not verify_boundary_shellings(initial, current, shelling['moves'], check=check):
        raise ArithmeticError('independent boundary shelling replay failed')
    steps = []
    stats = dict(initial_tetrahedra=len(initial['tetrahedra']),
                 shelled_tetrahedra=len(current['tetrahedra']),
                 sectors_attempted=0, bases_attempted=0, rays_examined=0,
                 positive_euler_rays=0, crushing_steps=0, stages=0,
                 matching_support_checks=0, matching_support_reductions=0,
                 forced_zero_types=0, sector_restarts=0,
                 sector_quantum_exhaustions=0, max_cached_sector_jobs=0)
    if sector_method in ('lp', 'tree', 'transversal'):
        stats.update(lp_calls=0, lp_pivots=0, anchors_tested=0,
                     reused_anchors=0, envelope_calls=0, lp_tableau_updates=0,
                     maximum_tableau_bits=0, extraction_steps=0)
        stats.update(fallback_statistics())
    if sector_method in ('tree', 'transversal'):
        stats.update(nodes_attempted=0, branch_splits=0, negative_leaves=0,
                     positive_relaxations=0, incompatible_positive_points=0,
                     nonpositive_envelope_points=0, reused_envelopes=0,
                     maximum_tree_depth=0, kernel_preparations=0)
    if sector_method == 'transversal':
        stats.update(hitting_subsets_tested=0, transversal_candidates=0,
                     transversal_restarts=0, learned_conflicts=0,
                     maximum_transversal_size=0, maximum_conflict_size=0,
                     peak_cached_conflicts=0, conflict_cache_evictions=0)
    if reduce_vertices:
        stats.update(vertex_reduction_calls=0, vertex_reduction_crushes=0)

    def chain():
        return dict(schema='diagram-crushing-v1', input_pd=[list(row) for row in source.pd],
                    source_triangulation=initial, shelling=shelling, steps=steps,
                    status='UNKNOT' if current is None else 'REDUCED',
                    triangulation=current)

    def inconclusive(reason):
        return dict(status='INCONCLUSIVE', reason=reason, stats=stats, partial_chain=chain())

    def conclusive(status, exhaustion):
        schema = ('diagram-crushing-recognition-v2' if type(exhaustion) is dict
                  else 'diagram-crushing-recognition-v1')
        certificate = dict(schema=schema, status=status,
                           chain=chain(), exhaustion=exhaustion)
        if not verify_crushing_recognition(source, certificate, check=check):
            raise ArithmeticError('independent crushing recognition replay failed')
        return dict(status=status, certificate=certificate, stats=stats)

    def apply_crush(coordinates):
        nonlocal current
        count = len(current['tetrahedra'])
        result = crush_normal_ray(current, coordinates, check=check)
        packet = result['certificate']
        if not verify_normal_crushing(current, packet, check=check):
            raise ArithmeticError('independent normal crushing replay failed')
        successor = packet['successor']
        if successor is not None and len(successor['tetrahedra']) >= count:
            raise ArithmeticError('normal crushing did not strictly shrink the source')
        steps.append(packet)
        stats['crushing_steps'] += 1
        current = successor

    def prepare_job(assignment):
        allowed = [[t, q] for t, q in enumerate(assignment)]
        kernel = build_sector_kernel(current, allowed, check=check)
        retained = list(range(len(assignment)))
        matching_proof = None
        # This source-row screen is sufficient only. Remaining coordinates
        # still pass through complete Q-corner enumeration.
        if len(kernel.basis) > 3:
            stats['matching_support_checks'] += 1
            retained, matching_proof = matching_support(kernel, check)
            if matching_proof is not None:
                stats['matching_support_reductions'] += 1
                stats['forced_zero_types'] += len(assignment)-len(retained)
                kernel = build_sector_kernel(current, [allowed[i] for i in retained],
                                             check=check)
        return dict(kernel=kernel, allowed=allowed, retained=retained,
                    matching_proof=matching_proof)

    def attempt(job, local_candidate_allowance):
        """One restartable Q-corner attempt; partial transcripts are discarded.

        Completed negative output is returned only after generator exhaustion.
        Caller exceptions escape through _CallbackRaised, including SearchLimit.
        All repeated candidate and ray work is charged to shared statistics.
        """
        kernel, retained = job['kernel'], job['retained']
        local, transcript = {}, []
        try:
            for rows in sector_rays(kernel, phase='quadrilateral', method='auto',
                                    max_bases=local_candidate_allowance,
                                    stats=local, check=check):
                check()
                stats['rays_examined'] += 1
                chi = _coordinates(kernel.prepared, rows, check)['euler_characteristic']
                if chi > 0:
                    stats['positive_euler_rays'] += 1
                    return dict(status='POSITIVE', coordinates=rows)
                quadrilaterals = [0]*len(job['allowed'])
                for i, (t, q) in zip(retained, kernel.support):
                    quadrilaterals[i] = rows[t][4+q]
                transcript.append(dict(quadrilaterals=quadrilaterals,
                                       euler_characteristic=chi))
        except SearchLimit as error:
            return dict(status='UNFINISHED', reason=str(error))
        finally:
            stats['bases_attempted'] += local.get('bases_attempted', 0)
        packet = dict(schema='normal-sector-exhaustion-v1', source_sha256=digest,
            allowed_types=job['allowed'], phase='quadrilateral',
            status='NO_POSITIVE_EULER', rays=json_safe(transcript))
        if job['matching_proof'] is not None:
            packet['matching_support_certificate'] = json_safe(job['matching_proof'])
        return dict(status='NEGATIVE', certificate=packet)

    def attempt_lp(job, quantum):
        def allowance(limit, used):
            remaining = None if limit is None else limit-used
            return (remaining if quantum is None else quantum if remaining is None
                    else min(quantum, remaining))
        result = decide_sector_euler(current, job['kernel'].support,
            strategy=lp_strategy, max_pivots=allowance(max_pivots, stats['lp_pivots']),
            max_anchors=allowance(max_anchors, stats['anchors_tested']),
            lp_policy=lp_policy, lp_fast_path_pivots=lp_fast_path_pivots,
            max_ellipsoid_iterations=allowance(max_ellipsoid_iterations, stats['lp_ellipsoid_iterations']),
            max_feasibility_calls=allowance(max_feasibility_calls, stats['lp_feasibility_calls']),
            check=check)
        merge_fallback(stats, result['stats'])
        for name in ('lp_calls', 'lp_pivots', 'anchors_tested', 'reused_anchors',
                     'envelope_calls', 'lp_tableau_updates'):
            stats[name] += result['stats'][name]
        stats['maximum_tableau_bits'] = max(stats['maximum_tableau_bits'],
                                           result['stats']['maximum_tableau_bits'])
        if result['status'] == 'INCONCLUSIVE':
            return dict(status='UNFINISHED', reason=result['reason'])
        proof = result['certificate']
        if job['matching_proof'] is not None:
            proof = dict(schema='normal-sector-euler-reduction-v1',
                status=result['status'], source_sha256=digest, allowed_types=job['allowed'],
                matching_support_certificate=json_safe(job['matching_proof']),
                euler_certificate=proof)
        if not verify_sector_euler_certificate(current, proof, check=check):
            raise ArithmeticError('independent Euler-LP replay failed')
        if result['status'] == 'NO_POSITIVE_EULER':
            return dict(status='NEGATIVE', certificate=proof)
        extracted = extract_positive_ray(current, result['coordinates'], check=check)
        stats['rays_examined'] += 1
        stats['positive_euler_rays'] += 1
        stats['extraction_steps'] += extracted['stats']['descent_steps']
        return dict(status='POSITIVE', coordinates=extracted['coordinates'])

    while current is not None:
        check()
        stats['stages'] += 1
        if reduce_vertices:
            reduction = vertex_reduction_ray(current, check=check)
            stats['vertex_reduction_calls'] += 1
            if reduction['status'] == 'POSITIVE_EULER':
                stats['rays_examined'] += 1
                stats['positive_euler_rays'] += 1
                if max_crushes is not None and len(steps) >= max_crushes:
                    return inconclusive('shared crushing-step allowance exhausted')
                apply_crush(reduction['coordinates'])
                stats['vertex_reduction_crushes'] += 1
                continue
            if reduction['status'] != 'ONE_VERTEX':
                raise ArithmeticError('unexpected vertex reduction outcome')
        count = len(current['tetrahedra'])
        digest = _source_hash(current)
        if sector_method in ('tree', 'transversal'):
            def remaining(cap, field):
                return None if cap is None else cap-stats[field]
            options = dict(strategy=lp_strategy,
                max_nodes=remaining(max_tree_nodes, 'nodes_attempted'),
                max_pivots=remaining(max_pivots, 'lp_pivots'),
                max_anchors=remaining(max_anchors, 'anchors_tested'),
                lp_policy=lp_policy, lp_fast_path_pivots=lp_fast_path_pivots,
                max_ellipsoid_iterations=remaining(max_ellipsoid_iterations, 'lp_ellipsoid_iterations'),
                max_feasibility_calls=remaining(max_feasibility_calls, 'lp_feasibility_calls'),
                check=check)
            if sector_method == 'tree':
                result = search_euler_tree(current, model=tree_model, **options)
            else:
                result = search_euler_transversal(current,
                    max_hitting_subsets=remaining(max_hitting_subsets, 'hitting_subsets_tested'),
                    candidate_policy=transversal_candidate_policy,
                    **options)
                for field in ('hitting_subsets_tested', 'transversal_candidates',
                              'transversal_restarts', 'learned_conflicts', 'conflict_cache_evictions'):
                    stats[field] += result['stats'][field]
                for field in ('maximum_transversal_size', 'maximum_conflict_size', 'peak_cached_conflicts'):
                    stats[field] = max(stats[field], result['stats'][field])
            merge_fallback(stats, result['stats'])
            for field in ('nodes_attempted', 'branch_splits', 'negative_leaves', 'lp_calls',
                          'lp_pivots', 'anchors_tested', 'reused_anchors', 'envelope_calls',
                          'lp_tableau_updates', 'positive_relaxations',
                          'incompatible_positive_points', 'nonpositive_envelope_points',
                          'reused_envelopes', 'kernel_preparations'):
                stats[field] += result['stats'][field]
            stats['maximum_tree_depth'] = max(stats['maximum_tree_depth'],
                                              result['stats']['maximum_depth'])
            stats['maximum_tableau_bits'] = max(stats['maximum_tableau_bits'],
                                               result['stats']['maximum_tableau_bits'])
            if result['status'] == 'INCONCLUSIVE':
                return inconclusive(result['reason'])
            if result['status'] == 'NO_POSITIVE_EULER':
                return conclusive('KNOTTED', result['certificate'])
            if result['status'] != 'POSITIVE_EULER':
                raise ArithmeticError('unexpected Euler tree outcome')
            extracted = extract_positive_ray(current, result['coordinates'], check=check)
            stats['extraction_steps'] += extracted['stats']['descent_steps']
            stats['rays_examined'] += 1
            stats['positive_euler_rays'] += 1
            if max_crushes is not None and len(steps) >= max_crushes:
                return inconclusive('shared crushing-step allowance exhausted')
            apply_crush(extracted['coordinates'])
            continue
        exhaustion = {}
        jobs = {}
        for assignment, quantum in _sector_schedule(count, sector_order, sector_quantum,
                                                    exhaustion, check):
            check()
            if assignment not in jobs:
                if max_sectors is not None and stats['sectors_attempted'] >= max_sectors:
                    return inconclusive('shared maximal-sector allowance exhausted')
                stats['sectors_attempted'] += 1
                jobs[assignment] = prepare_job(assignment)
                stats['max_cached_sector_jobs'] = max(stats['max_cached_sector_jobs'], len(jobs))
            else:
                stats['sector_restarts'] += 1
            if sector_method == 'lp':
                result = attempt_lp(jobs[assignment], quantum)
                exhausted = ((max_pivots is not None and stats['lp_pivots'] >= max_pivots)
                             or (max_anchors is not None and stats['anchors_tested'] >= max_anchors)
                             or (max_ellipsoid_iterations is not None
                                 and stats['lp_ellipsoid_iterations'] >= max_ellipsoid_iterations
                                 and result.get('reason') == 'shared ellipsoid iteration allowance exhausted')
                             or (max_feasibility_calls is not None
                                 and stats['lp_feasibility_calls'] >= max_feasibility_calls
                                 and result.get('reason') == 'shared feasibility decision allowance exhausted'))
            else:
                remaining = None if max_bases is None else max_bases-stats['bases_attempted']
                allowance = (remaining if quantum is None else quantum if remaining is None
                             else min(quantum, remaining))
                result = attempt(jobs[assignment], allowance)
                exhausted = remaining is not None and (quantum is None or remaining <= quantum)
            if result['status'] == 'UNFINISHED':
                if quantum is None or exhausted:
                    return inconclusive(result['reason'])
                stats['sector_quantum_exhaustions'] += 1
                continue
            if result['status'] == 'NEGATIVE':
                exhaustion[assignment] = result['certificate']
                del jobs[assignment]
                continue
            if max_crushes is not None and len(steps) >= max_crushes:
                return inconclusive('shared crushing-step allowance exhausted')
            apply_crush(result['coordinates'])
            # Every sector/exhaustion packet is relative to the old source;
            # restart all maximal assignments on the authenticated successor.
            break
        else:
            return conclusive('KNOTTED', [exhaustion[a] for a in sorted(exhaustion)])
    return conclusive('UNKNOT', [])
