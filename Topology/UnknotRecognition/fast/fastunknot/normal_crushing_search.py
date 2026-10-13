"""Complete bounded native recognition by positive-ray crushing and restart.

This additive driver authenticates the diagram exterior, searches all maximal
quadrilateral sectors, and consumes every positive canonical Q-corner lift by
crushing. Each such lift is a non-link standard extreme ray; each nonterminal
crush strictly decreases the tetrahedron count. Canonical Euler characteristic
is convex on the normalized Q cone, so Q corners suffice for positive discovery.
No rejected-surface list or geometric rejection allowance is needed.

With allowances removed the algorithm terminates, but maximal-sector search
and independent dense exhaustion replay remain exponential. This module does
not change the default recognition dispatcher or claim quasi-polynomial time.
"""
from itertools import product
from random import Random

from .diagram import Diagram
from .integer_codec import json_safe
from .normal_crushing_chain import verify_crushing_chain
from .normal_sector_verify import verify_sector_exhaustion
from .normal_euler_verify import verify_sector_euler_certificate


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
    requires a reduced chain and all 3**t maximal sectors, in canonical product
    order, independently exhausted with no positive Euler Q corner. Missing sectors,
    partial discovery, and finite search allowances never certify knottedness.
    Malformed packets return False; all caller exceptions propagate unchanged.
    """
    return _safe_call(_verify_crushing_recognition, check, diagram, certificate)


def _verify_crushing_recognition(diagram, certificate, *, check):
    check()
    try:
        if (type(certificate) is not dict or
                set(certificate) != {'schema', 'status', 'chain', 'exhaustion'} or
                certificate['schema'] != 'diagram-crushing-recognition-v1' or
                certificate['status'] not in ('UNKNOT', 'KNOTTED') or
                type(certificate['exhaustion']) is not list):
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
    'anchors'. These finite exact simplex computations have no polynomial
    pivot bound. Negative recognition may mix independently checked Euler-LP
    and corner-exhaustion packets, always on all full final-source assignments.

    ``reduce_vertices=True`` first constructs expanded-edge-link positive rays
    on each source with multiple vertices, without sector search. Their crushes
    use the same independent verifier and shared ``max_crushes`` allowance.
    Strict tetrahedron descent reaches a one-vertex source or a terminal unknot
    chain in polynomially many such steps. This does not bound the remaining
    sector family. ``False`` retains the search-only policy for comparisons.
    """
    for name, value in (('max_sectors', max_sectors), ('max_bases', max_bases),
                        ('max_crushes', max_crushes), ('max_pivots', max_pivots),
                        ('max_anchors', max_anchors)):
        if value is not None and (type(value) is not int or value < 0):
            raise ValueError(name + ' must be a nonnegative integer or None')
    if sector_order not in ('diversified', 'canonical'):
        raise ValueError('sector_order must be diversified or canonical')
    if sector_quantum is not None and (type(sector_quantum) is not int or sector_quantum <= 0):
        raise ValueError('sector_quantum must be a positive integer or None')
    if sector_method not in ('corners', 'lp'):
        raise ValueError('sector_method must be corners or lp')
    if lp_strategy not in ('anchors', 'envelope'):
        raise ValueError('lp_strategy must be anchors or envelope')
    if type(reduce_vertices) is not bool:
        raise ValueError('reduce_vertices must be a boolean')
    return _safe_call(_recognize_by_crushing, check, diagram,
                      max_sectors=max_sectors, max_bases=max_bases,
                      max_crushes=max_crushes, sector_order=sector_order,
                      sector_quantum=sector_quantum, sector_method=sector_method,
                      max_pivots=max_pivots, max_anchors=max_anchors,
                      lp_strategy=lp_strategy, reduce_vertices=reduce_vertices)


def _recognize_by_crushing(diagram, *, max_sectors, max_bases, max_crushes,
                          sector_order, sector_quantum, sector_method,
                          max_pivots, max_anchors, lp_strategy, reduce_vertices, check):
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
    if sector_method == 'lp':
        stats.update(lp_calls=0, lp_pivots=0, anchors_tested=0,
                     reused_anchors=0, envelope_calls=0, lp_tableau_updates=0,
                     maximum_tableau_bits=0, extraction_steps=0)
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
        certificate = dict(schema='diagram-crushing-recognition-v1', status=status,
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
            max_anchors=allowance(max_anchors, stats['anchors_tested']), check=check)
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
                             or (max_anchors is not None and stats['anchors_tested'] >= max_anchors))
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
