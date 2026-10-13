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
            if (type(packet) is not dict or set(packet) not in
                    (fields, fields | {'matching_support_certificate'}) or
                    packet['schema'] != 'normal-sector-exhaustion-v1' or
                    type(packet['allowed_types']) is not list or
                    any(type(pair) is not list or len(pair) != 2 or
                        any(type(value) is not int for value in pair)
                        for pair in packet['allowed_types']) or
                    packet['allowed_types'] != allowed or
                    packet['phase'] != 'quadrilateral' or
                    packet['status'] != 'NO_POSITIVE_EULER' or
                    not verify_sector_exhaustion(triangulation, packet, check=check)):
                return False
        return True
    except (ValueError, TypeError, KeyError, IndexError, AttributeError, OverflowError):
        return False


def recognize_by_crushing(diagram, *, max_sectors=256, max_bases=10000,
                          max_crushes=None, sector_order='diversified', check=lambda: None):
    """Recognize with globally shared search caps, returning three-way status.

    ``max_sectors`` counts begun maximal sectors across every smaller source;
    ``max_bases`` counts begun enumerator candidates across those sectors.
    ``max_crushes`` counts performed strict reductions, including a terminal
    crush. Each allowance is a nonnegative integer or None (unbounded).
    Configured exhaustion returns INCONCLUSIVE with an authenticated partial
    chain. In particular, a caller-raised SearchLimit is not a local allowance.
    Polynomial source validation, forced-zero matching preprocessing, and
    independent certificate replay are outside the candidate-basis allowance.
    ``sector_order='diversified'`` first tries sixteen deterministic seeded
    assignments, then every remaining assignment canonically; ``'canonical'``
    provides the ordinary lexicographic traversal for comparisons. Each full
    assignment is tried once per source, and negative proof order is canonical.
    """
    for name, value in (('max_sectors', max_sectors), ('max_bases', max_bases),
                        ('max_crushes', max_crushes)):
        if value is not None and (type(value) is not int or value < 0):
            raise ValueError(name + ' must be a nonnegative integer or None')
    if sector_order not in ('diversified', 'canonical'):
        raise ValueError('sector_order must be diversified or canonical')
    return _safe_call(_recognize_by_crushing, check, diagram,
                      max_sectors=max_sectors, max_bases=max_bases,
                      max_crushes=max_crushes, sector_order=sector_order)


def _recognize_by_crushing(diagram, *, max_sectors, max_bases, max_crushes, sector_order, check):
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
                 forced_zero_types=0)

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

    while current is not None:
        check()
        stats['stages'] += 1
        count = len(current['tetrahedra'])
        digest = _source_hash(current)
        exhaustion = {}
        for assignment in _sector_assignments(count, sector_order, check):
            check()
            if max_sectors is not None and stats['sectors_attempted'] >= max_sectors:
                return inconclusive('shared maximal-sector allowance exhausted')
            stats['sectors_attempted'] += 1
            allowed = [[t, q] for t, q in enumerate(assignment)]
            kernel = build_sector_kernel(current, allowed, check=check)
            retained = list(range(count))
            matching_proof = None
            # Retain the existing polynomial sufficient source-row screen.
            # Its fixed point is not an LP completeness test: every remaining
            # coordinate still goes through complete Q-corner enumeration.
            if len(kernel.basis) > 3:
                stats['matching_support_checks'] += 1
                retained, matching_proof = matching_support(kernel, check)
                if matching_proof is not None:
                    stats['matching_support_reductions'] += 1
                    stats['forced_zero_types'] += count-len(retained)
                    kernel = build_sector_kernel(current, [allowed[i] for i in retained],
                                                 check=check)
            allowance = None if max_bases is None else max_bases-stats['bases_attempted']
            local = {}
            transcript = []
            positive = None
            try:
                for rows in sector_rays(kernel, phase='quadrilateral', method='auto',
                                        max_bases=allowance, stats=local, check=check):
                    check()
                    stats['rays_examined'] += 1
                    chi = _coordinates(kernel.prepared, rows, check)['euler_characteristic']
                    if chi > 0:
                        stats['positive_euler_rays'] += 1
                        positive = rows
                        break
                    # The global sector always keeps one allowed type per
                    # tetrahedron, including source-proven forced-zero types.
                    quadrilaterals = [0]*count
                    for i, (t, q) in zip(retained, kernel.support):
                        quadrilaterals[i] = rows[t][4+q]
                    transcript.append(dict(quadrilaterals=quadrilaterals,
                                           euler_characteristic=chi))
            except SearchLimit as error:
                stats['bases_attempted'] += local.get('bases_attempted', 0)
                return inconclusive(str(error))
            stats['bases_attempted'] += local.get('bases_attempted', 0)
            if positive is None:
                packet = dict(schema='normal-sector-exhaustion-v1',
                    source_sha256=digest, allowed_types=allowed, phase='quadrilateral',
                    status='NO_POSITIVE_EULER', rays=json_safe(transcript))
                if matching_proof is not None:
                    packet['matching_support_certificate'] = json_safe(matching_proof)
                exhaustion[assignment] = packet
                continue
            if max_crushes is not None and len(steps) >= max_crushes:
                return inconclusive('shared crushing-step allowance exhausted')
            result = crush_normal_ray(current, positive, check=check)
            packet = result['certificate']
            if not verify_normal_crushing(current, packet, check=check):
                raise ArithmeticError('independent normal crushing replay failed')
            successor = packet['successor']
            if successor is not None and len(successor['tetrahedra']) >= count:
                raise ArithmeticError('normal crushing did not strictly shrink the source')
            steps.append(packet)
            stats['crushing_steps'] += 1
            current = successor
            # Every sector/exhaustion packet is relative to the old source;
            # restart all maximal assignments on the authenticated successor.
            break
        else:
            return conclusive('KNOTTED', [exhaustion[a] for a in sorted(exhaustion)])
    return conclusive('UNKNOT', [])
