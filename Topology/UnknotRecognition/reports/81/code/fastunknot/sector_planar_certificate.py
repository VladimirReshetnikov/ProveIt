"""Certificates and supplied-sector disc search using exact planar enumeration."""

from .normal_sector import build_sector_kernel, SearchLimit, _source_hash
from .normal_surface_geometry import _coordinates
from .normal_disk_kernel import (
    normal_compressing_disk_count, verify_normal_disk_count_certificate,
)
from .sector_planar import _Work, _rays


def _enumeration_proof(triangulation, support, quadrilaterals):
    return dict(schema='normal-sector-planar-rays-v1',
                source_sha256=_source_hash(triangulation),
                allowed_types=[list(pair) for pair in support],
                quadrilateral_rays=[list(q) for q in sorted(quadrilaterals)])


def certify_planar_sector(triangulation, allowed_types, *, check=lambda: None,
                          max_work=None):
    """Produce all non-link standard rays and an independently replayable list.

    A certificate's production is separate from its independent verification.
    A configured limit yields INCONCLUSIVE, without a partial coverage proof.
    """
    stats = {}
    work = _Work(check, max_work, stats)
    try:
        kernel = build_sector_kernel(triangulation, allowed_types,
                                    check=lambda: work.step('kernel_checkpoints'))
        stats.update(kernel.stats)
        rows = list(_rays(kernel, work, stats))
    except SearchLimit as exc:
        return dict(status='INCONCLUSIVE', reason=str(exc), stats=stats)
    rays = [tuple(surface[t][4 + q] for t, q in kernel.support) for surface in rows]
    return dict(status='COMPLETE', coordinates=rows, stats=stats,
                certificate=_enumeration_proof(triangulation, kernel.support, rays),
                trust='complete enumeration in the supplied sector')


def discover_planar_in_sector(triangulation, allowed_types, *, check=lambda: None,
                              max_work=None, max_orbit_cycles=None):
    """Search the complete standard ray list for an essential-disc component.

    Positive results use the existing witness schema and native independent
    disc replay.  Negative certificates bind complete planar enumeration plus
    all necessary negative component tests.  Neither result identifies the
    supplied triangulation with the exterior of a particular knot diagram.
    """
    if (max_orbit_cycles is not None and
            (type(max_orbit_cycles) is not int or max_orbit_cycles < 0)):
        raise ValueError('max_orbit_cycles must be a nonnegative integer or None')
    stats = dict(positive_euler_rays=0, orbit_queries=0)
    work = _Work(check, max_work, stats)
    records = []
    try:
        kernel = build_sector_kernel(triangulation, allowed_types,
                                    check=lambda: work.step('kernel_checkpoints'))
        stats.update(kernel.stats)
        for rows in _rays(kernel, work, stats):
            chi = _coordinates(kernel.prepared, rows, check)['euler_characteristic']
            q = [rows[t][4 + typ] for t, typ in kernel.support]
            record = dict(quadrilaterals=q, euler_characteristic=chi)
            records.append(record)
            if chi <= 0:
                continue
            stats['positive_euler_rays'] += 1
            stats['orbit_queries'] += 1
            result = normal_compressing_disk_count(triangulation, rows,
                max_cycles=max_orbit_cycles, record_certificate=True, check=check)
            if result['status'] != 'COMPLETE':
                raise SearchLimit('normal component query did not complete')
            proof = result['certificate']
            if not verify_normal_disk_count_certificate(triangulation, rows,
                                                         proof, check=check):
                raise ArithmeticError('native independent disc replay rejected')
            record['disk_certificate'] = proof
            if result['contains_compressing_disk']:
                certificate = dict(schema='normal-sector-witness-v1',
                    source_sha256=_source_hash(triangulation),
                    allowed_types=[list(pair) for pair in kernel.support],
                    coordinates=rows, disk_certificate=proof)
                return dict(status='DISC_FOUND', coordinates=rows,
                            certificate=certificate, stats=stats,
                            trust='essential disc in this supplied triangulation')
    except SearchLimit as exc:
        return dict(status='INCONCLUSIVE', reason=str(exc), stats=stats)
    status = ('NO_POSITIVE_EULER' if not stats['positive_euler_rays']
              else 'NO_VERTEX_DISC_IN_SECTOR')
    records.sort(key=lambda entry: entry['quadrilaterals'])
    enumeration = _enumeration_proof(triangulation, kernel.support,
                                    [tuple(r['quadrilaterals']) for r in records])
    certificate = dict(schema='normal-sector-planar-exhaustion-v1',
                       enumeration=enumeration, status=status, rays=records)
    return dict(status=status, certificate=certificate, stats=stats,
                trust='restricted sector exhaustion, not a knot verdict')
