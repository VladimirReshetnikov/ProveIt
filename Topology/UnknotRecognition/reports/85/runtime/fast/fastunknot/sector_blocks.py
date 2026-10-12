"""Exact coordinate-block decomposition for supplied normal sectors.

This opt-in module does not change the recognizer.  Quadrilateral extreme
rays split over matching-coordinate blocks.  Canonical Euler screening may
use that split even if the triangle minima interact.  Complete STANDARD rays
require the coarser minimum-interaction clusters constructed below.

The split is algebraic: it is not a decomposition of the physical components
of a supplied normal surface.  A positive Euler value alone is not a disc
or unknot verdict.
"""

from dataclasses import dataclass

from .normal_sector import SearchLimit, _primitive, _source_hash, sector_rays
from .normal_surface_geometry import _coordinates
from .sector_euler import _q_corner_parameters
from .sector_sparse import PreparedSectorSource
from .sector_window_basis import canonical_matching_basis


@dataclass(frozen=True)
class CoordinateBlock:
    """Original coordinate indices and their native-gauge local kernel."""

    indices: tuple
    basis: tuple


def coordinate_blocks(basis, width, *, check=lambda: None):
    """Return the finest coordinate direct-sum blocks of a rational space.

    Canonicalizing the row basis is essential: a deliberately mixed basis of
    a direct sum must not disguise its independent coordinate factors.
    Coordinates identically zero on the entire space are returned separately.
    """
    if type(width) is not int or width < 0:
        raise ValueError('width must be a nonnegative integer')
    vectors = tuple(tuple(row) for row in basis)
    if any(len(row) != width for row in vectors):
        raise ValueError('basis row width mismatch')
    canonical = canonical_matching_basis(vectors, width, check)
    parent = list(range(width))

    def find(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    active = set()
    row_supports = []
    for row in canonical:
        check()
        indices = tuple(i for i, value in enumerate(row) if value)
        row_supports.append(indices)
        active.update(indices)
        for i in indices[1:]:
            parent[find(i)] = find(indices[0])
    groups = {}
    for i in sorted(active):
        groups.setdefault(find(i), []).append(i)
    result = []
    for indices in sorted(tuple(group) for group in groups.values()):
        check()
        selected = set(indices)
        local = tuple(tuple(row[i] for i in indices)
                      for row, support in zip(canonical, row_supports)
                      if support[0] in selected)
        result.append(CoordinateBlock(indices, local))
    return tuple(result), tuple(i for i in range(width) if i not in active)


def minimum_interaction_clusters(kernel, blocks, *, check=lambda: None):
    """Merge Q blocks whose variations occur at one global vertex.

    Only differences from a group anchor are inspected.  The answer is thus
    invariant under the choice of triangle-potential additive gauge.
    """
    parent = list(range(len(blocks)))

    def find(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    for group in kernel.groups:
        check()
        anchor = kernel.potentials[group[0]]
        involved = []
        for number, block in enumerate(blocks):
            if any(sum((kernel.potentials[c][i] - anchor[i]) * value
                       for i, value in zip(block.indices, row))
                   for c in group[1:] for row in block.basis):
                involved.append(number)
        for number in involved[1:]:
            parent[find(number)] = find(involved[0])
    groups = {}
    for number, block in enumerate(blocks):
        groups.setdefault(find(number), []).extend(block.indices)
    return tuple(sorted(tuple(sorted(indices)) for indices in groups.values()))


def block_sector_rays(kernel, *, phase='quadrilateral', check=lambda: None,
                      max_bases=None, stats=None):
    """Yield every non-link extreme ray, using the appropriate exact split.

    The quadrilateral phase uses the matching blocks themselves.  The
    standard phase uses their minimum-interaction clusters.  Limits count
    begun candidate bases across the whole call; interruption propagates.
    """
    if phase not in ('quadrilateral', 'standard'):
        raise ValueError('phase must be quadrilateral or standard')
    if max_bases is not None and (type(max_bases) is not int or max_bases < 0):
        raise ValueError('max_bases must be a nonnegative integer or None')
    if stats is None:
        stats = {}
    blocks, forced = coordinate_blocks(kernel.basis, len(kernel.support), check=check)
    stats.update(method='coordinate-blocks', matching_blocks=len(blocks),
                 raw_matching_nullity=len(kernel.basis),
                 block_nullities=[len(block.basis) for block in blocks],
                 forced_linear_zeros=list(forced), bases_attempted=0,
                 hyperplanes=0, emitted_rays=0)
    if phase == 'standard':
        clusters = minimum_interaction_clusters(kernel, blocks, check=check)
        stats['standard_clusters'] = len(clusters)
        stats['cluster_nullities'] = []
        source = PreparedSectorSource(kernel.triangulation, check=check)
        for indices in clusters:
            check()
            local = source.build([kernel.support[i] for i in indices], check=check)
            stats['cluster_nullities'].append(len(local.basis))
            local_stats = {}
            remaining = None if max_bases is None else max_bases - stats['bases_attempted']
            try:
                for rows in sector_rays(local, phase='standard', check=check,
                                        max_bases=remaining, stats=local_stats):
                    stats['emitted_rays'] += 1
                    yield rows
            finally:
                stats['bases_attempted'] += local_stats.get('bases_attempted', 0)
                stats['hyperplanes'] += local_stats.get('hyperplanes', 0)
        return
    for block in blocks:
        for parameters in _q_corner_parameters(block.basis, check, stats,
                                                max_bases=max_bases, prefix=''):
            local_q = _primitive(sum(z * row[i]
                                     for z, row in zip(parameters, block.basis))
                                 for i in range(len(block.indices)))
            q = [0] * len(kernel.support)
            for i, value in zip(block.indices, local_q):
                q[i] = value
            rows = kernel.lift(tuple(q), check)
            stats['emitted_rays'] += 1
            yield rows


def enumerate_sector_blocks(triangulation, allowed_types, *, phase='quadrilateral',
                            max_bases=None, check=lambda: None):
    """Complete opt-in source-bound enumeration; no recognition conclusion."""
    source = PreparedSectorSource(triangulation, check=check)
    kernel = source.build(allowed_types, check=check)
    stats = {}
    rays = list(block_sector_rays(kernel, phase=phase, max_bases=max_bases,
                                  check=check, stats=stats))
    return rays, stats


def certify_sector_block_rays(triangulation, allowed_types, *, phase='quadrilateral',
                              max_bases=None, check=lambda: None):
    """Return a complete ray list with independently replayable block coverage.

    This proof certifies the ray set, without running component-disc queries.
    Consequently it asserts neither absence nor existence of an essential disc.
    """
    source = PreparedSectorSource(triangulation, check=check)
    kernel = source.build(allowed_types, check=check)
    blocks, _ = coordinate_blocks(kernel.basis, len(kernel.support), check=check)
    indices = (tuple(block.indices for block in blocks) if phase == 'quadrilateral'
               else minimum_interaction_clusters(kernel, blocks, check=check))
    owner = {i: number for number, group in enumerate(indices) for i in group}
    entries = [dict(indices=list(group), quadrilaterals=[]) for group in indices]
    rays, stats = [], {}
    try:
        for rows in block_sector_rays(kernel, phase=phase, check=check,
                                      max_bases=max_bases, stats=stats):
            q = [rows[t][4 + typ] for t, typ in kernel.support]
            number = owner[next(i for i, value in enumerate(q) if value)]
            entries[number]['quadrilaterals'].append([q[i] for i in indices[number]])
            rays.append(rows)
    except SearchLimit as exc:
        return dict(status='INCONCLUSIVE', reason=str(exc), stats=stats)
    certificate = dict(schema='normal-sector-block-rays-v1',
        source_sha256=_source_hash(triangulation), phase=phase,
        allowed_types=[list(item) for item in kernel.support], blocks=entries)
    return dict(status='COMPLETE', rays=rays, certificate=certificate, stats=stats,
                trust='complete supplied-sector ray set; no disc or knot verdict')


def screen_sector_blocks(triangulation, allowed_types, *, max_bases=None,
                          check=lambda: None):
    """Decide canonical positive Euler existence in one compatible sector.

    A negative result includes independent block-coverage and local Q-ray
    exhaustion evidence.  A positive result contains a source-checked normal
    vector, without any assertion about its physical component topology.
    """
    source = PreparedSectorSource(triangulation, check=check)
    kernel = source.build(allowed_types, check=check)
    blocks, _ = coordinate_blocks(kernel.basis, len(kernel.support), check=check)
    owner = {i: number for number, block in enumerate(blocks) for i in block.indices}
    transcripts = [[] for _ in blocks]
    stats = {}
    try:
        for rows in block_sector_rays(kernel, check=check, max_bases=max_bases, stats=stats):
            analysed = _coordinates(source.prepared, rows, check)
            chi = analysed['euler_characteristic']
            if chi > 0:
                certificate = dict(schema='normal-sector-block-positive-euler-v1',
                    source_sha256=_source_hash(triangulation),
                    allowed_types=[list(item) for item in kernel.support], coordinates=rows)
                return dict(status='POSITIVE_EULER', coordinates=rows, certificate=certificate,
                            stats=stats, trust='canonical Euler only; no disc or knot verdict')
            q = [rows[t][4 + typ] for t, typ in kernel.support]
            number = owner[next(i for i, value in enumerate(q) if value)]
            transcripts[number].append(dict(
                quadrilaterals=[q[i] for i in blocks[number].indices],
                euler_characteristic=chi))
    except SearchLimit as exc:
        return dict(status='INCONCLUSIVE', reason=str(exc), stats=stats)
    entries = []
    for block, transcript in zip(blocks, transcripts):
        entries.append(dict(indices=list(block.indices), certificate=dict(
            schema='normal-sector-exhaustion-v1', source_sha256=_source_hash(triangulation),
            allowed_types=[list(kernel.support[i]) for i in block.indices],
            phase='quadrilateral', status='NO_POSITIVE_EULER', rays=transcript)))
    certificate = dict(schema='normal-sector-block-euler-v1',
        source_sha256=_source_hash(triangulation),
        allowed_types=[list(item) for item in kernel.support], blocks=entries)
    return dict(status='NO_POSITIVE_EULER', certificate=certificate, stats=stats,
                trust='this compatible sector only; no knot verdict')
