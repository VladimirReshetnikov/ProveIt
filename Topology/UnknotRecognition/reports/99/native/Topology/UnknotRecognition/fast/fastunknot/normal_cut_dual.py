"""Native normal-cut completion after exact source 2/3 cancellations."""

from .bundle_boundary_kernel import bundle_boundary_kernel
from .parallelity_boundary_words import normal_parallelity_boundary_words
from .source_core_dual import source_core_dual_reduction


def finish_dual_cut(parallelity, triangulation, coordinates, *, max_cycles=None,
                    record_certificate=False, check=lambda: None):
    """Finish from an already discovered source parallelity packet.

    The normal-cut entry point passes its existing packet here, so no weighted
    orbit discovery is repeated.  This is a conservative terminal method on
    a supplied cut and supplies no standalone knottedness decision.
    """
    check()
    result = dict(status='INCONCLUSIVE', stats=dict(parallelity=parallelity['stats']),
                  trust='source cut handlebodies; no standalone knot verdict')
    reduction = source_core_dual_reduction(parallelity['geometry'], check=check)
    if reduction is None:
        result['reason'] = 'dual_core_component_without_boundary'
        return result
    geometry, dual_proof, statistics = reduction
    result['stats']['dual_core'] = statistics
    remaining = max_cycles
    if remaining is not None:
        remaining -= sum(s['orbit_cycles'] for s in parallelity['stats'].values())
    boundary = normal_parallelity_boundary_words(triangulation, coordinates,
        max_cycles=remaining, record_certificate=record_certificate, check=check)
    result['stats']['boundary'] = boundary['stats']
    if boundary['status'] != 'COMPLETE':
        result['reason'] = 'boundary_budget_exhausted'
        return result
    kernel = bundle_boundary_kernel(geometry, parallelity['summary'],
                                    boundary['skeleton'], check=check)
    if kernel is None:
        result['reason'] = 'dual_reduced_boundary_kernel_stalled'
        return result
    kernel_proof, census, kernel_stats = kernel
    result['stats']['boundary_kernel'] = kernel_stats
    result.update(status='COMPLETE', census=census)
    if record_certificate:
        result['certificate'] = dict(schema='normal-cut-handlebodies-v6',
            parallelity=parallelity['certificate'], boundary=boundary['certificate'],
            dual=dual_proof, kernel=kernel_proof, census=census)
    check()
    return result
