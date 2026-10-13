"""Euler-checked free-group terminals for complete normal cuts with disk bases.

An accepted output is an unmarked handlebody census.  The topological theorem
uses the Loop Theorem and the three-dimensional Poincare theorem.  Group-word
substitutions are not claimed to be geometric handle slides or marked maps.
"""

from collections import Counter

from .free_group_elimination import certify_free_group
from .normal_parallelity import normal_cut_parallelity
from .parallelity_boundary_moments import _compile as _compile_moment_boundary
from .source_cut_group import compile_disk_cut_presentation


def _census(presentation, ranks):
    isolated = presentation['isolated_ball_count']
    histogram = Counter({0: isolated}) if isolated else Counter()
    joined = []
    for component, rank in zip(presentation['components'], ranks):
        histogram[rank] += 1
        joined.append(dict(id=component['id'], core_components=component['core_components'],
                           interval_bases=component['interval_bases'],
                           annular_bases=component['annular_bases'], genus=rank))
    count, total_rank = len(ranks) + isolated, sum(ranks)
    euler = presentation['source_euler_characteristic']
    defect = euler - count + total_rank
    if defect:
        return None, defect
    return dict(histogram=[dict(genus=g, multiplicity=n) for g, n in sorted(histogram.items()) if n],
                components=count, ball_components=histogram[0],
                all_balls=all(g == 0 for g, n in histogram.items() if n),
                euler_characteristic=euler, free_rank_sum=total_rank,
                joined_components=joined, isolated_ball_count=isolated), 0


def _group_terminal(geometry, summary, skeleton, check):
    presentation = compile_disk_cut_presentation(geometry, summary, skeleton, check=check)
    if presentation is None:
        return dict(status='INCONCLUSIVE', reason='non_disk_parallelity_base', stats={})
    groups, ranks, details = [], [], []
    for component in presentation['components']:
        check()
        reduced = certify_free_group(component['generators'], component['relators'], check=check)
        details.append(dict(component=component['id'], **reduced['stats']))
        if reduced['status'] != 'COMPLETE':
            return dict(status='INCONCLUSIVE', reason='group_elimination_stalled',
                        component=component['id'],
                        stats=dict(presentation=presentation['stats'], group_components=details))
        groups.append(dict(component=component['id'], proof=reduced['certificate']))
        ranks.append(reduced['free_rank'])
    census, defect = _census(presentation, ranks)
    stats = dict(presentation=presentation['stats'], group_components=details,
                 euler_defect=defect,
                 trivial_relators=sum(d['trivial_relators'] for d in details))
    if census is None:
        # For a valid source and correct free presentations, this is the
        # exact sum of second Betti numbers.  It is never a knot verdict.
        if defect < 0:
            raise ArithmeticError('free presentation contradicts source Euler characteristic')
        return dict(status='INCONCLUSIVE', reason='positive_second_betti_number',
                    second_betti_sum=defect, stats=stats)
    return dict(status='COMPLETE', presentation=presentation, groups=groups,
                census=census, stats=stats)


def normal_cut_group_handlebodies(triangulation, coordinates, *, max_cycles=None,
                                 record_certificate=False, check=lambda: None):
    """Produce a source-bound terminal census using finite group elimination.

    Unsupported bases, orbit budgets, and a stalled deterministic word policy
    return INCONCLUSIVE.  COMPLETE certifies the entire cut, including binary
    families of isolated balls.  Source validity is the maintained compact,
    connected, orientable triangulation with one torus boundary contract.
    """
    check()
    if type(record_certificate) is not bool:
        raise ValueError('record_certificate must be bool')
    if max_cycles is not None and (type(max_cycles) is not int or max_cycles < 0):
        raise ValueError('max_cycles must be a nonnegative integer or None')
    result = dict(status='INCONCLUSIVE', stats={},
                  trust='source cut unmarked handlebodies; no standalone knot verdict')
    parallelity = normal_cut_parallelity(triangulation, coordinates,
        max_cycles=max_cycles, record_certificate=record_certificate, check=check)
    result['stats']['parallelity'] = parallelity['stats']
    if parallelity['status'] != 'COMPLETE':
        result['reason'] = 'parallelity_budget_exhausted'
        return result
    for p in parallelity['summary']['base_profiles']:
        check()
        if (p['euler_characteristic'], p['boundary_components'], p['orientable'], p['product']) != (1, 1, True, True):
            result['reason'] = 'non_disk_parallelity_base'
            return result
    remaining = max_cycles
    if remaining is not None:
        remaining -= sum(s['orbit_cycles'] for s in parallelity['stats'].values())
    fingerprint = parallelity['certificate']['input_sha256'] if record_certificate else None
    boundary = _compile_moment_boundary(parallelity['geometry'], fingerprint, remaining,
                                        record_certificate, check, 'pair')
    result['stats']['boundary'] = boundary['stats']
    if boundary['status'] != 'COMPLETE':
        result['reason'] = 'boundary_budget_exhausted'
        return result
    terminal = _group_terminal(parallelity['geometry'], parallelity['summary'],
                               boundary['skeleton'], check)
    result['stats']['terminal'] = terminal['stats']
    if terminal['status'] != 'COMPLETE':
        result['reason'] = terminal['reason']
        if 'second_betti_sum' in terminal:
            result['second_betti_sum'] = terminal['second_betti_sum']
        return result
    result.update(status='COMPLETE', census=terminal['census'])
    if record_certificate:
        result['certificate'] = dict(schema='normal-cut-euler-free-v1',
            parallelity=parallelity['certificate'], boundary=boundary['certificate'],
            presentation=terminal['presentation'], groups=terminal['groups'],
            census=terminal['census'])
    check()
    return result
