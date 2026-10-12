"""Source-certified whole-cut censuses through relative bundle incidence.

This opt-in research operator consumes the pinned fastunknot source geometry.
It never returns an unknot or a non-handlebody verdict.  COMPLETE is a proved
handlebody genus census.  A certified raw obstruction is INCONCLUSIVE for
topology and only rules out full cancellation in the stated positive model.
"""

from fastunknot.normal_parallelity import normal_cut_parallelity
from fastunknot.parallelity_boundary_words import normal_parallelity_boundary_words

from column_peeling import column_peeling_plan
from relative_bundles import (compile_relative_bundles,
                              census_after_complete_cancellation)


def _original_core_model(core, check):
    """Compile the fixed original-core forest and unsigned source incidences.

    The source parallelity operator authenticates these charts.  This local
    finite compiler has no bundle-boundary dependency and creates no new
    geometric incidences.  Forest order agrees with the relative compiler.
    """
    vertices, edges, discs = [core['handles' + str(i)] for i in range(3)]
    if any(type(h['id']) is not int or h['id'] != i
           for handles in (vertices, edges, discs) for i, h in enumerate(handles)):
        raise ValueError('noncanonical original-core handles')
    parent = list(range(len(vertices)))

    def root(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    forest = []
    for handle in edges:
        check()
        a, b = handle['ends']
        if any(type(v) is not int or not 0 <= v < len(vertices) for v in (a, b)):
            raise ValueError('invalid original-core one-handle ends')
        x, y = root(a), root(b)
        if x != y:
            parent[max(x, y)] = min(x, y)
            forest.append(handle['id'])
    tree = set(forest)
    counts = {}
    for disc in discs:
        check()
        row = {}
        for flag in disc['cycle']:
            if flag['dimension'] == 1 and flag['handle'] not in tree:
                column = flag['handle']
                row[column] = min(2, row.get(column, 0) + 1)
        counts[disc['id']] = row
    proof = dict(forest=forest,
                 rows=[dict(id=r, counts=[[c, v] for c, v in sorted(row.items())])
                       for r, row in sorted(counts.items())])
    return counts, proof


def normal_cut_saturation(triangulation, coordinates, *, max_cycles=None,
                          record_certificate=False, precheck_core=False,
                          check=lambda: None):
    """Classify a supplied normal cut, including saturated bordered bundles.

    Up to six upstream orbit discoveries share one optional cycle allowance.
    Genus and normal-coordinate magnitudes remain binary encoded.  Resource
    exhaustion, closed bundle bases, core three-handles, and positive-model
    obstructions have no negative topological meaning.

    ``precheck_core=True`` first checks the original core rows after the four
    source parallelity queries.  An original-core stopping set remains a
    stopping set after appending relative bundle rows.  It therefore permits
    a certified INCONCLUSIVE return before the two ordered-boundary queries.
    The default False preserves the original operator and certificate schema.
    """
    check()
    if type(record_certificate) is not bool:
        raise ValueError('record_certificate must be bool')
    if type(precheck_core) is not bool:
        raise ValueError('precheck_core must be bool')
    if max_cycles is not None and (type(max_cycles) is not int or max_cycles < 0):
        raise ValueError('max_cycles must be a nonnegative integer or None')
    result = dict(status='INCONCLUSIVE', stats={},
                  trust='whole supplied cut; no standalone knot verdict')
    parallelity = normal_cut_parallelity(
        triangulation, coordinates, max_cycles=max_cycles,
        record_certificate=record_certificate, check=check)
    result['stats']['parallelity'] = parallelity.get('stats', {})
    if parallelity['status'] != 'COMPLETE':
        return dict(result, reason='parallelity_budget_exhausted')
    if parallelity['geometry']['core']['handles3']:
        return dict(result, reason='core_has_three_handles')
    if any(p['boundary_components'] == 0
           for p in parallelity['summary']['base_profiles']):
        return dict(result, reason='closed_bundle_base')
    if precheck_core:
        core_counts, core_proof = _original_core_model(parallelity['geometry']['core'], check)
        core_peeling = column_peeling_plan(core_counts, check=check)
        result['stats']['core_precheck'] = core_peeling['stats']
        if core_peeling['status'] == 'OBSTRUCTED':
            conclusion = dict(status='INCONCLUSIVE', reason='original_core_raw_obstruction',
                              remaining_two_handles=core_peeling['remaining_rows'])
            result.update(conclusion)
            result['stats']['avoided_boundary_queries'] = (
                2 if parallelity['geometry']['ports'] else 0)
            if record_certificate:
                result['certificate'] = dict(
                    schema='normal-cut-core-obstruction-v1',
                    parallelity=parallelity['certificate'], core=core_proof,
                    peeling=core_peeling['certificate'], conclusion=conclusion)
            check()
            return result
    remaining = max_cycles
    if remaining is not None:
        remaining -= sum(s['orbit_cycles'] for s in parallelity['stats'].values())
    boundary = normal_parallelity_boundary_words(
        triangulation, coordinates, max_cycles=remaining,
        record_certificate=record_certificate, check=check)
    result['stats']['boundary'] = boundary.get('stats', {})
    if boundary['status'] != 'COMPLETE':
        return dict(result, reason='boundary_budget_exhausted')
    model = compile_relative_bundles(
        parallelity['geometry'], parallelity['summary'], boundary['skeleton'],
        check=check)
    if model['status'] != 'READY':
        return dict(result, reason=model['reason'])
    result['stats']['relative'] = model['stats']
    peeling = column_peeling_plan(model['counts'], check=check)
    result['stats']['peeling'] = peeling['stats']
    if peeling['status'] == 'COMPLETE':
        census = census_after_complete_cancellation(model, check=check)
        conclusion = dict(status='COMPLETE', census=census)
    else:
        conclusion = dict(status='INCONCLUSIVE',
                          reason='full_raw_cancellation_obstructed',
                          remaining_two_handles=peeling['remaining_rows'])
    result.update(conclusion)
    if record_certificate:
        result['certificate'] = dict(
            schema='normal-cut-saturated-bundles-v1',
            parallelity=parallelity['certificate'], boundary=boundary['certificate'],
            relative=model['certificate'], peeling=peeling['certificate'],
            conclusion=conclusion)
    check()
    return result
