"""Opt-in bridge to the pinned ProveIt fastunknot component APIs.

STATUS: source-reviewed integration draft; NOT executed against native fastunknot
in the delivery environment. The standalone transfer kernel is tested separately.
The negative precheck and the final positive witness use native independent replay.
No recognizer dispatch is modified and no knot verdict is returned.

Put this directory and ../src on PYTHONPATH alongside ProveIt's fast/ directory.
"""
from __future__ import annotations
from copy import deepcopy


def _native():
    from fastunknot.normal_surface_geometry import _prepare, _coordinates, _fingerprint
    from fastunknot.normal_component_geometry import (
        component_weight_system, _edge_offsets, disk_corner_intervals,
    )
    from fastunknot.normal_surface_components import normal_component_census
    from fastunknot.normal_component_verify import verify_normal_component_certificate
    return (_prepare, _coordinates, _fingerprint, component_weight_system,
            _edge_offsets, disk_corner_intervals, normal_component_census,
            verify_normal_component_certificate)


def selective_normal_disk(triangulation, coordinates, *, max_cycles=None,
                          max_nodes=None, check=None):
    """Find one independently certified disc in a supplied normal surface.

    COMPLETE is an actual disc in the validated manifold, not an unknot claim.
    NO_DISC_IN_SUPPLIED_VECTOR is not a search-completeness or knottedness claim.
    One cycle allowance covers the native precheck and final witness census.
    Circuit nodes have their own allowance; cancellation is cooperative throughout.
    """
    from orbit_transfer import compile_transfer, ResourceExhausted
    for value,name in ((max_cycles,'max_cycles'),(max_nodes,'max_nodes')):
        if value is not None and (type(value) is not int or value < 0):
            raise ValueError(name+' must be a nonnegative integer or None')
    poll=check if check is not None else lambda: None
    poll()
    prepare,analyse,fingerprint,system_of,offsets_of,corners_of,census,verify=_native()
    # Preserve the inexpensive three-weight negative path. Include independent replay.
    initial=census(triangulation,coordinates,mode='disk',max_cycles=max_cycles,
                   check=poll,record_certificate=True)
    if initial['status'] != 'COMPLETE':
        return dict(status='INCONCLUSIVE',reason='initial orbit allowance exhausted')
    initial_cert=initial['certificate']
    if not verify(triangulation,coordinates,initial_cert,check=poll):
        raise ArithmeticError('native precheck failed independent replay')
    from fastunknot.integer_codec import encoded_integer
    initial_summary=initial_cert['summary']
    if encoded_integer(initial_summary['compressing_disk_components'])==0:
        return dict(status='NO_DISC_IN_SUPPLIED_VECTOR',certificate=initial_cert,
                    trust='negative only for this supplied normal vector')
    prepared=prepare(triangulation,poll); analysed=analyse(prepared,coordinates,poll)
    system=system_of(prepared,analysed,mode='disk',check=poll)
    offsets,_=offsets_of(analysed,poll)
    owners=corners_of(prepared,analysed,offsets,poll)
    cuts={0,system['size']}
    for _,lo,hi in owners: poll(); cuts.update((lo,hi))
    for lo,hi,_ in system['weights']: poll(); cuts.update((lo,hi))
    proof=initial_cert['weighted_orbits']['orbit_proof']
    try:
        program=compile_transfer(system['size'],system['pairings'],proof,cuts,
                                 max_nodes=max_nodes,check=poll)
    except ResourceExhausted:
        return dict(status='INCONCLUSIVE',reason='circuit-node allowance exhausted')
    values=[program.evaluate_intervals([(lo,hi,v[j]) for lo,hi,v in system['weights']])
            for j in range(3)]
    selected=next((i for i in range(len(program.emissions))
                   if values[0][i]==1 and (values[1][i]%2 or values[2][i]%2)),None)
    if selected is None:
        raise ArithmeticError('compiled selection disagrees with native precheck')
    flat=program.extract(selected,owners,7*len(analysed['rows']))
    witness=[flat[j:j+7] for j in range(0,len(flat),7)]
    # This is a NEW query on y, not an assumption that a compiler is trustworthy.
    used=initial['stats']['orbit_cycles']
    remaining=None if max_cycles is None else max_cycles-used
    terminal=census(triangulation,witness,mode='disk',max_cycles=remaining,
                    check=poll,record_certificate=True)
    if terminal['status'] != 'COMPLETE':
        return dict(status='INCONCLUSIVE',reason='witness orbit allowance exhausted')
    cert=dict(schema='selective-normal-disc-v1',
              input_sha256=fingerprint(triangulation,analysed,poll),
              coordinates=witness,disc_census=deepcopy(terminal['certificate']))
    if not verify_selective_normal_disk(triangulation,coordinates,cert,check=poll):
        raise ArithmeticError('selected witness failed independent terminal replay')
    return dict(status='COMPLETE',coordinates=witness,certificate=cert,
                stats=dict(transfer=program.stats,initial_cycles=used,
                           witness_cycles=terminal['stats']['orbit_cycles']),
                trust='one compressing disc in the supplied validated manifold; '
                      'no knot-exterior provenance or search bound asserted')


def verify_selective_normal_disk(triangulation, original_coordinates, certificate, *,
                                 check=None):
    """Check a positive disc certificate WITHOUT importing/calling the compiler.

    This establishes admissible y <= x and a connected essential disc y.
    It does NOT independently establish that y is a connected component of x.
    The stronger component statement is the transfer theorem, not this interface.
    """
    poll=check if check is not None else lambda: None
    poll()
    from fastunknot.normal_surface_geometry import (
        _prepare, _coordinates, _fingerprint, NormalOrbitError,
    )
    from fastunknot.normal_component_verify import verify_normal_component_certificate
    from fastunknot.integer_codec import encoded_integer
    if type(certificate) is not dict or certificate.get('schema')!='selective-normal-disc-v1':
        return False
    try:
        prepared=_prepare(triangulation,poll)
        original=_coordinates(prepared,original_coordinates,poll)
        if certificate.get('input_sha256') != _fingerprint(triangulation,original,poll):
            return False
        witness=certificate.get('coordinates')
        current=_coordinates(prepared,witness,poll)
        if any(y>x for a,b in zip(original['rows'],current['rows']) for x,y in zip(a,b)):
            return False
    except NormalOrbitError:
        return False
    proof=certificate.get('disc_census')
    if not verify_normal_component_certificate(triangulation,witness,proof,check=poll):
        return False
    summary=proof['summary']  # This object, not a separate result wrapper, is checked above.
    return (encoded_integer(summary['components'])==1
            and encoded_integer(summary['compressing_disk_components'])==1)
