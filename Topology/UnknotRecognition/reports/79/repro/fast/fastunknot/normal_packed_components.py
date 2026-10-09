"""Support-compiled normal component coordinates with exact scalar packing.

The supplied positive support determines a rational matching space. A checked
coordinate projection identifies every component in that space. Nonnegative
projected counts are bounded by the source and can be packed into one integer
without carries between slots. The maintained AHT engine transports this one
integer; the full component vectors are reconstructed only at the output.

This evaluates one supplied surface. It neither searches for a normal surface
nor asserts that its ambient triangulation is the exterior of a knot diagram.
"""

from .normal_surface_geometry import _prepare, _coordinates, _fingerprint, _arc_system
from .normal_component_geometry import (
    boundary_homology_basis, disk_corner_intervals, _edge_offsets,
)
from .normal_surface_components import _component_summary
from .normal_support import compile_support, decode_support
from .normal_support_verify import verify_support
from .weighted_orbits import (
    weighted_orbit_histogram, weighted_histogram_from_orbit_certificate,
)


def _projected_system(prepared, analysed, selected, encoding, check):
    """Construct weights directly, without allocating the old 7t-vector rows."""
    size, pairings = _arc_system(prepared, analysed, check=check)
    offsets, total = _edge_offsets(analysed, check)
    if total != size:
        raise ArithmeticError('inconsistent normal edge universe')
    source = [value for row in analysed['rows'] for value in row]
    widths = [source[index].bit_length() for index in selected]
    shifts, total_bits = [], 0
    for width in widths:
        shifts.append(total_bits)
        total_bits += width
    positions = {index: j for j, index in enumerate(selected)}
    dimension = 1 if encoding == 'packed' else max(1, len(selected))
    weights = []
    for index, lo, hi in disk_corner_intervals(prepared, analysed, offsets, check):
        check()
        if index not in positions:
            continue
        j = positions[index]
        if encoding == 'packed':
            weight = [1 << shifts[j]]
        else:
            weight = [0] * dimension
            weight[j] = 1
        weights.append((lo, hi, weight))
    return dict(size=size, pairings=pairings, weights=weights,
                dimension=dimension, widths=widths, shifts=shifts,
                packed_bits=total_bits)


def normal_packed_component_census(triangulation, coordinates, *,
                                  encoding='packed', support_certificate=None,
                                  max_cycles=None, periodic_rule='fine_wilf',
                                  check=lambda: None, record_certificate=False,
                                  orbit_certificate=None):
    """Return the complete coordinate histogram of the supplied normal surface.

    ``encoding='vector'`` is an exact comparison implementation using the same
    compiled projection without scalar packing. A provided support certificate
    is independently checked and may be reused with different positive values
    on precisely the same support. Its minimum-bit property is guaranteed only
    when freshly compiled for the current values; reuse preserves correctness.

    A supplied orbit trace is independently verified before weighted replay.
    All integer coordinates remain binary; neither points nor sheets expand.
    """
    if encoding not in ('packed', 'vector'):
        raise ValueError('encoding must be packed or vector')
    if type(record_certificate) is not bool:
        raise ValueError('record_certificate must be bool')
    if max_cycles is not None and (type(max_cycles) is not int or max_cycles < 0):
        raise ValueError('max_cycles must be a nonnegative integer or None')
    if periodic_rule not in ('fine_wilf', 'aht'):
        raise ValueError('unknown periodic rule')
    if orbit_certificate is not None and max_cycles is not None:
        raise ValueError('max_cycles cannot constrain replay of a supplied trace')
    check()
    prepared = _prepare(triangulation, check)
    analysed = _coordinates(prepared, coordinates, check)
    fresh = support_certificate is None
    if fresh:
        support = compile_support(prepared, analysed, check=check)
    else:
        if not verify_support(prepared, analysed, support_certificate, check=check):
            raise ValueError('invalid or inapplicable support certificate')
        support = support_certificate
    # Certificates accept hexadecimal integer encodings; normalize the selected
    # indices here even when an externally supplied proof uses that encoding.
    from .integer_codec import encoded_integer
    selected = [encoded_integer(index) for index in support['selected']]
    system = _projected_system(prepared, analysed, selected, encoding, check)
    kwargs = dict(dimension=system['dimension'], check=check,
                  record_certificate=record_certificate)
    if orbit_certificate is None:
        result = weighted_orbit_histogram(
            system['size'], system['pairings'], system['weights'],
            max_cycles=max_cycles, periodic_rule=periodic_rule, **kwargs)
    else:
        result = weighted_histogram_from_orbit_certificate(
            system['size'], system['pairings'], system['weights'],
            orbit_certificate, **kwargs)
    if result['status'] != 'COMPLETE':
        return dict(status='INCONCLUSIVE', reason='orbit-cycle allowance exhausted',
                    encoding=encoding, stats=result['stats'])
    histogram = []
    source = [value for row in analysed['rows'] for value in row]
    recovered = [0] * len(source)
    for item in result['histogram']:
        check()
        if encoding == 'packed':
            code = item['weight'][0]
            if not 0 <= code < (1 << system['packed_bits']):
                raise ArithmeticError('packed orbit weight exceeds the source box')
            projected = [(code >> shift) & ((1 << width)-1)
                         for shift, width in zip(system['shifts'], system['widths'])]
        else:
            projected = item['weight'][:len(selected)]
        vector = decode_support(analysed, support, projected, check=check)
        if not any(vector):
            raise ArithmeticError('a nonempty normal component has zero coordinates')
        count = item['orbits']
        histogram.append(dict(weight=vector, orbits=count))
        for i, value in enumerate(vector):
            recovered[i] += count * value
    if recovered != source:
        raise ArithmeticError('component coordinates do not reconstruct the source')
    basis = boundary_homology_basis(prepared, check)
    summary = _component_summary(prepared, histogram, 'coordinates', basis, check)
    if summary['components'] != result['orbit_count']:
        raise ArithmeticError('component multiplicities differ from orbit count')
    answer = dict(status='COMPLETE', mode='coordinates', encoding=encoding,
        tetrahedra=len(analysed['rows']), normal_points=system['size'],
        normal_disks=analysed['normal_disks'],
        euler_characteristic=analysed['euler_characteristic'],
        boundary_normal_arcs=analysed['boundary_arcs'],
        maximum_coordinate_bits=analysed['maximum_coordinate_bits'],
        support_size=len(support['support']), projection_dimension=len(selected),
        selected_coordinates=selected, source_slot_bits=system['widths'],
        packed_bits=system['packed_bits'], weight_dimension=system['dimension'],
        freshly_optimized_projection=fresh, boundary_homology_basis=basis,
        stats=result['stats'], **summary,
        trust='components of the supplied normal surface in the validated '
              'torus-boundary manifold; no knot-diagram correspondence asserted')
    if record_certificate:
        answer['certificate'] = dict(schema='normal-packed-components-v1',
            input_sha256=_fingerprint(triangulation, analysed, check),
            encoding=encoding, support_kernel=support,
            boundary_homology_basis=basis, weighted_orbits=result['certificate'],
            summary=summary)
    check()
    return answer
