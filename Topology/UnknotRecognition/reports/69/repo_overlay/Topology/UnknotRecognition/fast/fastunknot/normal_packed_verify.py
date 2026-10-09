"""Independent replay of support-projected, packed normal component proofs.

The producer's packing builder, coordinate decoder, and histogram classifier
are not called. Matching-space rank is checked independently, and the existing
prefix-sum weighted-orbit checker verifies transport. The finite triangulation
and normal-corner geometry are shared trusted representations.
"""

from .integer_codec import encoded_integer, certificate_equal
from .normal_surface_geometry import (
    _prepare, _coordinates, _fingerprint, _arc_system, NormalOrbitError,
)
from .normal_component_geometry import (
    disk_corner_intervals, valid_boundary_basis, full_vector_signature,
)
from .normal_support_verify import verify_support
from .weighted_orbit_verify import verify_weighted_orbit_certificate


def verify_normal_packed_certificate(triangulation, coordinates, certificate, *,
                                     check=lambda: None):
    """Check all source-dependent claims; malformed evidence returns False.

    Cancellation exceptions raised by ``check`` propagate. This routine is a
    mathematical proof checker, not a resource sandbox for arbitrary payloads.
    """
    callback, callback_error = check, [None]

    def check():
        try:
            callback()
        except BaseException as exc:
            callback_error[0] = exc
            raise

    check()
    fields = {'schema', 'input_sha256', 'encoding', 'support_kernel',
              'boundary_homology_basis', 'weighted_orbits', 'summary'}
    if (type(certificate) is not dict or set(certificate) != fields
            or certificate['schema'] != 'normal-packed-components-v1'
            or certificate['encoding'] not in ('packed', 'vector')):
        return False
    try:
        prepared = _prepare(triangulation, check)
        analysed = _coordinates(prepared, coordinates, check)
    except NormalOrbitError:
        if callback_error[0] is not None:
            raise
        return False
    if certificate['input_sha256'] != _fingerprint(triangulation, analysed, check):
        return False
    kernel = certificate['support_kernel']
    if not verify_support(prepared, analysed, kernel, check=check):
        return False
    basis = certificate['boundary_homology_basis']
    if not valid_boundary_basis(prepared, basis, check):
        return False
    # Read only after the rank checker has validated sizes and integer syntax.
    support = [encoded_integer(value) for value in kernel['support']]
    selected = [encoded_integer(value) for value in kernel['selected']]
    denominator = encoded_integer(kernel['denominator'])
    numerators = [[encoded_integer(value) for value in row]
                  for row in kernel['numerators']]
    source = [value for row in analysed['rows'] for value in row]
    positions = {value: i for i, value in enumerate(selected)}
    radices = [2 ** source[i].bit_length() for i in selected]
    factors, capacity = [], 1
    for radix in radices:
        factors.append(capacity)
        capacity *= radix
    encoding = certificate['encoding']
    dimension = 1 if encoding == 'packed' else max(1, len(selected))
    offsets, total = {}, 0
    for edge, count in sorted(analysed['weights'].items()):
        check()
        offsets[edge] = total
        total += count
    size, pairings = _arc_system(prepared, analysed, check=check)
    if size != total:
        return False
    weights = []
    for index, start, stop in disk_corner_intervals(prepared, analysed, offsets, check):
        check()
        if index in positions:
            j = positions[index]
            row = [factors[j]] if encoding == 'packed' else [int(k == j) for k in range(dimension)]
            weights.append((start, stop, row))
    proof = certificate['weighted_orbits']
    if not verify_weighted_orbit_certificate(size, pairings, weights, proof,
                                             dimension=dimension, check=check):
        if callback_error[0] is not None:
            raise callback_error[0]
        return False
    grouped, total_components, disc_count = {}, 0, 0
    recovered = [0] * len(source)
    for item in proof['histogram']:
        check()
        weight = [encoded_integer(value) for value in item['weight']]
        count = encoded_integer(item['orbits'])
        if encoding == 'packed':
            quotient = weight[0]
            if quotient < 0 or quotient >= capacity:
                return False
            projected = []
            for radix in radices:
                quotient, digit = divmod(quotient, radix)
                projected.append(digit)
            if quotient:
                return False
        else:
            projected = weight[:len(selected)]
        if any(not 0 <= value <= source[index]
               for index, value in zip(selected, projected)):
            return False
        vector = [0] * len(source)
        for index, row in zip(support, numerators):
            check()
            value, remainder = divmod(sum(a*b for a, b in zip(row, projected)), denominator)
            if remainder or not 0 <= value <= source[index]:
                return False
            vector[index] = value
        if not any(vector):
            return False
        try:
            signature, rows = full_vector_signature(prepared, vector, basis, check)
        except (ValueError, NormalOrbitError):
            if callback_error[0] is not None:
                raise
            return False
        chi, first, second, disks, boundary = signature
        parity = first % 2, second % 2
        good = chi == 1 and parity != (0, 0)
        key = (chi, *parity, disks, boundary, *vector)
        if key not in grouped:
            grouped[key] = dict(euler_characteristic=chi,
                boundary_homology_mod2=list(parity), compressing_disk=good,
                multiplicity=0, normal_disks=disks, boundary_points=boundary,
                coordinates=rows)
        grouped[key]['multiplicity'] += count
        total_components += count
        if good:
            disc_count += count
        for i, value in enumerate(vector):
            recovered[i] += count * value
    if recovered != source:
        return False
    expected = dict(components=total_components, compressing_disk_components=disc_count,
        contains_compressing_disk=bool(disc_count),
        component_histogram=[grouped[key] for key in sorted(grouped)])
    return certificate_equal(certificate['summary'], expected)
