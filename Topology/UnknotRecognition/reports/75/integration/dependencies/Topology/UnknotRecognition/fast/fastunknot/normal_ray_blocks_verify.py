"""Independent replay of geometric support blocks and ray disc counts.

The block partition uses breadth-first traversal of original face records,
not the producer's union-find routine.  Rank and decoder identities use the
separate support verifier.  Fallback proofs retain their existing independent
component replay.  No producer or orbit-discovery function is called here.
"""

from math import gcd

from .integer_codec import encoded_integer, certificate_equal
from .normal_component_geometry import valid_boundary_basis
from .normal_disk_kernel import verify_normal_disk_count_certificate
from .normal_surface_geometry import _prepare, _coordinates, _fingerprint, _quad, NormalOrbitError
from .normal_support_verify import verify_support
from .normal_support_peeling_verify import verify_support_ray


def _reconstruct_blocks(prepared, analysed, check):
    source = [value for row in analysed['rows'] for value in row]
    adjacency = {index: set() for index, value in enumerate(source) if value}
    for t, f, u, g, permutation in prepared['pairs']:
        check()
        for corner in range(4):
            if corner == f:
                continue
            image = permutation[corner]
            original = [7*t+corner, 7*t+4+_quad(f, corner),
                        7*u+image, 7*u+4+_quad(g, image)]
            live = [index for index in original if index in adjacency]
            for left, right in zip(live, live[1:]):
                check()
                adjacency[left].add(right)
                adjacency[right].add(left)
    seen, groups = set(), []
    for root in sorted(adjacency):
        check()
        if root in seen:
            continue
        seen.add(root)
        queue, cursor = [root], 0
        while cursor < len(queue):
            check()
            current = queue[cursor]
            cursor += 1
            for other in adjacency[current]:
                if other not in seen:
                    seen.add(other)
                    queue.append(other)
        groups.append(sorted(queue))
    return groups


def _rebuild_unit_primitive(prepared, source, proof, check):
    """Independently evaluate a checked unit transcript at seed value one."""
    present = {i for i, value in enumerate(source) if value}
    seed = encoded_integer(proof['seed'])
    values = {seed: 1}
    for step in proof['steps']:
        check()
        row, target = (encoded_integer(value) for value in step)
        equation = prepared['matching'][row]
        pivot = equation.get(target, 0)
        if pivot not in (-1, 1) or target in values:
            return None
        remainder = 0
        for index, coefficient in equation.items():
            if index == target or index not in present:
                continue
            if index not in values:
                return None
            remainder -= coefficient*values[index]
        value = remainder if pivot == 1 else -remainder
        if not 0 < value <= source[target]:
            return None
        values[target] = value
    if set(values) != present:
        return None
    # The independently checked rank witness and both matching vectors prove
    # source = source[seed] * values. The seed entry one proves primitivity.
    return [[values.get(7*t+j, 0) for j in range(7)]
            for t in range(len(prepared['tetrahedra']))]


def verify_normal_ray_block_disk_certificate(triangulation, coordinates, certificate,
                                              *, check=lambda: None):
    """Verify exact disc counts for the supplied vector, without discovery."""
    callback, callback_error = check, [None]

    def check():
        try:
            callback()
        except BaseException as exc:
            callback_error[0] = exc
            raise

    check()
    fields = {'schema', 'input_sha256', 'boundary_homology_basis', 'blocks',
              'compressing_disk_components'}
    if (type(certificate) is not dict or set(certificate) != fields
            or certificate['schema'] != 'normal-ray-block-disks-v1'):
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
    basis = certificate['boundary_homology_basis']
    if not valid_boundary_basis(prepared, basis, check):
        return False
    expected_blocks = _reconstruct_blocks(prepared, analysed, check)
    records = certificate['blocks']
    if type(records) is not list or len(records) != len(expected_blocks):
        return False
    source = [value for row in analysed['rows'] for value in row]
    total = 0
    for record, support in zip(records, expected_blocks):
        check()
        if (type(record) is not dict
                or not certificate_equal(record.get('support'), support)):
            return False
        flat = [0] * len(source)
        for index in support:
            check()
            flat[index] = source[index]
        rows = [flat[7*t:7*t+7] for t in range(len(analysed['rows']))]
        try:
            block = _coordinates(prepared, rows, check)
        except NormalOrbitError:
            if callback_error[0] is not None:
                raise
            return False
        if record.get('method') == 'ray':
            if set(record) != {'support', 'method', 'support_certificate',
                    'coordinate_divisor', 'primitive_euler_characteristic',
                    'primitive_boundary_homology_mod2', 'compressing_disk_components'}:
                return False
            proof = record['support_certificate']
            peeling = (type(proof) is dict
                       and proof.get('schema') == 'normal-support-ray-peeling-v1')
            valid = (verify_support_ray(prepared, block, proof, check) if peeling
                     else verify_support(prepared, block, proof, check))
            if not valid:
                return False
            if not certificate_equal(proof['nullity'], 1):
                return False
            if peeling:
                divisor = source[encoded_integer(proof['seed'])]
            else:
                divisor = 0
                for value in flat:
                    check()
                    divisor = gcd(divisor, value)
            if divisor < 1 or not certificate_equal(record['coordinate_divisor'], divisor):
                return False
            # Reconstruct primitive coordinates and recount the normal cells.
            # A checked unit transcript uses integer addition, not division
            # by the potentially enormous common source multiplier.
            if peeling:
                primitive_rows = _rebuild_unit_primitive(prepared, flat, proof, check)
                if primitive_rows is None:
                    return False
            else:
                primitive_rows = []
                for row in rows:
                    check()
                    divided = []
                    for value in row:
                        quotient, remainder = divmod(value, divisor)
                        if remainder:
                            return False
                        divided.append(quotient)
                    primitive_rows.append(divided)
            try:
                primitive = _coordinates(prepared, primitive_rows, check)
            except NormalOrbitError:
                if callback_error[0] is not None:
                    raise
                return False
            chi = primitive['euler_characteristic']
            parity = []
            for cycle in basis:
                check()
                value = 0
                for edge in cycle:
                    check()
                    value ^= primitive['weights'][edge] & 1
                parity.append(value)
            if (not certificate_equal(record['primitive_euler_characteristic'], chi)
                    or not certificate_equal(record['primitive_boundary_homology_mod2'], parity)):
                return False
            count = divisor if chi == 1 and any(parity) else 0
        elif record.get('method') == 'component_census':
            if set(record) != {'support', 'method', 'certificate', 'compressing_disk_components'}:
                return False
            proof = record['certificate']
            if not verify_normal_disk_count_certificate(triangulation, rows, proof, check=check):
                if callback_error[0] is not None:
                    raise callback_error[0]
                return False
            count = encoded_integer(proof['compressing_disk_components'])
        else:
            return False
        if not certificate_equal(record['compressing_disk_components'], count):
            return False
        total += count
    check()
    return certificate_equal(certificate['compressing_disk_components'], total)
