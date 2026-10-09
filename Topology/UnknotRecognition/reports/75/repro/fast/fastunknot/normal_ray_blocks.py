"""Essential-disc counts from support blocks and certified normal rays.

Normal-disc types joined by an original face-arc equation form a safe
geometric block.  A primitive vector in a block with matching nullity one
is connected.  Its Euler characteristic and boundary parity therefore
decide the disc count without an interval-orbit computation.  Other blocks
retain the existing complete supplied-vector disc-count query.

This interface concerns the supplied surface in a validated torus-boundary
manifold.  It establishes neither a knot-diagram correspondence nor the
absence of another normal disc elsewhere in the manifold.
"""

from math import gcd

from .normal_component_geometry import boundary_homology_basis
from .normal_disk_kernel import normal_compressing_disk_count
from .normal_surface_geometry import _prepare, _coordinates, _fingerprint, _quad
from .normal_support import compile_support
from .normal_support_peeling import peel_support_ray


def _support_blocks(prepared, analysed, check=lambda: None):
    """Partition positive types using uncollected face-arc incidences.

    Original occurrences are retained even if coefficients cancel in the
    algebraic matching matrix.  This intentionally conservative graph only
    makes geometric separations that follow directly from face gluing.
    """
    source = [value for row in analysed['rows'] for value in row]
    parent = list(range(len(source)))
    size = [1] * len(source)

    def root(index):
        while parent[index] != index:
            parent[index] = parent[parent[index]]
            index = parent[index]
        return index

    def join(left, right):
        left, right = root(left), root(right)
        if left == right:
            return
        if size[left] < size[right]:
            left, right = right, left
        parent[right] = left
        size[left] += size[right]

    for t, f, u, g, permutation in prepared['pairs']:
        check()
        for v in range(4):
            if v == f:
                continue
            occurrences = (7*t+v, 7*t+4+_quad(f, v),
                           7*u+permutation[v], 7*u+4+_quad(g, permutation[v]))
            positive = [index for index in occurrences if source[index]]
            for index in positive[1:]:
                check()
                join(positive[0], index)
    groups = {}
    for index, value in enumerate(source):
        check()
        if value:
            groups.setdefault(root(index), []).append(index)
    return sorted(groups.values(), key=lambda group: group[0])


def _primitive_peeling_rows(prepared, analysed, proof, check=lambda: None):
    """Recover the primitive ray by unit row recurrences, without division.

    The nonzero matching source and the seed-normalized triangular witness
    imply source = source[seed] * primitive. No large scalar products are
    needed to check this equality again coordinate by coordinate.
    """
    source = [value for row in analysed['rows'] for value in row]
    primitive = [None if value else 0 for value in source]
    primitive[proof['seed']] = 1
    for row_index, pivot in proof['steps']:
        check()
        equation = prepared['matching'][row_index]
        coefficient = equation.get(pivot, 0)
        if coefficient not in (-1, 1) or primitive[pivot] is not None:
            raise ArithmeticError('invalid unit recurrence in normal-ray producer')
        total = 0
        for index, value in equation.items():
            if index != pivot:
                if primitive[index] is None:
                    raise ArithmeticError('normal-ray recurrence used an unknown coordinate')
                total += value*primitive[index]
        value = -coefficient*total
        if not 0 < value <= source[pivot]:
            raise ArithmeticError('normal-ray recurrence left the positive source support')
        primitive[pivot] = value
    if any(value is None for value in primitive):
        raise ArithmeticError('normal-ray recurrence did not recover all coordinates')
    return [primitive[7*t:7*t+7] for t in range(len(analysed['rows']))]


def normal_ray_block_disk_count(triangulation, coordinates, *, max_cycles=None,
                                 periodic_rule='fine_wilf', check=lambda: None,
                                 record_certificate=False):
    """Count essential-disc components, bypassing orbits on rank-one blocks.

    ``max_cycles`` is a shared allowance for all fallback orbit queries.
    A zero allowance still permits any number of certified ray blocks.
    There is deliberately no claim about the total component count: a
    multiple of a one-sided primitive ray need not have that many components.
    """
    if type(record_certificate) is not bool:
        raise ValueError('record_certificate must be bool')
    if max_cycles is not None and (type(max_cycles) is not int or max_cycles < 0):
        raise ValueError('max_cycles must be a nonnegative integer or None')
    if periodic_rule not in ('fine_wilf', 'aht'):
        raise ValueError('unknown periodic rule')
    check()
    prepared = _prepare(triangulation, check)
    analysed = _coordinates(prepared, coordinates, check)
    blocks = _support_blocks(prepared, analysed, check)
    basis = boundary_homology_basis(prepared, check)
    source = [value for row in analysed['rows'] for value in row]
    entries, dimensions = [], []
    total = cycles = ray_blocks = fallback_blocks = 0
    peeling_ray_blocks = compiled_ray_blocks = 0
    for support in blocks:
        check()
        flat = [0] * len(source)
        for index in support:
            check()
            flat[index] = source[index]
        rows = [flat[7*t:7*t+7] for t in range(len(analysed['rows']))]
        block = _coordinates(prepared, rows, check)
        kernel = peel_support_ray(prepared, block, check)
        peeled = kernel is not None
        if kernel is None:
            kernel = compile_support(prepared, block, check)
        dimension = kernel['nullity']
        dimensions.append(dimension)
        if dimension < 1:
            raise ArithmeticError('a nonempty matching block has zero nullity')
        if dimension == 1:
            if peeled:
                # Unit-pivot propagation makes every coordinate an integer
                # multiple of this one; its own multiplier is one.
                divisor = source[kernel['seed']]
                primitive_rows = _primitive_peeling_rows(prepared, block, kernel, check)
                primitive = _coordinates(prepared, primitive_rows, check)
                chi = primitive['euler_characteristic']
                parity = []
                for cycle in basis:
                    value = 0
                    for edge in cycle:
                        check()
                        value += primitive['weights'][edge]
                    parity.append(value & 1)
            else:
                divisor = 0
                for index in support:
                    check()
                    divisor = gcd(divisor, source[index])
                chi, remainder = divmod(block['euler_characteristic'], divisor)
                if remainder:
                    raise ArithmeticError('primitive Euler characteristic is not integral')
                parity = []
                for cycle in basis:
                    check()
                    count = sum(block['weights'][edge] for edge in cycle)
                    value, remainder = divmod(count, divisor)
                    if remainder:
                        raise ArithmeticError('primitive boundary weight is not integral')
                    parity.append(value & 1)
            count = divisor if chi == 1 and any(parity) else 0
            entry = dict(support=support, method='ray', support_certificate=kernel,
                         coordinate_divisor=divisor,
                         primitive_euler_characteristic=chi,
                         primitive_boundary_homology_mod2=parity,
                         compressing_disk_components=count)
            ray_blocks += 1
            if peeled:
                peeling_ray_blocks += 1
            else:
                compiled_ray_blocks += 1
        else:
            allowance = None if max_cycles is None else max_cycles-cycles
            answer = normal_compressing_disk_count(triangulation, rows,
                max_cycles=allowance, periodic_rule=periodic_rule,
                check=check, record_certificate=record_certificate)
            cycles += answer['stats']['orbit_cycles']
            fallback_blocks += 1
            if answer['status'] != 'COMPLETE':
                check()
                return dict(status='INCONCLUSIVE',
                    reason='shared fallback orbit-cycle allowance exhausted',
                    stats=dict(blocks=len(blocks), ray_blocks=ray_blocks,
                               fallback_blocks=fallback_blocks, orbit_cycles=cycles,
                               peeling_ray_blocks=peeling_ray_blocks,
                               compiled_ray_blocks=compiled_ray_blocks,
                               support_dimensions=dimensions))
            count = answer['compressing_disk_components']
            entry = dict(support=support, method='component_census',
                         compressing_disk_components=count)
            if record_certificate:
                entry['certificate'] = answer['certificate']
        total += count
        if record_certificate:
            entries.append(entry)
    answer = dict(status='COMPLETE', compressing_disk_components=total,
                  contains_compressing_disk=bool(total),
                  stats=dict(blocks=len(blocks), ray_blocks=ray_blocks,
                             fallback_blocks=fallback_blocks, orbit_cycles=cycles,
                             peeling_ray_blocks=peeling_ray_blocks,
                             compiled_ray_blocks=compiled_ray_blocks,
                             support_dimensions=dimensions),
                  trust='disc components of this supplied normal vector only; '
                        'no knot-diagram correspondence asserted')
    if record_certificate:
        certificate = dict(schema='normal-ray-block-disks-v1',
            input_sha256=_fingerprint(triangulation, analysed, check),
            boundary_homology_basis=basis, blocks=entries,
            compressing_disk_components=total)
        from .normal_ray_blocks_verify import verify_normal_ray_block_disk_certificate
        if not verify_normal_ray_block_disk_certificate(triangulation, coordinates,
                                                        certificate, check=check):
            raise ArithmeticError('normal ray-block certificate failed independent replay')
        answer['certificate'] = certificate
    check()
    return answer
