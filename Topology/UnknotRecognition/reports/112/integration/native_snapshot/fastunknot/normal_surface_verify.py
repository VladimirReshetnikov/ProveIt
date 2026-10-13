"""Replay supplied-normal-surface topology without any orbit search.

The finite manifold validator and normal-arc construction are shared with the
producer. Orbit scheduling and boundary cohomology search are not rerun.
The certified object is the caller's triangulation and normal vector, never
an implicitly associated knot diagram. Invalid source geometry raises the
same NormalOrbitError as the producer; malformed certificates return False.
"""

from .integer_codec import encoded_integer
from .interval_orbit_verify import verify_orbit_certificate
from .normal_surface_geometry import (
    _prepare, _coordinates, _arc_system, _boundary_graph, _fingerprint,
    _divide_coordinates,
    _boundary_intervals, _coned_pairings,
)
from .normal_surface_parity import _verify_parity


def _boundary_counts(prepared, analysed, systems, counts, proofs, check, *, even_multiple):
    """Replay supplied cones and derive any omitted counts without a planner."""
    total, double, boundary = (counts[key] for key in ('surface', 'double', 'boundary'))
    known = {}
    if boundary == 0:
        known = {'surface': 0, 'double': 0}
    elif total == 1:
        known = {'surface': 1, 'double': double}
    elif boundary == 1:
        known['surface'] = 1
    extra = set(proofs) - {'surface', 'double', 'boundary'}
    if len(known) < 2 or extra:
        marks = _boundary_intervals(prepared, analysed, check=check)
        if marks == ((0, systems['surface'][0]),):
            for name, value in (('surface', total), ('double', double)):
                if name in known and known[name] != value:
                    return None
                known[name] = value
        for name, scale in (('surface', 1), ('double', 2)):
            label = name + '_boundary_cone'
            if label not in proofs:
                continue
            if not marks:
                return None
            size, pairings = systems[name]
            intervals = marks if scale == 1 else _boundary_intervals(
                prepared, analysed, scale=2, check=check)
            coned = _coned_pairings(pairings, intervals, check)
            if not verify_orbit_certificate(size, coned, proofs[label], check=check):
                return None
            value = counts[name] - encoded_integer(proofs[label]['orbit_count']) + 1
            if name in known and known[name] != value:
                return None
            known[name] = value
    # Pure orientability relates the two counts in either direction. This
    # accepts complete redundant proofs or a sound alternate choice of cone.
    if double in (total, 2 * total):
        factor = 1 if double == total else 2
        if 'surface' in known:
            value = factor * known['surface']
            if 'double' in known and known['double'] != value:
                return None
            known['double'] = value
        elif 'double' in known:
            if known['double'] % factor:
                return None
            known['surface'] = known['double'] // factor
    if set(known) == {'double'} and even_multiple:
        if not 1 <= known['double'] <= min(double, 2*boundary):
            return None
        # An even multiple only needs the touched count of the orientable 2Q.
        return None, known['double']
    if set(known) != {'surface', 'double'}:
        return None
    touched, lifted = known['surface'], known['double']
    orientable, nonorientable = lifted-touched, 2*touched-lifted
    if (not 0 <= orientable <= double-total
            or not 0 <= nonorientable <= 2*total-double
            or (touched != 0 if boundary == 0 else
                not 1 <= touched <= min(total, boundary))):
        return None
    return touched, lifted


def verify_normal_surface_certificate(triangulation, coordinates, certificate, *,
                                      max_operations=None, check=lambda: None):
    """Verify exact source binding, all supplied orbit proofs and every claim.

    max_operations bounds the combined number of recorded orbit events before
    replay. Exceeding it returns False (unverified), never a topological result.
    Callbacks propagate, including ValueError; deadlines and serialized-size
    limits can be imposed by the caller. Running time is polynomial in the
    encoded triangulation, coordinates, and supplied trace lengths.
    Version two checks an exact common coordinate divisor and lifts the verified
    quotient counts, accounting for one-sided components. Version one is retained.
    Version three also classifies boundary-touching and closed components.
    Missing cone queries require deductions from the verified base counts or
    full marked support; the producer's scheduling policy is never invoked.
    Version four replaces the double query by a finite coorientation proof
    and an exact doubled count, with an explicit boundary-classification flag.
    """
    check()
    if max_operations is not None and (type(max_operations) is not int or max_operations < 0):
        raise ValueError('max_operations must be a nonnegative integer or None')
    if type(certificate) is not dict:
        return False
    schema = certificate.get('schema')
    if schema not in ('normal-surface-topology-v1', 'normal-surface-topology-v2',
                      'normal-surface-topology-v3', 'normal-surface-topology-v4'):
        return False
    fields = {'schema', 'input_sha256', 'queries', 'boundary_homology', 'topology'}
    if schema != 'normal-surface-topology-v1':
        fields.add('coordinate_divisor')
    classify = schema == 'normal-surface-topology-v3'
    if schema == 'normal-surface-topology-v4':
        fields.add('classify_boundary')
        if type(certificate.get('classify_boundary')) is not bool:
            return False
        classify = certificate['classify_boundary']
    if set(certificate) != fields:
        return False
    proofs = certificate['queries']
    base_labels = {'surface', 'double', 'boundary'}
    extra_labels = ({'surface_boundary_cone', 'double_boundary_cone'}
                    if classify else set())
    if (type(proofs) is not dict or not base_labels <= set(proofs)
            or not set(proofs) <= base_labels | extra_labels):
        return False
    operations = 0
    for proof in proofs.values():
        check()
        if type(proof) is not dict or type(proof.get('operations')) is not list:
            return False
        operations += len(proof['operations'])
    if max_operations is not None and operations > max_operations:
        return False
    prepared = _prepare(triangulation, check)
    analysed = _coordinates(prepared, coordinates, check)
    if certificate['input_sha256'] != _fingerprint(triangulation, analysed, check):
        return False
    divisor, orbit_data = 1, analysed
    if schema != 'normal-surface-topology-v1':
        try:
            divisor = encoded_integer(certificate['coordinate_divisor'])
        except ValueError:
            return False
        # Check witness validity separately from the cancellable geometry helper,
        # so exceptions raised by a caller's check callback always propagate.
        minimum = 2 if schema == 'normal-surface-topology-v2' else 1
        if divisor < minimum or (divisor > 1 and not analysed['normal_disks']):
            return False
        for row in analysed['rows']:
            check()
            if any(value % divisor for value in row):
                return False
        if divisor > 1:
            orbit_data = _divide_coordinates(analysed, divisor, check)
    counts, systems = {}, {}
    for label, boundary, scale in [('surface', False, 1),
                                    ('double', False, 2), ('boundary', True, 1)]:
        check()
        size, pairings = _arc_system(prepared, orbit_data, boundary=boundary,
                                     scale=scale, check=check)
        if (classify or schema == 'normal-surface-topology-v4') and not boundary:
            systems[label] = size, pairings
        if schema == 'normal-surface-topology-v4' and label == 'double':
            proof = proofs[label]
            if (set(proof) != {'schema','coorientation','orbit_count','operations'}
                    or proof['schema'] != 'normal-double-coorientation-v1'
                    or proof['operations'] != []
                    or type(proof['coorientation']) is not dict
                    or set(proof['coorientation']) != {'nonzero','vertex_values'}
                    or proof['coorientation'].get('nonzero') is not False):
                return False
            from .normal_coorientation import _coorientation_graph
            graph = _coorientation_graph(orbit_data, systems['surface'][1], check)
            if not _verify_parity(graph, proof['coorientation'], check):
                return False
            try:
                count = encoded_integer(proof['orbit_count'])
            except ValueError:
                return False
            if count != 2*counts['surface']:
                return False
            counts[label] = count
            continue
        if not verify_orbit_certificate(size, pairings, proofs[label], check=check):
            return False
        counts[label] = encoded_integer(proofs[label]['orbit_count'])
    parity = certificate['boundary_homology']
    if not _verify_parity(_boundary_graph(prepared, analysed, check), parity, check):
        return False
    components, lifted, boundary = (counts[key] for key in ('surface', 'double', 'boundary'))
    orientable, nonorientable = lifted - components, 2 * components - lifted
    if min(orientable, nonorientable) < 0:
        return False
    boundary_counts = None
    if classify:
        boundary_counts = _boundary_counts(prepared, orbit_data, systems, counts, proofs, check,
                                           even_multiple=divisor % 2 == 0)
        if boundary_counts is None:
            return False
    # Each two-sided component has divisor copies. A one-sided component has
    # floor(divisor/2) double covers and, for odd divisor, its middle sheet.
    orientable, nonorientable = (divisor * orientable + (divisor // 2) * nonorientable,
                                 (divisor % 2) * nonorientable)
    components = orientable + nonorientable
    boundary *= divisor
    chi = analysed['euler_characteristic']
    expected = dict(components=components, orientable_components=orientable,
                    nonorientable_components=nonorientable, boundary_components=boundary,
                    euler_characteristic=chi, normal_disks=analysed['normal_disks'],
                    compressing_disk=(components == 1 and chi == 1 and boundary == 1
                                      and parity['nonzero']))
    if boundary_counts is not None:
        touched, covered = boundary_counts
        if touched is None:
            boundary_o, boundary_n = (divisor // 2) * covered, 0
        else:
            boundary_o, boundary_n = covered-touched, 2*touched-covered
            boundary_o, boundary_n = (divisor * boundary_o + (divisor // 2) * boundary_n,
                                       (divisor % 2) * boundary_n)
        touched = boundary_o + boundary_n
        expected.update(components_with_boundary=touched, closed_components=components-touched,
                        orientable_components_with_boundary=boundary_o,
                        nonorientable_components_with_boundary=boundary_n,
                        closed_orientable_components=orientable-boundary_o,
                        closed_nonorientable_components=nonorientable-boundary_n)
    if components == 1:
        defect = 2 - boundary - chi
        if orientable:
            if defect < 0 or defect & 1:
                return False
            expected['genus'] = defect // 2
        else:
            if defect < 1:
                return False
            expected['crosscaps'] = defect
    supplied = certificate['topology']
    if type(supplied) is not dict or set(supplied) != set(expected):
        return False
    for key, value in expected.items():
        check()
        if type(value) is bool:
            if type(supplied[key]) is not bool or supplied[key] != value:
                return False
        else:
            try:
                actual = encoded_integer(supplied[key])
            except ValueError:
                return False
            if actual != value:
                return False
    check()
    return True
