"""Producer-independent replay of whole-cut relative bundle certificates.

True authenticates the exact conclusion in the certificate.  In particular,
an INCONCLUSIVE conclusion with a stopping core is not a non-handlebody proof.
The verifier imports neither the relative compiler nor the peeling producer.
"""

from collections import Counter

from fastunknot.integer_codec import encoded_integer, certificate_equal
from fastunknot.normal_parallelity_verify import verify_normal_cut_parallelity
from fastunknot.parallelity_boundary_words_verify import verify_parallelity_boundary_words

from column_peeling_verify import verify_column_peeling_certificate
from relative_bundles_verify import replay_relative_bundle_compilation


class _CallbackFailure(Exception):
    def __init__(self, original):
        self.original = original


def _decode(value):
    if isinstance(value, dict):
        return {key: _decode(item) for key, item in value.items()}
    if isinstance(value, list):
        return [_decode(item) for item in value]
    if isinstance(value, str) and value.lower().lstrip('+-').startswith('0x'):
        return encoded_integer(value)
    return value


def _orbit_operations(parallelity, boundary=None):
    total = 0
    for name in ('vertex_selector', 'boundary_selector', 'polygon_weights', 'fibre_cover'):
        proof = parallelity[name]
        if name.endswith('selector'):
            proof = proof['weighted_certificate']
        total += len(proof['orbit_proof']['operations'])
    if boundary is not None:
        for name in ('vertex_partition', 'gap_cover'):
            proof = boundary[name]
            if proof is not None:
                total += len(proof['orbit_proof']['operations'])
    return total


def _independent_original_core(core, proof, check):
    """Rebuild source incidences and the deterministic forest without a producer.

    Connectivity search on previously selected forest edges deliberately
    replaces the producer's disjoint-set algorithm.  Raw alternating source
    cycles are checked and read directly; asserted occurrence counts are not
    trusted.  The source geometry itself has already passed upstream replay.
    """
    if type(proof) is not dict or set(proof) != {'forest', 'rows'}:
        return None
    vertices, edges, discs = [core['handles' + str(i)] for i in range(3)]
    if any(type(h['id']) is not int or h['id'] != i
           for handles in (vertices, edges, discs) for i, h in enumerate(handles)):
        return None
    adjacency = {v: set() for v in range(len(vertices))}
    forest = []
    for e, handle in enumerate(edges):
        check()
        a, b = handle['ends']
        if any(type(v) is not int or not 0 <= v < len(vertices) for v in (a, b)):
            return None
        todo, seen = [a], set()
        while todo:
            check()
            current = todo.pop()
            if current in seen:
                continue
            seen.add(current)
            todo.extend(adjacency[current] - seen)
        if b not in seen:
            forest.append(e)
            adjacency[a].add(b)
            adjacency[b].add(a)
    if not certificate_equal(proof['forest'], forest):
        return None
    tree = set(forest)
    matrix = {}
    for r, handle in enumerate(discs):
        check()
        cycle = handle['cycle']
        if type(cycle) is not list or not cycle or len(cycle) % 2:
            return None
        row = {}
        for j in range(0, len(cycle), 2):
            check()
            point, crossing = cycle[j], cycle[j + 1]
            if point['dimension'] != 0 or crossing['dimension'] != 1:
                return None
            v, e = point['handle'], crossing['handle']
            following = cycle[(j + 2) % len(cycle)]['handle']
            if any(type(x) is not int for x in (v, e, following)):
                return None
            if not (0 <= v < len(vertices) and 0 <= following < len(vertices)
                    and 0 <= e < len(edges)):
                return None
            if sorted((v, following)) != sorted(edges[e]['ends']):
                return None
            if e not in tree:
                row[e] = min(2, row.get(e, 0) + 1)
        matrix[r] = row
    expected = [dict(id=r, counts=[[c, v] for c, v in sorted(row.items())])
                for r, row in sorted(matrix.items())]
    if not certificate_equal(proof['rows'], expected):
        return None
    return matrix


def _replay_core_obstruction(triangulation, coordinates, certificate, max_operations, check):
    fields = {'schema', 'parallelity', 'core', 'peeling', 'conclusion'}
    if set(certificate) != fields:
        return False
    p = certificate['parallelity']
    if type(p) is not dict:
        return False
    if max_operations is not None and _orbit_operations(p) > max_operations:
        return False
    if not verify_normal_cut_parallelity(triangulation, coordinates, p, check=check):
        return False
    geometry, summary = _decode(p['geometry']), _decode(p['summary'])
    if geometry['core']['handles3']:
        return False
    if any(profile['boundary_components'] == 0 for profile in summary['base_profiles']):
        return False
    counts = _independent_original_core(geometry['core'], _decode(certificate['core']), check)
    if counts is None:
        return False
    peeling = _decode(certificate['peeling'])
    if not verify_column_peeling_certificate(counts, peeling, check=check):
        return False
    residual = peeling['residual_rows']
    if not residual:
        return False
    expected = dict(status='INCONCLUSIVE', reason='original_core_raw_obstruction',
                    remaining_two_handles=residual)
    check()
    return certificate_equal(certificate['conclusion'], expected)


def _replay(triangulation, coordinates, certificate, max_operations, check):
    if type(certificate) is not dict:
        return False
    if certificate.get('schema') == 'normal-cut-core-obstruction-v1':
        return _replay_core_obstruction(
            triangulation, coordinates, certificate, max_operations, check)
    fields = {'schema', 'parallelity', 'boundary', 'relative', 'peeling', 'conclusion'}
    if type(certificate) is not dict or set(certificate) != fields:
        return False
    if certificate['schema'] != 'normal-cut-saturated-bundles-v1':
        return False
    p, b = certificate['parallelity'], certificate['boundary']
    if type(p) is not dict or type(b) is not dict:
        return False
    if max_operations is not None and _orbit_operations(p, b) > max_operations:
        return False
    if not verify_normal_cut_parallelity(triangulation, coordinates, p, check=check):
        return False
    if not verify_parallelity_boundary_words(triangulation, coordinates, b, check=check):
        return False
    geometry, summary, skeleton = _decode(p['geometry']), _decode(p['summary']), _decode(b['skeleton'])
    model = replay_relative_bundle_compilation(
        geometry, summary, skeleton, _decode(certificate['relative']), check=check)
    if model is None:
        return False
    peeling = _decode(certificate['peeling'])
    if not verify_column_peeling_certificate(model['counts'], peeling, check=check):
        return False
    residual = peeling['residual_rows']
    if residual:
        expected = dict(status='INCONCLUSIVE', reason='full_raw_cancellation_obstructed',
                        remaining_two_handles=residual)
    else:
        histogram = Counter()
        for component in model['joined_components']:
            check()
            rank = len(component['active_one_handles']) + component['private_one_handles']
            genus = rank - len(component['two_handle_rows'])
            if genus < 0:
                return False
            histogram[genus] += 1
        for bundle in model['isolated_bundles']:
            check()
            if bundle['genus'] < 0 or bundle['multiplicity'] <= 0:
                return False
            histogram[bundle['genus']] += bundle['multiplicity']
        euler = sum((1 - genus) * copies for genus, copies in histogram.items())
        if euler != model['certificate']['source_euler_characteristic']:
            return False
        census = dict(histogram=[dict(genus=g, multiplicity=m)
                                 for g, m in sorted(histogram.items())],
                      components=sum(histogram.values()), ball_components=histogram.get(0, 0),
                      all_balls=all(g == 0 for g in histogram), euler_characteristic=euler)
        expected = dict(status='COMPLETE', census=census)
    check()
    return certificate_equal(certificate['conclusion'], expected)


def verify_normal_cut_saturation(triangulation, coordinates, certificate, *,
                                  max_operations=None, check=lambda: None):
    """Authenticate source, relative bands, cancellation, and the stated result.

    The optional early core-obstruction schema replays four source traces and
    no ordered-boundary query.  The ordinary schema also authenticates the two
    boundary-query slots when present; zero-port sources have no such traces.
    max_operations caps total supplied orbit-trace operations.  It is not a
    hard time or memory limit on the source verifier or on malformed input.
    All caller callback exceptions propagate with their original type.
    """
    check()
    if max_operations is not None and (type(max_operations) is not int or max_operations < 0):
        raise ValueError('max_operations must be a nonnegative integer or None')

    def guarded_check():
        try:
            check()
        except BaseException as exc:
            raise _CallbackFailure(exc) from exc

    try:
        return _replay(triangulation, coordinates, certificate, max_operations, guarded_check)
    except _CallbackFailure as failure:
        raise failure.original.with_traceback(failure.original.__traceback__)
    except (KeyError, IndexError, TypeError, ValueError, ArithmeticError, AttributeError):
        return False
