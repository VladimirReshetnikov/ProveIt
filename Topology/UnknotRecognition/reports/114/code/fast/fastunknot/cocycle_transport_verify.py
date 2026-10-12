"""Independent replay of cocycle transport and source-bound disc certificates.

No transport, cocycle seed, Pachner move, or orbit producer is imported.
The checker uses signed edge differences and full normal cell counts, not
the producer's gap formula. Callback cancellation propagates.
"""
from itertools import combinations
from functools import wraps

from .integer_codec import encoded_integer
from .normal_surface_geometry import _prepare, _coordinates, _EDGES, NormalOrbitError
from .pachner23_verify import verify_pachner_23
from .pachner32_verify import verify_pachner_32


class _CallbackAbort(BaseException):
    """Keep callback failures distinct from malformed-certificate failures."""
    def __init__(self, original):
        self.original = original


def _shield_callback(function):
    """Preserve arbitrary callback exceptions across input-validation catches.

    Each nested public call adds and removes its own shield. This matters
    when a callback is itself another API's budget or protected callback.
    """
    @wraps(function)
    def wrapped(*args, **kwargs):
        callback = kwargs.get('check', lambda: None)

        def protected():
            try:
                callback()
            except BaseException as error:
                raise _CallbackAbort(error) from None

        kwargs['check'] = protected
        try:
            return function(*args, **kwargs)
        except _CallbackAbort as error:
            raise error.original from None

    return wrapped


def _read_heights(rows, count, check):
    if type(rows) is not list or len(rows) != count:
        return None
    answer = []
    for row in rows:
        check()
        if type(row) is not list or len(row) != 4:
            return None
        try:
            answer.append([encoded_integer(x) for x in row])
        except ValueError:
            return None
    return answer


def _check_signed_edges(prepared, heights, check):
    values = {}
    for t, row in enumerate(heights):
        check()
        for j, (a, b) in enumerate(_EDGES):
            edge = 6*t+j
            value = (row[a]-row[b] if prepared['edge_orientations'][edge]
                     else row[b]-row[a])
            root = prepared['edge_roots'][edge]
            if root in values and values[root] != value:
                return False
            values[root] = value
    return True


@_shield_callback
def verify_cocycle_transport(before, heights, after, certificate, *, check=lambda: None):
    """Verify class-preserving transport and the exact two global cell jumps."""
    check()
    fields = {'schema', 'move', 'bipyramid_heights', 'heights', 'coordinates',
              'euler_jump', 'normal_disc_jump'}
    if (type(certificate) is not dict or set(certificate) != fields
            or certificate['schema'] != 'pachner-cocycle-transport-v1'):
        return False
    move = certificate['move']
    schema = move.get('schema') if type(move) is dict else None
    verify = {'pachner-23-v1': verify_pachner_23,
              'pachner-32-v1': verify_pachner_32}.get(schema)
    if verify is None or not verify(before, after, move, check=check):
        return False
    try:
        old = _prepare(before, check)
        new = _prepare(after, check)
    except NormalOrbitError:
        return False
    h = _read_heights(heights, len(old['tetrahedra']), check)
    k = _read_heights(certificate['heights'], len(new['tetrahedra']), check)
    five = certificate['bipyramid_heights']
    if h is None or k is None or type(five) is not list or len(five) != 5:
        return False
    try:
        five = [encoded_integer(x) for x in five]
        euler_jump = encoded_integer(certificate['euler_jump'])
        normal_jump = encoded_integer(certificate['normal_disc_jump'])
    except ValueError:
        return False
    if five[0] != 0 or not _check_signed_edges(old, h, check):
        return False
    if schema == 'pachner-32-v1':
        region = {item['tetrahedron']: item['vertices'] for item in move['region']}
        replacement = [(0,1,2,3), (0,1,2,4)]
    else:
        t, f = move['tetrahedron'], move['face']
        entry = old['tetrahedra'][t][f]
        u, permutation = entry['tetrahedron'], entry['permutation']
        shared = [v for v in range(4) if v != f]
        left = [shared.index(v) if v != f else 3 for v in range(4)]
        right = [4 if v == permutation[f] else left[permutation.index(v)] for v in range(4)]
        region = {t: left, u: right}
        replacement = [(3,4,0,1), (3,4,1,2), (3,4,2,0)]
    survivors = [t for t in range(len(h)) if t not in region]
    for t, labels in region.items():
        check()
        for a, b in combinations(range(4), 2):
            if h[t][b]-h[t][a] != five[labels[b]]-five[labels[a]]:
                return False
    for out, t in enumerate(survivors):
        check()
        if k[out] != [v-h[t][0] for v in h[t]]:
            return False
    for i, labels in enumerate(replacement, len(survivors)):
        check()
        if k[i] != [five[v]-five[labels[0]] for v in labels]:
            return False
    if not _check_signed_edges(new, k, check):
        return False
    try:
        analysed = _coordinates(new, certificate['coordinates'], check)
    except NormalOrbitError:
        return False
    # Admissibility and the six edge weights uniquely determine each local
    # normal vector; the producer's local_coordinates routine is not used.
    for t, row in enumerate(k):
        check()
        for j, (a, b) in enumerate(_EDGES):
            root = new['edge_roots'][6*t+j]
            if analysed['weights'][root] != abs(row[b]-row[a]):
                return False
    # Independently recover the source Euler count by integer coarea cell
    # counts: edge magnitudes, unique-face spans, and tetrahedron spans.
    edge_weights = {}
    for t, row in enumerate(h):
        check()
        for j, (a, b) in enumerate(_EDGES):
            edge_weights[old['edge_roots'][6*t+j]] = abs(row[b]-row[a])
    old_pieces = sum(max(row)-min(row) for row in h)
    faces = old['boundary_faces'] + [(t,f) for t,f,u,g,p in old['pairs']]
    old_arcs = 0
    for t, f in faces:
        check()
        row = [h[t][v] for v in range(4) if v != f]
        old_arcs += max(row)-min(row)
    old_euler = sum(edge_weights.values())-old_arcs+old_pieces
    check()
    return (analysed['euler_characteristic']-old_euler == euler_jump
            and analysed['normal_disks']-old_pieces == normal_jump)
