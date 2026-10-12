"""Integral cocycle transport and exact scores for formal Pachner regions.

The five abstract bipyramid heights preserve the global cohomology class.
They do not preserve the topology or connectivity of its coherent surface.
Every returned transport is independently replayed; no knot verdict is
inferred from a total Euler characteristic.
"""
from copy import deepcopy

from .integer_codec import encoded_integer
from .normal_cocycle import _Budget, local_coordinates
from .normal_surface_geometry import _prepare, _EDGES, NormalOrbitError
from .cocycle_transport_verify import _shield_callback


def bipyramid_cocycle_score(heights):
    """Exact 2--3 jumps from heights (belt C,D,E, apices A,B).

    Both the Euler loss 2*gap and normal-disc increase are nonnegative.
    This performs O(1) integer operations, independently of layer count.
    """
    if type(heights) not in (list, tuple) or len(heights) != 5:
        raise ValueError('five integral bipyramid heights are required')
    c, d, e, a, b = [encoded_integer(x) for x in heights]
    x, y, z = sorted((c, d, e))
    low, high = min(a, b), max(a, b)
    gap = max(0, low-z) + max(0, x-high)
    pieces = (max(high, y)-min(low, y)
              + max(0, min(high, x)-low)
              + max(0, high-max(low, z)))
    return dict(gap=gap, euler_loss=2*gap, normal_disc_increase=pieces)


def _integer_heights(prepared, heights, check):
    if type(heights) is not list or len(heights) != len(prepared['tetrahedra']):
        raise ValueError('one four-entry integral height row per tetrahedron is required')
    result = []
    values = {}
    for t, row in enumerate(heights):
        check()
        if type(row) is not list or len(row) != 4:
            raise ValueError('each height row must contain four integers')
        h = [encoded_integer(x) for x in row]
        result.append([x-h[0] for x in h])
        for j, (a, b) in enumerate(_EDGES):
            check()
            local = 6*t+j
            value = h[b]-h[a]
            if prepared['edge_orientations'][local]:
                value = -value
            edge = prepared['edge_roots'][local]
            if edge in values and values[edge] != value:
                raise NormalOrbitError('height differences are not a global integral cocycle')
            values[edge] = value
    return result


def _region_heights(region, heights, check):
    """Recover the five heights by propagation through shared formal labels."""
    remaining = dict(region)
    first = min(remaining)
    values = dict(zip(region[first], heights[first]))
    del remaining[first]
    while remaining:
        advanced = False
        for t, labels in list(remaining.items()):
            check()
            known = [i for i, v in enumerate(labels) if v in values]
            if not known:
                continue
            i = known[0]
            offset = values[labels[i]]-heights[t][i]
            for j, label in enumerate(labels):
                value = heights[t][j]+offset
                if label in values and values[label] != value:
                    raise NormalOrbitError('the formal bipyramid does not admit coherent heights')
                values[label] = value
            del remaining[t]
            advanced = True
        if not advanced:
            raise NormalOrbitError('the formal bipyramid is disconnected')
    if set(values) != set(range(5)):
        raise NormalOrbitError('the formal bipyramid lacks five labelled vertices')
    offset = values[0]
    return [values[i]-offset for i in range(5)]


def _move_region(rows, move):
    if move['schema'] == 'pachner-32-v1':
        return {item['tetrahedron']: item['vertices'] for item in move['region']}
    t, f = move['tetrahedron'], move['face']
    entry = rows[t][f]
    u, permutation = entry['tetrahedron'], entry['permutation']
    left, right = [3]*4, [4]*4
    for label, v in enumerate(v for v in range(4) if v != f):
        left[v] = label
        right[permutation[v]] = label
    return {t: left, u: right}


@_shield_callback
def transport_cocycle(before, heights, after, move_certificate, *, max_work=None,
                      check=lambda: None):
    """Transport a cocycle through a supplied independently valid 2--3/3--2 move.

    Untouched rows are normalized but their signed edge values are preserved.
    Local arithmetic is constant-size; emitting all rows and replaying both
    finite manifolds costs at least linear work in tetrahedron count.
    """
    from .pachner23_verify import verify_pachner_23
    from .pachner32_verify import verify_pachner_32
    from .cocycle_transport_verify import verify_cocycle_transport

    budget = _Budget(check, max_work)
    budget.tick()
    schema = move_certificate.get('schema') if type(move_certificate) is dict else None
    verifier = {'pachner-23-v1': verify_pachner_23,
                'pachner-32-v1': verify_pachner_32}.get(schema)
    if verifier is None or not verifier(before, after, move_certificate, check=budget.tick):
        raise ValueError('a valid canonical Pachner replacement is required')
    prepared = _prepare(before, budget.tick)
    h = _integer_heights(prepared, heights, budget.tick)
    region = _move_region(prepared['tetrahedra'], move_certificate)
    five = _region_heights(region, h, budget.tick)
    labels = ((3,4,0,1), (3,4,1,2), (3,4,2,0)) if schema == 'pachner-23-v1' else (
        (0,1,2,3), (0,1,2,4))
    output = []
    for t, row in enumerate(h):
        budget.tick()
        if t not in region:
            output.append([x-row[0] for x in row])
    for row in labels:
        budget.tick()
        output.append([five[v]-five[row[0]] for v in row])
    coordinates = []
    for row in output:
        budget.tick()
        coordinates.append(local_coordinates(row))
    score = bipyramid_cocycle_score(five)
    sign = 1 if schema == 'pachner-23-v1' else -1
    certificate = dict(schema='pachner-cocycle-transport-v1',
        move=deepcopy(move_certificate), bipyramid_heights=five,
        heights=output, coordinates=coordinates,
        euler_jump=-sign*score['euler_loss'],
        normal_disc_jump=sign*score['normal_disc_increase'])
    if not verify_cocycle_transport(before, h, after, certificate, check=budget.tick):
        raise ArithmeticError('cocycle transport failed independent replay')
    return dict(heights=output, coordinates=coordinates, certificate=certificate,
                score=score, stats=dict(work=budget.work, height_rows=len(output),
                    replaced_tetrahedra=len(region), new_tetrahedra=len(labels)))


def _collapse_region(rows, occurrences, check):
    """Recognize one degree-three formal bipyramid without another preparation."""
    if len(occurrences) != 3 or len({t for t, a, b in occurrences}) != 3:
        return None
    first, a, b = occurrences[0]
    labels = [-1]*4
    labels[a], labels[b] = 3, 4
    for i, v in enumerate(v for v in range(4) if v not in (a, b)):
        labels[v] = i
    region, selected = {first: labels}, {t for t, a, b in occurrences}
    queue = [first]
    for t in queue:
        check()
        for f in range(4):
            if region[t][f] in (3,4):
                continue
            entry = rows[t][f]
            if entry is None or entry['tetrahedron'] not in selected:
                return None
            u, permutation = entry['tetrahedron'], entry['permutation']
            if u in region:
                if any(region[t][v] != region[u][permutation[v]]
                       for v in range(4) if v != f):
                    return None
            else:
                other = [-1]*4
                for v in range(4):
                    if v != f:
                        other[permutation[v]] = region[t][v]
                absent = {0,1,2}-set(region[t])
                if len(absent) != 1:
                    return None
                other[permutation[f]] = absent.pop()
                region[u] = other
                queue.append(u)
    expected = {frozenset((3,4,0,1)), frozenset((3,4,1,2)), frozenset((3,4,2,0))}
    if set(region) != selected or {frozenset(row) for row in region.values()} != expected:
        return None
    return region


@_shield_callback
def cocycle_collapse_candidates(triangulation, heights, *, max_work=None,
                                check=lambda: None):
    """Score all eligible degree-three collapses in one incidence scan.

    Candidates retain local-incidence order; choosing their largest score
    requires only a linear scan. No candidate is a topology verdict.
    """
    budget = _Budget(check, max_work)
    prepared = _prepare(triangulation, budget.tick)
    h = _integer_heights(prepared, heights, budget.tick)
    groups = {}
    for local, root in enumerate(prepared['edge_roots']):
        budget.tick()
        groups.setdefault(root, []).append((local//6, *_EDGES[local%6]))
    candidates = []
    for edge, occurrences in groups.items():
        budget.tick()
        region = _collapse_region(prepared['tetrahedra'], occurrences, budget.tick)
        if region is None:
            continue
        five = _region_heights(region, h, budget.tick)
        score = bipyramid_cocycle_score(five)
        t, a, b = occurrences[0]
        candidates.append(dict(tetrahedron=t, vertices=[a,b], edge=edge,
            euler_gain=score['euler_loss'], normal_disc_saving=score['normal_disc_increase'],
            bipyramid_heights=five))
    return dict(candidates=candidates, stats=dict(work=budget.work,
        global_edges=len(groups), candidates=len(candidates)))


@_shield_callback
def descend_cocycle(triangulation, heights, *, strategy='score', max_moves=None,
                    max_work=None, check=lambda: None):
    """Perform a checked monotone 3--2 epoch, without a topology verdict.

    'score' chooses largest Euler gain, then largest normal-disc saving;
    ties follow local incidence order. 'first' retains the first valid site.
    A move cap limits discovery, not the validity of the returned transcript.
    The ordinary complete triangulations retained at every step can occupy
    quadratic storage. No persistent-data-structure improvement is claimed.
    """
    from .pachner32 import pachner_32

    if strategy not in ('score', 'first'):
        raise ValueError('strategy must be score or first')
    if max_moves is not None and (type(max_moves) is not int or max_moves < 0):
        raise ValueError('max_moves must be a nonnegative integer or None')
    budget = _Budget(check, max_work)
    raw, h = triangulation, heights
    trace, choices, gain, saving = [], [], 0, 0
    candidate_count = 0
    terminal = False
    while max_moves is None or len(trace) < max_moves:
        budget.tick()
        available = cocycle_collapse_candidates(raw, h, check=budget.tick)
        candidates = available['candidates']
        candidate_count += len(candidates)
        if not candidates:
            terminal = True
            break
        selected = (max(candidates, key=lambda c: (c['euler_gain'], c['normal_disc_saving']))
                    if strategy == 'score' else candidates[0])
        replacement = pachner_32(raw, selected['tetrahedron'], selected['vertices'],
                                 check=budget.tick)
        after = replacement['triangulation']
        transported = transport_cocycle(raw, h, after, replacement['certificate'],
                                       check=budget.tick)
        if (transported['certificate']['euler_jump'] != selected['euler_gain']
                or transported['certificate']['normal_disc_jump'] != -selected['normal_disc_saving']):
            raise ArithmeticError('selected local score disagrees with independent cell replay')
        trace.append(dict(triangulation=after, transport=transported['certificate']))
        choices.append(dict(selected, alternatives=len(candidates)))
        gain += selected['euler_gain']
        saving += selected['normal_disc_saving']
        raw, h = after, transported['heights']
    # A capped zero-move epoch still validates the caller's height rows.
    prepared = _prepare(raw, budget.tick)
    h = _integer_heights(prepared, h, budget.tick)
    coordinates = []
    for row in h:
        budget.tick()
        coordinates.append(local_coordinates(row))
    return dict(status='TERMINAL' if terminal else 'MOVE_LIMIT',
        triangulation=deepcopy(raw), heights=h, coordinates=coordinates,
        moves=trace, choices=choices,
        stats=dict(work=budget.work, moves=len(trace), scored_candidates=candidate_count,
                   euler_gain=gain, normal_disc_saving=saving,
                   initial_tetrahedra=len(triangulation['tetrahedra']),
                   remaining_tetrahedra=len(raw['tetrahedra'])))
