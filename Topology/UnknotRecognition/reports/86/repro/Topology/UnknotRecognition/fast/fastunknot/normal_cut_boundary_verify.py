"""Independent source-rank reconstruction of a compressed normal cut boundary.

Face bands are rebuilt from rank events, weights from separately owned cell
counts, and cyclic recipes from integer midpoint cross products. No cut
boundary producer, chamber producer or orbit discovery routine is imported.
"""
from itertools import combinations

from .normal_surface_geometry import _prepare, _coordinates, _edge, _quad, _fingerprint, _permutation_sign
from .normal_cut_complement_verify import _reference_chambers
from .interval_orbits import IntervalPairing
from .integer_codec import encoded_integer, certificate_equal
from .orbit_transversal_verify import verify_orbit_transversal_certificate
from .weighted_orbit_verify import verify_weighted_orbit_certificate


def _reference_cycles(prepared, rows, faces, check):
    signs = {0: 1}; frontier = [0]
    while frontier:
        check(); t = frontier.pop()
        for entry in prepared['tetrahedra'][t]:
            if entry is not None and entry['tetrahedron'] not in signs:
                u = entry['tetrahedron']; signs[u] = -signs[t]*_permutation_sign(entry['permutation'])
                frontier.append(u)
    points = [(0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1)]
    def difference(a, b): return tuple(x-y for x, y in zip(a, b))
    def cross(a, b): return (a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0])
    def dot(a, b): return sum(x*y for x, y in zip(a, b))
    def midpoint(edge): return tuple(points[edge[0]][i]+points[edge[1]][i] for i in range(3))
    def orientation(vertices, direction):
        return dot(cross(difference(vertices[1], vertices[0]), difference(vertices[2], vertices[0])), direction)
    def arc(f, v, s, o, side, a, b, minimum=0):
        return dict(kind='normal_arc', face=f, corner=v, rank=[s, o], side=side,
                    forward=a < b, minimum_rank=minimum)
    def gap(t, a, b, s, o, direction):
        index = _edge(t, a, b); root = prepared['edge_roots'][index]
        backwards = bool(prepared['edge_orientations'][index]) != (a > b)
        if backwards:
            weight = rows[t][a]+rows[t][b]+sum(rows[t][4:])-rows[t][4+_quad(a, b)]
            s, o = -s, weight-o
        return dict(kind='boundary_edge', edge=root, rank=[s, o], forward=direction != backwards)
    def recipe_key(r):
        if r['kind'] == 'normal_arc':
            return (0, r['face'], r['corner'], *r['rank'], r['side'], int(r['forward']), r['minimum_rank'])
        return (1, r['edge'], *r['rank'], int(r['forward']))
    for family in faces:
        check(); t = family['tetrahedron']; cycle = []
        if family['kind'] == 'horizontal':
            column, side = family['column'], family['side']
            if column < 4:
                crossing = [edge for edge in combinations(range(4), 2) if column in edge]
                direction = tuple(sum(points[v][i] for v in range(4) if v != column)-3*points[column][i] for i in range(3))
            else:
                partition = {0, column-3}
                crossing = [edge for edge in combinations(range(4), 2) if (edge[0] in partition) != (edge[1] in partition)]
                direction = tuple(sum(points[v][i] for v in range(4) if v not in partition)-
                                  sum(points[v][i] for v in partition) for i in range(3))
            ring = [min(crossing)]
            while len(ring) < len(crossing):
                ring.append(min(edge for edge in crossing if edge not in ring and set(edge) & set(ring[-1])))
            target_sign = signs[t]*(1 if side == 0 else -1)
            if orientation([midpoint(e) for e in ring], direction)*target_sign < 0:
                ring.reverse()
            for left, right in zip(ring, ring[1:]+ring[:1]):
                v = next(iter(set(left) & set(right)))
                a = next(x for x in left if x != v); b = next(x for x in right if x != v)
                f = next(x for x in range(4) if x not in (v, a, b))
                if column < 4:
                    s, o, inward = 1, 0, side
                else:
                    positive = v in {0, column-3}; s = 1 if positive else -1
                    o = rows[t][v]+(0 if positive else rows[t][column]-1)
                    inward = side if positive else 1-side
                cycle.append(arc(f, v, s, o, inward, a, b))
        else:
            f = family['face']; ring = [v for v in range(4) if v != f]
            direction = tuple(sum(points[v][i] for v in ring)-3*points[f][i] for i in range(3))
            if orientation([points[v] for v in ring], direction)*signs[t] < 0:
                ring.reverse()
            if family['kind'] == 'original_centre':
                for i, a in enumerate(ring):
                    b, c = ring[(i+1) % 3], ring[(i+2) % 3]
                    ma = rows[t][a]+rows[t][4+_quad(f, a)]
                    mb = rows[t][b]+rows[t][4+_quad(f, b)]
                    cycle.append(gap(t, a, b, 0, ma, True))
                    if mb: cycle.append(arc(f, b, 0, mb-1, 1, a, c))
            else:
                v = family['corner']; index = ring.index(v)
                a, b = ring[(index+1) % 3], ring[(index+2) % 3]
                cycle = [gap(t, v, a, 1, 0, True), arc(f, v, 1, 0, 0, a, b),
                         gap(t, v, b, 1, 0, False), arc(f, v, 1, -1, 1, b, a, 1)]
        choices = [cycle[i:]+cycle[:i] for i in range(len(cycle))]
        family['cycle'] = min(choices, key=lambda r: tuple(recipe_key(e) for e in r))


def _reference_system(prepared, analysed, check):
    rows = analysed['rows']; starts = []; faces = []; size = 0
    for t, row in enumerate(rows):
        check(); local = []
        for col, count in enumerate(row):
            local.append([size, size+count])
            for side in (0, 1):
                if count: faces.append(dict(kind='horizontal', tetrahedron=t, column=col, side=side,
                                           start=size, stop=size+count))
                size += count
        starts.append(local)
    original = {}
    for t, f in prepared['boundary_faces']:
        check(); centre = size; arms = {}
        faces.append(dict(kind='original_centre', tetrahedron=t, face=f, start=size, stop=size+1)); size += 1
        for v in (v for v in range(4) if v != f):
            count = rows[t][v]+rows[t][4+_quad(f, v)]; arms[v] = size
            if count: faces.append(dict(kind='original_arm', tetrahedron=t, face=f, corner=v,
                                       start=size, stop=size+count))
            size += count
        original[t, f] = (centre, arms)
    roots = sorted({prepared['vertex_roots'][4*t+v] for t, f in prepared['boundary_faces'] for v in range(4) if v != f})
    old = {root: i for i, root in enumerate(roots)}
    vertices = [dict(kind='original', root=root, start=i, stop=i+1) for root, i in old.items()]
    vsize = len(roots); cut = {}
    for root, weight in sorted(analysed['weights'].items()):
        check(); cut[root] = [vsize, vsize+weight]
        for side in (0, 1):
            if weight: vertices.append(dict(kind='normal', edge=root, side=side, start=vsize, stop=vsize+weight))
            vsize += weight
    def normal(t, f, v, side, rank):
        m = rows[t][v]
        if rank < m: return 1, starts[t][v][side]
        col = 4+_quad(f, v); q = rows[t][col]
        positive = v in {0, col-3}; slope = 1 if positive else -1
        index = rank-m if positive else q-1-(rank-m)
        disk_side = side if positive else 1-side
        return slope, starts[t][col][disk_side]+index-slope*rank
    def ends(t, f, v, side):
        result = []
        for u in (x for x in range(4) if x not in (v, f)):
            local = _edge(t, v, u); root = prepared['edge_roots'][local]
            backwards = bool(prepared['edge_orientations'][local]) != (v > u)
            result.append([-1, cut[root][1-side]+analysed['weights'][root]-1] if backwards else [1, cut[root][side]])
        return result
    bands = []
    def band(kind, location, lo, hi, a, b, endpoints):
        if hi-lo == 1: a, b = (1, a[0]*lo+a[1]-lo), (1, b[0]*lo+b[1]-lo)
        bands.append(dict(kind=kind, **location, rank_start=lo, rank_stop=hi,
                          source=list(a), target=list(b), ends=endpoints))
    owned_faces = sorted(set(prepared['boundary_faces']) | {(t, f) for t, f, _, _, _ in prepared['pairs']})
    for t, f in owned_faces:
        check(); entry = prepared['tetrahedra'][t][f]
        for v in (x for x in range(4) if x != f):
            count = rows[t][v]+rows[t][4+_quad(f, v)]
            if not count: continue
            for side in (0, 1):
                bounds = {0, count, rows[t][v]}
                if entry is None:
                    u, g = t, f; flipped = False
                    if side: bounds.add(count-1)
                else:
                    u, p = entry['tetrahedron'], entry['permutation']; g = p[f]
                    bounds.add(rows[u][p[v]])
                    remaining = [x for x in range(4) if x not in (v, f)]
                    flipped = p[remaining[0]] > p[remaining[1]]
                events = sorted(bounds)
                for lo, hi in zip(events, events[1:]):
                    if lo == hi: continue
                    left = normal(t, f, v, side, lo)
                    if entry is None:
                        centre, arms = original[t, f]
                        right = (1, centre-lo) if side and lo == count-1 else (1, arms[v]+side)
                    else:
                        right = normal(u, g, p[v], side, lo)
                    location = dict(tetrahedron=t, face=f, target_tetrahedron=u, target_face=g,
                                    corner=v, side=side, target_endpoint_reversed=flipped)
                    band('normal_arc', location, lo, hi, left, right, ends(t, f, v, side))
    incidents = {}; edge_owners = {}
    for t in range(len(rows)):
        for a, b in combinations(range(4), 2):
            edge_owners.setdefault(prepared['edge_roots'][_edge(t, a, b)], (t, a, b))
    for t, f in prepared['boundary_faces']:
        for a, b in combinations((v for v in range(4) if v != f), 2):
            incidents.setdefault(prepared['edge_roots'][_edge(t, a, b)], []).append((t, f, a, b))
    def original_cell(location, rank, weight):
        t, f, a, b = location; centre, arms = original[t, f]
        reverse = prepared['edge_orientations'][_edge(t, a, b)]
        local = weight-rank if reverse else rank
        amount = rows[t][a]+rows[t][4+_quad(f, a)]
        if local < amount: return (-1, arms[a]+weight) if reverse else (1, arms[a])
        if local == amount: return 1, centre-rank
        return (1, arms[b]) if reverse else (-1, arms[b]+weight)
    for root, locations in sorted(incidents.items()):
        check(); left, right = sorted(locations); weight = analysed['weights'][root]
        bounds = {0, weight+1, 1, weight}
        for t, f, a, b in (left, right):
            centre = rows[t][a]+rows[t][4+_quad(f, a)]
            if prepared['edge_orientations'][_edge(t, a, b)]: centre = weight-centre
            bounds.update((centre, centre+1))
        events = sorted(x for x in bounds if 0 <= x <= weight+1)
        t, f, a, b = left; u, g, _, _ = right
        endpoints = [prepared['vertex_roots'][4*t+a], prepared['vertex_roots'][4*t+b]]
        if prepared['edge_orientations'][_edge(t, a, b)]: endpoints.reverse()
        for lo, hi in zip(events, events[1:]):
            first = [0, old[endpoints[0]]] if lo == 0 else [1, cut[root][1]-1]
            last = [0, old[endpoints[1]]] if lo == weight else [1, cut[root][0]]
            band('boundary_edge', dict(edge=root, tetrahedron=t, face=f, target_tetrahedron=u, target_face=g),
                 lo, hi, original_cell(left, lo, weight), original_cell(right, lo, weight), [first, last])
    def key(b):
        if b['kind'] == 'normal_arc': return (0, b['tetrahedron'], b['face'], b['corner'], b['side'], b['rank_start'])
        return (1, b['edge'], b['rank_start'])
    bands.sort(key=key); pairs = []; esize = 0
    for b in bands:
        lo, hi = b['rank_start'], b['rank_stop']; a, o = b['source']; c, p = b['target']
        source = sorted((a*lo+o, a*(hi-1)+o)); target = sorted((c*lo+p, c*(hi-1)+p))
        pairs.append(IntervalPairing(*source, *target, a != c))
        b['edge_start'], b['edge_stop'] = esize, esize+hi-lo; esize += hi-lo
    weights = []
    for family in faces:
        check(); t = family['tetrahedron']; chi = 1
        if family['kind'] == 'horizontal':
            col = family['column']
            chi -= sum(tt == t and (col >= 4 or col != f) for tt, f in owned_faces)
            chi += sum(tt == t and (col in (a, b) if col < 4 else col-4 != _quad(a, b))
                       for tt, a, b in edge_owners.values())
            weights.append((family['start'], family['stop'], [chi, 1, 0]))
        else: weights.append((family['start'], family['stop'], [1, 0, 1]))
    for b in bands:
        if b['kind'] == 'boundary_edge':
            lo, hi = b['rank_start'], b['rank_stop']; a, o = b['source']
            values = sorted((a*lo+o, a*(hi-1)+o)); weights.append((values[0], values[1]+1, [-1, 0, 0]))
    seen = set()
    for t, f in prepared['boundary_faces']:
        centre, arms = original[t, f]
        for v in arms:
            root = prepared['vertex_roots'][4*t+v]
            if root not in seen:
                seen.add(root); count = rows[t][v]+rows[t][4+_quad(f, v)]
                p = arms[v] if count else centre; weights.append((p, p+1, [1, 0, 0]))
    chamber_layout = []; chamber_families = []; csize = 0
    for t, row in enumerate(rows):
        q = sum(row[4:]); start = csize; tips = []
        chamber_families.append(dict(kind='chain', tetrahedron=t, start=csize, stop=csize+q+1)); csize += q+1
        for v, count in enumerate(row[:4]):
            tips.append(csize)
            if count: chamber_families.append(dict(kind='triangle_arm', tetrahedron=t, corner=v, start=csize, stop=csize+count))
            csize += count
        chamber_layout.append((start, tips, q, next((j for j in range(3) if row[4+j]), None)))
    carriers = []
    def carrier(lo, hi, slope, offset):
        if lo < hi:
            values = [slope*lo+offset, slope*(hi-1)+offset]
            carriers.append(dict(face_start=lo, face_stop=hi, chamber_start=min(values),
                                 chamber_stop=max(values)+1, reverse=values[0] > values[1]))
    for family in faces:
        check(); t = family['tetrahedron']; lo, hi = family['start'], family['stop']
        chain, tips, q, kind = chamber_layout[t]
        if family['kind'] == 'horizontal':
            col, side = family['column'], family['side']
            if col >= 4: carrier(lo, hi, 1, chain+side-lo)
            elif side == 0: carrier(lo, hi, 1, tips[col]-lo)
            else:
                carrier(lo, hi-1, 1, tips[col]+1-lo)
                endpoint = chain+(q if kind is not None and col not in {0, kind+1} else 0)
                carrier(hi-1, hi, 1, endpoint-(hi-1))
        elif family['kind'] == 'original_centre':
            point = chain+(q if kind is not None and family['face'] in {0, kind+1} else 0)
            carrier(lo, hi, 1, point-lo)
        else:
            v = family['corner']; m = rows[t][v]
            carrier(lo, lo+m, 1, tips[v]-lo)
            if hi > lo+m:
                direction = 1 if v in {0, kind+1} else -1
                first = chain+(0 if direction == 1 else q)
                carrier(lo+m, hi, direction, first-direction*(lo+m))
    carriers.sort(key=lambda c: c['face_start'])
    _reference_cycles(prepared, rows, faces, check)
    geometry = dict(face_points=size, edge_points=esize, vertex_points=vsize, chamber_points=csize,
                    faces=faces, edges=bands, vertices=vertices, chambers=chamber_families, carriers=carriers)
    checked_size, cpairs = _reference_chambers(prepared, rows, check)
    if checked_size != csize: raise ArithmeticError('independent chamber layout disagrees')
    return size, pairs, weights, csize, cpairs, carriers, geometry


def verify_normal_cut_boundary(triangulation, coordinates, certificate, *, max_operations=None, check=lambda: None):
    """Verify source cells, oriented attachments and boundary ownership.

    Invalid source geometry raises the established NormalOrbitError. Malformed
    proofs return False. The replay cap counts all three supplied orbit traces,
    including the repeated boundary trace. External cancellation propagates.
    """
    check()
    if max_operations is not None and (type(max_operations) is not int or max_operations < 0):
        raise ValueError('max_operations must be nonnegative or None')
    keys = {'schema', 'input_sha256', 'geometry', 'summary', 'boundary_transversal', 'boundary_weights', 'pieces'}
    if type(certificate) is not dict or set(certificate) != keys or certificate['schema'] != 'normal-cut-boundary-v1': return False
    traces = []
    for field in ('boundary_transversal', 'boundary_weights', 'pieces'):
        proof = certificate[field]
        if type(proof) is not dict or type(proof.get('orbit_proof')) is not dict: return False
        events = proof['orbit_proof'].get('operations')
        if type(events) is not list: return False
        traces.append(events)
    if max_operations is not None and sum(map(len, traces)) > max_operations: return False
    prepared = _prepare(triangulation, check); analysed = _coordinates(prepared, coordinates, check)
    if certificate['input_sha256'] != _fingerprint(triangulation, analysed, check): return False
    size, pairs, weights, csize, cpairs, carriers, expected = _reference_system(prepared, analysed, check)
    if not certificate_equal(certificate['geometry'], expected): return False
    selector, boundary, pieces = (certificate[k] for k in ('boundary_transversal', 'boundary_weights', 'pieces'))
    if not verify_orbit_transversal_certificate(size, pairs, selector, check=check): return False
    if not verify_weighted_orbit_certificate(size, pairs, weights, boundary, dimension=3, check=check): return False
    joint_pairs = list(pairs)
    for a, b, c, d, sign in cpairs: joint_pairs.append(IntervalPairing(size+a, size+b, size+c, size+d, sign == -1))
    for c in carriers: joint_pairs.append(IntervalPairing(c['face_start'], c['face_stop']-1,
        size+c['chamber_start'], size+c['chamber_stop']-1, c['reverse']))
    joint_weights = [(lo, hi, [v[0], 0, v[1], v[2], 0]) for lo, hi, v in weights]
    for lo, hi in selector['representative_intervals']:
        joint_weights.append((encoded_integer(lo), encoded_integer(hi), [0, 1, 0, 0, 0]))
    joint_weights.append((size, size+csize, [0, 0, 0, 0, 1]))
    if not verify_weighted_orbit_certificate(size+csize, joint_pairs, joint_weights, pieces, dimension=5, check=check): return False
    bprofiles, pprofiles = [], []
    for r in boundary['histogram']:
        check(); chi, horizontal, original = map(encoded_integer, r['weight']); m = encoded_integer(r['orbits'])
        if chi % 2 or chi > 2 or horizontal+original < 1: return False
        bprofiles.append(dict(euler_characteristic=chi, genus=1-chi//2, horizontal_polygons=horizontal,
                              original_polygons=original, multiplicity=m))
    for r in pieces['histogram']:
        check(); chi, b, horizontal, original, chambers = map(encoded_integer, r['weight']); m = encoded_integer(r['orbits'])
        if b < 1 or chi % 2 or chi > 2*b or chambers < 1: return False
        pprofiles.append(dict(boundary_components=b, boundary_euler_characteristic=chi, total_boundary_genus=b-chi//2,
                             horizontal_polygons=horizontal, original_polygons=original, chambers=chambers, multiplicity=m))
    count = sum(r['multiplicity'] for r in bprofiles)
    chi = sum(r['multiplicity']*r['euler_characteristic'] for r in bprofiles)
    if count != sum(r['multiplicity']*r['boundary_components'] for r in pprofiles) or chi != 2*analysed['euler_characteristic']: return False
    if chi != sum(r['multiplicity']*r['boundary_euler_characteristic'] for r in pprofiles): return False
    summary = dict(boundary_components=count, boundary_euler_characteristic=chi,
                   cut_components=encoded_integer(pieces['orbit_proof']['orbit_count']), boundary_profiles=bprofiles, piece_profiles=pprofiles)
    return certificate_equal(certificate['summary'], summary)
