"""Independent rank-event verification of full source-bound normal cut cells.

The verifier rebuilds cell namespaces, signed incidences and chamber carriers
from source ranks. Polygon orientations use the separate midpoint reference.
No cut-cell constructor or producer cycle routine is imported.
"""
from itertools import combinations

from .normal_surface_geometry import _prepare, _coordinates, _edge, _quad, _fingerprint, _permutation_sign
from .normal_cut_boundary_verify import _reference_cycles
from .integer_codec import certificate_equal


def _reference_cells(prepared, analysed, check):
    rows = analysed['rows']; owners = sorted({(t, f) for t, f, _, _, _ in prepared['pairs']} | set(prepared['boundary_faces']))
    signs = {0: 1}; todo = [0]
    while todo:
        check(); t = todo.pop()
        for e in prepared['tetrahedra'][t]:
            if e is not None and e['tetrahedron'] not in signs:
                u = e['tetrahedron']; signs[u] = -signs[t]*_permutation_sign(e['permutation']); todo.append(u)
    old_roots = sorted(set(prepared['vertex_roots']))
    boundary_roots = {prepared['vertex_roots'][4*t+v] for t, f in prepared['boundary_faces'] for v in range(4) if v != f}
    old = {root: i for i, root in enumerate(old_roots)}
    vertices = [dict(kind='original', root=root, start=i, stop=i+1, boundary=root in boundary_roots) for root, i in old.items()]
    vertex_size = len(old); cut = {}
    for root, count in sorted(analysed['weights'].items()):
        check(); cut[root] = [vertex_size, vertex_size+count]
        for side in (0, 1):
            if count: vertices.append(dict(kind='normal', edge=root, side=side, start=vertex_size, stop=vertex_size+count, boundary=True))
            vertex_size += count
    faces, starts, original, face_size = [], [], {}, 0
    for t, row in enumerate(rows):
        check(); local = []
        for col, count in enumerate(row):
            local.append([face_size, face_size+count])
            for side in (0, 1):
                if count: faces.append(dict(kind='horizontal', tetrahedron=t, column=col, side=side,
                                           start=face_size, stop=face_size+count, boundary=True))
                face_size += count
        starts.append(local)
    for t, f in owners:
        centre = face_size; arms = {}; boundary = prepared['tetrahedra'][t][f] is None
        faces.append(dict(kind='original_centre', tetrahedron=t, face=f, start=face_size, stop=face_size+1, boundary=boundary)); face_size += 1
        for v in (x for x in range(4) if x != f):
            count = rows[t][v]+rows[t][4+_quad(f, v)]; arms[v] = face_size
            if count: faces.append(dict(kind='original_arm', tetrahedron=t, face=f, corner=v,
                                       start=face_size, stop=face_size+count, boundary=boundary))
            face_size += count
        original[t, f] = centre, arms
    _reference_cycles(prepared, rows, faces, check)
    by_start = {r['start']: r for r in faces}
    for family in faces:
        for r in family['cycle']:
            if r['kind'] == 'boundary_edge': r['kind'] = 'source_edge'
    def direction(family, f, v, side):
        candidates = [r for r in family['cycle'] if r['kind'] == 'normal_arc' and r['face'] == f and r['corner'] == v and r['side'] == side]
        if len(candidates) != 1: raise ArithmeticError('independent normal-edge orientation is ambiguous')
        return 1 if candidates[0]['forward'] else -1
    def horizontal(t, f, v, side, rank):
        m = rows[t][v]
        if rank < m: return 1, starts[t][v][side], by_start[starts[t][v][side]]
        col = 4+_quad(f, v); q = rows[t][col]; positive = v in {0, col-3}
        slope = 1 if positive else -1; copy = side if positive else 1-side
        index = rank-m if positive else q-1-rank+m
        return slope, starts[t][col][copy]+index-slope*rank, by_start[starts[t][col][copy]]
    def incidence(lo, hi, mapping, sign, **label):
        slope, offset = mapping
        if hi-lo == 1: offset += (slope-1)*lo; slope = 1
        return dict(rank_start=lo, rank_stop=hi, face=[slope, offset], sign=sign, **label)
    edges, edge_size = [], 0
    for t, f in owners:
        check(); entry = prepared['tetrahedra'][t][f]; centre, arms = original[t, f]
        for v in (x for x in range(4) if x != f):
            count = rows[t][v]+rows[t][4+_quad(f, v)]
            if not count: continue
            for side in (0, 1):
                items = []; endpoints = []
                occurrences = [(t, f, v, 1, 'horizontal_source')]
                if entry is not None:
                    u, p = entry['tetrahedron'], entry['permutation']; g, w = p[f], p[v]
                    other = [x for x in range(4) if x not in (v, f)]
                    flip = -1 if p[other[0]] > p[other[1]] else 1
                    occurrences.append((u, g, w, flip, 'horizontal_target'))
                for u, g, w, flip, role in occurrences:
                    bounds = sorted({0, rows[u][w], count})
                    for lo, hi in zip(bounds, bounds[1:]):
                        if lo == hi: continue
                        s, o, family = horizontal(u, g, w, side, lo)
                        items.append(incidence(lo, hi, (s, o), flip*direction(family, g, w, side),
                                               role=role, tetrahedron=u, local_face=g, corner=w))
                bounds = [0, count] if side == 0 else sorted({0, count-1, count})
                for lo, hi in zip(bounds, bounds[1:]):
                    if lo == hi: continue
                    last = side == 1 and lo == count-1
                    point = centre-lo if last else arms[v]+side
                    family = by_start[centre] if last else by_start[arms[v]]
                    items.append(incidence(lo, hi, (1, point), direction(family, f, v, side),
                                           role='original', tetrahedron=t, local_face=f, corner=v))
                for u in (x for x in range(4) if x not in (v, f)):
                    local = _edge(t, v, u); root = prepared['edge_roots'][local]
                    backwards = bool(prepared['edge_orientations'][local]) != (v > u)
                    endpoints.append([-1, cut[root][1-side]+analysed['weights'][root]-1] if backwards else [1, cut[root][side]])
                items.sort(key=lambda r: (r['rank_start'], r['role'], r['tetrahedron'], r['local_face']))
                edges.append(dict(kind='normal_arc', tetrahedron=t, face=f, corner=v, side=side,
                                  start=edge_size, stop=edge_size+count, ends=endpoints, incidences=items, boundary=True)); edge_size += count
    representatives, incident = {}, {}
    for t in range(len(rows)):
        for a, b in combinations(range(4), 2): representatives.setdefault(prepared['edge_roots'][_edge(t, a, b)], (t, a, b))
    for t, f in owners:
        for a, b in combinations((v for v in range(4) if v != f), 2):
            incident.setdefault(prepared['edge_roots'][_edge(t, a, b)], []).append((t, f, a, b))
    coords = [(0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1)]
    for root, count in sorted(analysed['weights'].items()):
        check(); t, a, b = representatives[root]
        endpoint_roots = [prepared['vertex_roots'][4*t+a], prepared['vertex_roots'][4*t+b]]
        if prepared['edge_orientations'][_edge(t, a, b)]: endpoint_roots.reverse()
        pieces = []
        bounds = sorted({0, count+1, *(r for r in (1, count) if 0 < r < count+1)})
        for lo, hi in zip(bounds, bounds[1:]):
            left = [0, old[endpoint_roots[0]]] if lo == 0 else [1, cut[root][1]-1]
            right = [0, old[endpoint_roots[1]]] if lo == count else [1, cut[root][0]]
            pieces.append(dict(rank_start=lo, rank_stop=hi, ends=[left, right]))
        items = []
        for t, f, a, b in sorted(incident[root]):
            centre, arms = original[t, f]; reverse = prepared['edge_orientations'][_edge(t, a, b)]
            amount = rows[t][a]+rows[t][4+_quad(f, a)]
            event = count-amount if reverse else amount
            bounds = sorted({0, event, event+1, count+1})
            ordered = [v for v in range(4) if v != f]
            u = [coords[ordered[1]][i]-coords[ordered[0]][i] for i in range(3)]
            v = [coords[ordered[2]][i]-coords[ordered[0]][i] for i in range(3)]
            cross = [u[1]*v[2]-u[2]*v[1], u[2]*v[0]-u[0]*v[2], u[0]*v[1]-u[1]*v[0]]
            away = [sum(coords[x][i] for x in ordered)-3*coords[f][i] for i in range(3)]
            if sum(cross[i]*away[i] for i in range(3))*signs[t] < 0: ordered.reverse()
            local_sign = 1 if ordered[(ordered.index(a)+1) % 3] == b else -1
            sign = -local_sign if reverse else local_sign
            for lo, hi in zip(bounds, bounds[1:]):
                if lo == hi: continue
                k = count-lo if reverse else lo
                if k < amount: mapping = (-1, arms[a]+count) if reverse else (1, arms[a])
                elif k == amount: mapping = (1, centre-lo)
                else: mapping = (1, arms[b]) if reverse else (-1, arms[b]+count)
                items.append(incidence(lo, hi, mapping, sign, role='original', tetrahedron=t, local_face=f, local_edge=[a, b]))
        items.sort(key=lambda r: (r['tetrahedron'], r['local_face'], r['local_edge'], r['rank_start']))
        edges.append(dict(kind='source_edge', edge=root, start=edge_size, stop=edge_size+count+1,
                          endpoint_pieces=pieces, incidences=items, boundary=root in prepared['boundary_incidence'])); edge_size += count+1
    chambers, c_layout, chamber_size = [], [], 0
    for t, row in enumerate(rows):
        q = sum(row[4:]); chain = chamber_size; tips = []
        chambers.append(dict(kind='chain', tetrahedron=t, start=chamber_size, stop=chamber_size+q+1)); chamber_size += q+1
        for v, count in enumerate(row[:4]):
            tips.append(chamber_size)
            if count: chambers.append(dict(kind='triangle_arm', tetrahedron=t, corner=v, start=chamber_size, stop=chamber_size+count))
            chamber_size += count
        c_layout.append((chain, tips, q, next((j for j in range(3) if row[4+j]), None)))
    uses = []
    def use(lo, hi, mapping, sign, **label):
        if lo >= hi: return
        s, o = mapping
        if hi-lo == 1: o += (s-1)*lo; s = 1
        uses.append(dict(face_start=lo, face_stop=hi, chamber=[s, o], sign=sign, **label))
    for family in faces:
        check(); t = family['tetrahedron']; lo, hi = family['start'], family['stop']
        if family['kind'] == 'horizontal':
            col, side = family['column'], family['side']; chain, tips, q, kind = c_layout[t]
            label = dict(kind='horizontal', tetrahedron=t, column=col, side=side)
            if col >= 4: use(lo, hi, (1, chain+side-lo), 1, **label)
            elif side == 0: use(lo, hi, (1, tips[col]-lo), 1, **label)
            else:
                use(lo, hi-1, (1, tips[col]+1-lo), 1, **label)
                point = chain+(q if kind is not None and col not in {0, kind+1} else 0)
                use(hi-1, hi, (1, point-(hi-1)), 1, **label)
            continue
        f = family['face']; entry = prepared['tetrahedra'][t][f]
        occurrences = [(t, f, None, 1)]
        if entry is not None: occurrences.append((entry['tetrahedron'], entry['permutation'][f], entry['permutation'], -1))
        for u, g, p, sign in occurrences:
            chain, tips, q, kind = c_layout[u]
            if family['kind'] == 'original_centre':
                point = chain+(q if kind is not None and g in {0, kind+1} else 0)
                use(lo, hi, (1, point-lo), sign, kind='original', tetrahedron=u, face=g, corner=-1)
            else:
                v = family['corner']; w = p[v] if p is not None else v; m = rows[u][w]
                use(lo, lo+m, (1, tips[w]-lo), sign, kind='original', tetrahedron=u, face=g, corner=w)
                if lo+m < hi:
                    slope = 1 if w in {0, kind+1} else -1
                    point = chain+(0 if slope == 1 else q)
                    use(lo+m, hi, (slope, point-slope*(lo+m)), sign, kind='original', tetrahedron=u, face=g, corner=w)
    uses.sort(key=lambda r: (r['face_start'], -r['sign'], r['tetrahedron'], r.get('face', -1)))
    return dict(vertex_points=vertex_size, edge_points=edge_size, face_points=face_size, chamber_points=chamber_size,
                vertices=vertices, edges=edges, faces=faces, chambers=chambers, face_incidence=uses,
                source={'tetrahedra': [[None if r is None else dict(tetrahedron=r['tetrahedron'], permutation=r['permutation'].copy())
                                        for r in tetrahedron] for tetrahedron in prepared['tetrahedra']]},
                coordinates=[row.copy() for row in rows])


def verify_normal_cut_cell_complex(triangulation, coordinates, certificate, *, check=lambda: None):
    """Verify every raw cut cell and attaching family against its source.

    Invalid source geometry raises NormalOrbitError; malformed proofs return
    False. External cancellation propagates. This does not test irreducibility
    or whether a sphere-bounded component is a ball.
    """
    check()
    if type(certificate) is not dict or set(certificate) != {'schema', 'input_sha256', 'geometry', 'summary'} or certificate['schema'] != 'normal-cut-cells-v1': return False
    prepared = _prepare(triangulation, check); analysed = _coordinates(prepared, coordinates, check)
    if certificate['input_sha256'] != _fingerprint(triangulation, analysed, check): return False
    expected = _reference_cells(prepared, analysed, check)
    if not certificate_equal(certificate['geometry'], expected): return False
    boundary = {kind: sum(r['stop']-r['start'] for r in expected[kind] if r['boundary']) for kind in ('vertices', 'edges', 'faces')}
    chi = expected['vertex_points']-expected['edge_points']+expected['face_points']-expected['chamber_points']
    original = prepared['vertices']-prepared['edges']+len(prepared['pairs'])+len(prepared['boundary_faces'])-len(prepared['tetrahedra'])
    if chi != original+analysed['euler_characteristic'] or boundary['vertices']-boundary['edges']+boundary['faces'] != 2*chi: return False
    summary = dict(euler_characteristic=chi, boundary_euler_characteristic=2*chi,
                   boundary_vertices=boundary['vertices'], boundary_edges=boundary['edges'], boundary_faces=boundary['faces'])
    check(); return certificate_equal(certificate['summary'], summary)
