"""Full normal cut manifolds as source-labelled binary CW cell families.

This retains all interior cells and oriented chamber attachments. It is a
compressed raw cut, not a bounded core, a parallelity collapse, a hierarchy,
or a knot verdict. No represented cell family is expanded.
"""
from itertools import combinations

from .normal_surface_geometry import _prepare, _coordinates, _edge, _quad, _fingerprint, _permutation_sign
from .normal_cut_boundary import _cycle_recipes


def _orientations(prepared, check):
    signs = {0: 1}; pending = [0]
    for t in pending:
        check()
        for record in prepared['tetrahedra'][t]:
            if record is not None and record['tetrahedron'] not in signs:
                u = record['tetrahedron']; signs[u] = -signs[t]*_permutation_sign(record['permutation'])
                pending.append(u)
    return signs


def _cut_cells(prepared, analysed, check):
    rows = analysed['rows']; signs = _orientations(prepared, check)
    owned = sorted(set(prepared['boundary_faces']) | {(t, f) for t, f, _, _, _ in prepared['pairs']})
    boundary_roots = {prepared['vertex_roots'][4*t+v] for t, f in prepared['boundary_faces'] for v in range(4) if v != f}
    vertices, old_ids = [], {}
    for root in sorted(set(prepared['vertex_roots'])):
        index = len(old_ids); old_ids[root] = index
        vertices.append(dict(kind='original', root=root, start=index, stop=index+1, boundary=root in boundary_roots))
    vsize = len(old_ids); cut_vertices = {}
    for root, count in sorted(analysed['weights'].items()):
        check(); cut_vertices[root] = [vsize, vsize+count]
        for side in (0, 1):
            if count: vertices.append(dict(kind='normal', edge=root, side=side, start=vsize, stop=vsize+count, boundary=True))
            vsize += count

    faces, horizontal, original, fsize = [], [], {}, 0
    for t, row in enumerate(rows):
        check(); local = []
        for column, count in enumerate(row):
            sides = []
            for side in (0, 1):
                sides.append(fsize)
                if count: faces.append(dict(kind='horizontal', tetrahedron=t, column=column, side=side,
                                           start=fsize, stop=fsize+count, boundary=True))
                fsize += count
            local.append(sides)
        horizontal.append(local)
    for t, f in owned:
        check(); centre = fsize; arms = {}; boundary = prepared['tetrahedra'][t][f] is None
        faces.append(dict(kind='original_centre', tetrahedron=t, face=f, start=fsize, stop=fsize+1, boundary=boundary)); fsize += 1
        for v in (x for x in range(4) if x != f):
            count = rows[t][v]+rows[t][4+_quad(f, v)]; arms[v] = fsize
            if count: faces.append(dict(kind='original_arm', tetrahedron=t, face=f, corner=v,
                                       start=fsize, stop=fsize+count, boundary=boundary))
            fsize += count
        original[t, f] = centre, arms
    _cycle_recipes(prepared, rows, faces, check)
    face_by_start = {f['start']: f for f in faces}
    for family in faces:
        for recipe in family['cycle']:
            if recipe['kind'] == 'boundary_edge': recipe['kind'] = 'source_edge'

    def arc(t, f, v, side):
        m = rows[t][v]; result = [(0, m, 1, horizontal[t][v][side], v, side)] if m else []
        col = 4+_quad(f, v); q = rows[t][col]
        if q:
            positive = v in (0, col-3); s = 1 if positive else -1
            copy = side if positive else 1-side
            result.append((m, m+q, s, horizontal[t][col][copy]-s*m+(0 if positive else q-1), col, copy))
        return result
    def normal_direction(family, f, v, side):
        recipe = next(r for r in family['cycle'] if r['kind'] == 'normal_arc' and
                      r['face'] == f and r['corner'] == v and r['side'] == side)
        return 1 if recipe['forward'] else -1
    def arc_ends(t, f, v, side):
        result = []
        for u in (x for x in range(4) if x not in (v, f)):
            local = _edge(t, v, u); root = prepared['edge_roots'][local]
            backwards = prepared['edge_orientations'][local] ^ int(v > u)
            base = cut_vertices[root][backwards ^ side]
            result.append([-1, base+analysed['weights'][root]-1] if backwards else [1, base])
        return result
    def add_incidence(target, lo, hi, s, offset, sign, **label):
        if lo < hi:
            if hi-lo == 1: offset = s*lo+offset-lo; s = 1
            target.append(dict(rank_start=lo, rank_stop=hi, face=[s, offset], sign=sign, **label))

    edges, esize = [], 0
    for t, f in owned:
        check(); entry = prepared['tetrahedra'][t][f]; centre, arms = original[t, f]
        for v in (x for x in range(4) if x != f):
            count = rows[t][v]+rows[t][4+_quad(f, v)]
            if not count: continue
            for side in (0, 1):
                incidences = []
                for lo, hi, s, offset, col, copy in arc(t, f, v, side):
                    family = face_by_start[horizontal[t][col][copy]]
                    add_incidence(incidences, lo, hi, s, offset, normal_direction(family, f, v, side),
                                  role='horizontal_source', tetrahedron=t, local_face=f, corner=v)
                if entry is not None:
                    u, p = entry['tetrahedron'], entry['permutation']; g, w = p[f], p[v]
                    others = [x for x in range(4) if x not in (f, v)]
                    flip = -1 if p[others[0]] > p[others[1]] else 1
                    for lo, hi, s, offset, col, copy in arc(u, g, w, side):
                        family = face_by_start[horizontal[u][col][copy]]
                        add_incidence(incidences, lo, hi, s, offset, flip*normal_direction(family, g, w, side),
                                      role='horizontal_target', tetrahedron=u, local_face=g, corner=w)
                family = face_by_start[arms[v]]
                if side == 0:
                    add_incidence(incidences, 0, count, 1, arms[v], normal_direction(family, f, v, side),
                                  role='original', tetrahedron=t, local_face=f, corner=v)
                else:
                    add_incidence(incidences, 0, count-1, 1, arms[v]+1, normal_direction(family, f, v, side),
                                  role='original', tetrahedron=t, local_face=f, corner=v)
                    central = face_by_start[centre]
                    add_incidence(incidences, count-1, count, 1, centre-(count-1), normal_direction(central, f, v, side),
                                  role='original', tetrahedron=t, local_face=f, corner=v)
                incidences.sort(key=lambda r: (r['rank_start'], r['role'], r['tetrahedron'], r['local_face']))
                edges.append(dict(kind='normal_arc', tetrahedron=t, face=f, corner=v, side=side,
                                  start=esize, stop=esize+count, ends=arc_ends(t, f, v, side),
                                  incidences=incidences, boundary=True)); esize += count

    owners, occurrences = {}, {}
    for t in range(len(rows)):
        for a, b in combinations(range(4), 2): owners.setdefault(prepared['edge_roots'][_edge(t, a, b)], (t, a, b))
    for t, f in owned:
        for a, b in combinations((v for v in range(4) if v != f), 2):
            occurrences.setdefault(prepared['edge_roots'][_edge(t, a, b)], []).append((t, f, a, b))
    for root, count in sorted(analysed['weights'].items()):
        check(); t, a, b = owners[root]; parity = prepared['edge_orientations'][_edge(t, a, b)]
        roots = [prepared['vertex_roots'][4*t+a], prepared['vertex_roots'][4*t+b]]
        if parity: roots.reverse()
        endpoint_pieces = []
        events = sorted({0, count+1, *(x for x in (1, count) if 0 < x < count+1)})
        for lo, hi in zip(events, events[1:]):
            first = [0, old_ids[roots[0]]] if lo == 0 else [1, cut_vertices[root][1]-1]
            last = [0, old_ids[roots[1]]] if lo == count else [1, cut_vertices[root][0]]
            endpoint_pieces.append(dict(rank_start=lo, rank_stop=hi, ends=[first, last]))
        incidences = []
        for t, f, a, b in sorted(occurrences[root]):
            centre, arms = original[t, f]
            left = rows[t][a]+rows[t][4+_quad(f, a)]
            parts = [(0, left, 1, arms[a]), (left, left+1, 1, centre-left),
                     (left+1, count+1, -1, arms[b]+count)]
            orientation = [v for v in range(4) if v != f]
            if signs[t]*(-1 if f % 2 else 1) < 0: orientation.reverse()
            local_sign = 1 if (a, b) in list(zip(orientation, orientation[1:]+orientation[:1])) else -1
            reverse = prepared['edge_orientations'][_edge(t, a, b)]
            for lo, hi, s, offset in parts:
                if reverse: lo, hi, s, offset = count-hi+1, count-lo+1, -s, offset+s*count
                add_incidence(incidences, lo, hi, s, offset, -local_sign if reverse else local_sign,
                              role='original', tetrahedron=t, local_face=f, local_edge=[a, b])
        incidences.sort(key=lambda r: (r['tetrahedron'], r['local_face'], r['local_edge'], r['rank_start']))
        edges.append(dict(kind='source_edge', edge=root, start=esize, stop=esize+count+1,
                          endpoint_pieces=endpoint_pieces, incidences=incidences,
                          boundary=root in prepared['boundary_incidence'])); esize += count+1

    chambers, layout, csize = [], [], 0
    for t, row in enumerate(rows):
        check(); q = sum(row[4:]); kind = next((j for j in range(3) if row[4+j]), None)
        chain = csize; tips = []
        chambers.append(dict(kind='chain', tetrahedron=t, start=csize, stop=csize+q+1)); csize += q+1
        for v, count in enumerate(row[:4]):
            tips.append(csize)
            if count: chambers.append(dict(kind='triangle_arm', tetrahedron=t, corner=v, start=csize, stop=csize+count))
            csize += count
        layout.append((chain, tips, q, kind))
    face_incidence = []
    def attach(lo, hi, s, offset, sign, **label):
        if lo < hi:
            if hi-lo == 1: offset = s*lo+offset-lo; s = 1
            face_incidence.append(dict(face_start=lo, face_stop=hi, chamber=[s, offset], sign=sign, **label))
    for t, row in enumerate(rows):
        chain, tips, q, kind = layout[t]
        for col, count in enumerate(row):
            for side in (0, 1):
                start = horizontal[t][col][side]
                label = dict(kind='horizontal', tetrahedron=t, column=col, side=side)
                if col >= 4: attach(start, start+count, 1, chain+side-start, 1, **label)
                elif side == 0: attach(start, start+count, 1, tips[col]-start, 1, **label)
                else:
                    attach(start, start+count-1, 1, tips[col]+1-start, 1, **label)
                    if count:
                        end = chain+(q if kind is not None and col not in (0, kind+1) else 0)
                        attach(start+count-1, start+count, 1, end-(start+count-1), 1, **label)
    for t, f in owned:
        centre, arms = original[t, f]; entry = prepared['tetrahedra'][t][f]
        local = [(t, f, None, 1)]
        if entry is not None: local.append((entry['tetrahedron'], entry['permutation'][f], entry['permutation'], -1))
        for u, g, p, sign in local:
            chain, tips, q, kind = layout[u]
            point = chain+(q if kind is not None and g in (0, kind+1) else 0)
            attach(centre, centre+1, 1, point-centre, sign, kind='original', tetrahedron=u, face=g, corner=-1)
            for v, start in arms.items():
                w = v if p is None else p[v]; m = rows[u][w]
                count = rows[t][v]+rows[t][4+_quad(f, v)]
                attach(start, start+m, 1, tips[w]-start, sign, kind='original', tetrahedron=u, face=g, corner=w)
                if count > m:
                    slope = 1 if w in (0, kind+1) else -1
                    point = chain+(0 if slope == 1 else q)
                    attach(start+m, start+count, slope, point-slope*(start+m), sign,
                           kind='original', tetrahedron=u, face=g, corner=w)
    face_incidence.sort(key=lambda r: (r['face_start'], -r['sign'], r['tetrahedron'], r.get('face', -1)))
    geometry = dict(vertex_points=vsize, edge_points=esize, face_points=fsize, chamber_points=csize,
                    vertices=vertices, edges=edges, faces=faces, chambers=chambers, face_incidence=face_incidence,
                    source={'tetrahedra': [[None if r is None else dict(tetrahedron=r['tetrahedron'], permutation=r['permutation'].copy())
                                            for r in tetrahedron] for tetrahedron in prepared['tetrahedra']]},
                    coordinates=[row.copy() for row in rows])
    return geometry


def _summary(prepared, analysed, geometry):
    boundary = {kind: sum(f['stop']-f['start'] for f in geometry[kind] if f['boundary']) for kind in ('vertices', 'edges', 'faces')}
    chi = geometry['vertex_points']-geometry['edge_points']+geometry['face_points']-geometry['chamber_points']
    source_chi = prepared['vertices']-prepared['edges']+len(prepared['pairs'])+len(prepared['boundary_faces'])-len(prepared['tetrahedra'])
    if chi != source_chi+analysed['euler_characteristic']:
        raise ArithmeticError('cut Euler characteristic disagrees with the source')
    if boundary['vertices']-boundary['edges']+boundary['faces'] != 2*chi:
        raise ArithmeticError('boundary Euler characteristic disagrees with the cut')
    return dict(euler_characteristic=chi, boundary_euler_characteristic=2*chi,
                boundary_vertices=boundary['vertices'], boundary_edges=boundary['edges'], boundary_faces=boundary['faces'])


def normal_cut_cell_complex(triangulation, coordinates, *, record_certificate=False, check=lambda: None):
    """Construct the actual cut manifold as binary cells and oriented maps.

    No normal multiplicity is divided out. This deterministic source operation
    starts no orbit search. It does not remove parallelity or certify a ball.
    """
    check()
    if type(record_certificate) is not bool: raise ValueError('record_certificate must be bool')
    prepared = _prepare(triangulation, check); analysed = _coordinates(prepared, coordinates, check)
    geometry = _cut_cells(prepared, analysed, check); summary = _summary(prepared, analysed, geometry)
    result = dict(status='COMPLETE', geometry=geometry, summary=summary,
                  trust='full source-labelled raw cut CW cells; no bounded-core, ball or knot verdict')
    if record_certificate:
        result['certificate'] = dict(schema='normal-cut-cells-v1', input_sha256=_fingerprint(triangulation, analysed, check),
                                     geometry=geometry, summary=summary)
    check(); return result
