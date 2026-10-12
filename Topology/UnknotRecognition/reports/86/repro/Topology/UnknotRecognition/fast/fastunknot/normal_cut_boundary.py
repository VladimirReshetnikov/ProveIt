"""Source-labelled binary cell structure of a normal cut boundary.

The closed boundary of the cut manifold includes two local sides of every
normal disc and the cut original boundary faces. Edge and vertex families
are retained, including one-sided surfaces and self-identifications.
This does not construct the interior core or a complete hierarchy.
"""
from itertools import combinations

from .interval_orbits import IntervalPairing
from .normal_surface_geometry import _prepare, _coordinates, _quad, _edge, _fingerprint, _permutation_sign
from .normal_cut_complement import _chamber_system
from .orbit_transversal import orbit_transversal
from .weighted_orbits import weighted_orbit_histogram, weighted_histogram_from_orbit_certificate


def _cycle_recipes(prepared, rows, families, check):
    """Constant-length cyclic attaching recipes, with affine edge ranks."""
    orientations = {0: 1}; pending = [0]
    for t in pending:
        check()
        for record in prepared['tetrahedra'][t]:
            if record is not None and record['tetrahedron'] not in orientations:
                u = record['tetrahedron']
                orientations[u] = -_permutation_sign(record['permutation'])*orientations[t]
                pending.append(u)

    def gap(t, a, b, s, offset, forward=True):
        local = _edge(t, a, b); root = prepared['edge_roots'][local]
        backwards = prepared['edge_orientations'][local] ^ int(a > b)
        if backwards:
            s, offset = -s, (rows[t][a]+rows[t][b]+sum(rows[t][4:])-rows[t][4+_quad(a, b)])-offset
        return dict(kind='boundary_edge', edge=root, rank=[s, offset], forward=bool(forward ^ backwards))

    def normal(f, v, rank, side, a, b, minimum=0):
        return dict(kind='normal_arc', face=f, corner=v, rank=rank, side=side,
                    forward=a < b, minimum_rank=minimum)

    for family in families:
        check(); t = family['tetrahedron']; cycle = []
        if family['kind'] == 'horizontal':
            column, side = family['column'], family['side']
            if column < 4:
                v = column; others = [x for x in range(4) if x != v]
                points = [(v, x) for x in others]
                flip = orientations[t]*(-1 if (v+side) % 2 else 1)
            else:
                j = column-4; a, b = 0, j+1
                c, d = [x for x in range(4) if x not in (a, b)]
                points = [(a, c), (a, d), (b, d), (b, c)]
                flip = orientations[t]*(-1 if (j+side) % 2 else 1)
            if flip < 0:
                points.reverse()
            for left, right in zip(points, points[1:]+points[:1]):
                v = next(x for x in left if x in right)
                a = next(x for x in left if x != v); b = next(x for x in right if x != v)
                f = next(x for x in range(4) if x not in (v, a, b))
                if column < 4:
                    rank, inward = [1, 0], side
                else:
                    positive = v in (0, column-3)
                    rank = [1, rows[t][v]] if positive else [-1, rows[t][v]+rows[t][column]-1]
                    inward = side if positive else 1-side
                cycle.append(normal(f, v, rank, inward, a, b))
        else:
            f = family['face']; points = [x for x in range(4) if x != f]
            if orientations[t]*(-1 if f % 2 else 1) < 0:
                points.reverse()
            if family['kind'] == 'original_centre':
                for i, a in enumerate(points):
                    b, c = points[(i+1) % 3], points[(i+2) % 3]
                    amount = rows[t][a]+rows[t][4+_quad(f, a)]
                    cycle.append(gap(t, a, b, 0, amount))
                    count = rows[t][b]+rows[t][4+_quad(f, b)]
                    if count:
                        cycle.append(normal(f, b, [0, count-1], 1, a, c))
            else:
                v = family['corner']; index = points.index(v)
                a, b = points[(index+1) % 3], points[(index+2) % 3]
                cycle = [gap(t, v, a, 1, 0), normal(f, v, [1, 0], 0, a, b),
                         gap(t, v, b, 1, 0, False), normal(f, v, [1, -1], 1, b, a, 1)]
        def key(recipe):
            if recipe['kind'] == 'normal_arc':
                return (0, recipe['face'], recipe['corner'], *recipe['rank'], recipe['side'],
                        int(recipe['forward']), recipe['minimum_rank'])
            return (1, recipe['edge'], *recipe['rank'], int(recipe['forward']))
        family['cycle'] = min((cycle[i:]+cycle[:i] for i in range(len(cycle))),
                              key=lambda value: tuple(key(r) for r in value))


def _boundary_system(prepared, analysed, check):
    rows = analysed['rows']
    horizontal, original, faces, face_size = [], {}, [], 0
    for t, row in enumerate(rows):
        check()
        blocks = []
        for column, count in enumerate(row):
            sides = []
            for side in (0, 1):
                sides.append(face_size)
                if count:
                    faces.append(dict(kind='horizontal', tetrahedron=t, column=column,
                                      side=side, start=face_size, stop=face_size+count))
                face_size += count
            blocks.append(sides)
        horizontal.append(blocks)
    for t, f in prepared['boundary_faces']:
        check()
        centre = face_size
        faces.append(dict(kind='original_centre', tetrahedron=t, face=f,
                          start=face_size, stop=face_size+1))
        face_size += 1
        arms = {}
        for v in range(4):
            if v == f:
                continue
            count = rows[t][v]+rows[t][4+_quad(f, v)]
            arms[v] = face_size
            if count:
                faces.append(dict(kind='original_arm', tetrahedron=t, face=f, corner=v,
                                  start=face_size, stop=face_size+count))
            face_size += count
        original[t, f] = (centre, arms)

    # Both sides of an edge intersection are distinct cut vertices. Old
    # boundary vertices remain single vertices, even at self-glued corners.
    old_roots = sorted({prepared['vertex_roots'][4*t+v]
                        for t, f in prepared['boundary_faces'] for v in range(4) if v != f})
    old_ids = {root: i for i, root in enumerate(old_roots)}
    vertices = [dict(kind='original', root=root, start=i, stop=i+1) for root, i in old_ids.items()]
    vertex_size = len(old_roots)
    cut_vertices = {}
    for root, count in sorted(analysed['weights'].items()):
        check()
        starts = []
        for side in (0, 1):
            starts.append(vertex_size)
            if count:
                vertices.append(dict(kind='normal', edge=root, side=side,
                                     start=vertex_size, stop=vertex_size+count))
            vertex_size += count
        cut_vertices[root] = starts

    def arc(t, f, v, side):
        """Map arc rank from its corner to the incident horizontal face."""
        m = rows[t][v]
        parts = [(0, m, 1, horizontal[t][v][side])] if m else []
        column = 4+_quad(f, v)
        q = rows[t][column]
        if q:
            positive = v in (0, column-3)
            s = 1 if positive else -1
            disk_side = side if positive else 1-side
            offset = horizontal[t][column][disk_side]-s*m+(0 if positive else q-1)
            parts.append((m, m+q, s, offset))
        return parts

    def arc_ends(t, f, v, side):
        result = []
        for u in (x for x in range(4) if x not in (f, v)):
            local = _edge(t, v, u)
            root = prepared['edge_roots'][local]
            backwards = prepared['edge_orientations'][local] ^ int(v > u)
            count = analysed['weights'][root]
            base = cut_vertices[root][backwards ^ side]
            result.append([-1, base+count-1] if backwards else [1, base])
        return result

    bands = []
    def emit(kind, location, lo, hi, sa, oa, sb, ob, ends):
        if lo < hi:
            check()
            if hi-lo == 1:
                oa, ob = sa*lo+oa-lo, sb*lo+ob-lo
                sa = sb = 1
            bands.append(dict(kind=kind, **location, rank_start=lo, rank_stop=hi,
                              source=[sa, oa], target=[sb, ob], ends=ends))

    for t, f, u, g, p in prepared['pairs']:
        for v in range(4):
            if v == f:
                continue
            for side in (0, 1):
                for a, b, sa, oa in arc(t, f, v, side):
                    for c, d, sb, ob in arc(u, g, p[v], side):
                        lo, hi = max(a, c), min(b, d)
                        others = [x for x in range(4) if x not in (f, v)]
                        location = dict(tetrahedron=t, face=f, target_tetrahedron=u, target_face=g,
                                        corner=v, side=side, target_endpoint_reversed=p[others[0]] > p[others[1]])
                        emit('normal_arc', location, lo, hi, sa, oa, sb, ob, arc_ends(t, f, v, side))
    for t, f in prepared['boundary_faces']:
        centre, arms = original[t, f]
        for v in arms:
            count = rows[t][v]+rows[t][4+_quad(f, v)]
            for side in (0, 1):
                location = dict(tetrahedron=t, face=f, target_tetrahedron=t, target_face=f,
                                corner=v, side=side, target_endpoint_reversed=False)
                for lo, hi, s, offset in arc(t, f, v, side):
                    if side == 0:
                        emit('normal_arc', location, lo, hi, s, offset, 1, arms[v], arc_ends(t, f, v, side))
                    else:
                        stop = min(hi, count-1)
                        emit('normal_arc', location, lo, stop, s, offset, 1, arms[v]+1, arc_ends(t, f, v, side))
                        if lo <= count-1 < hi:
                            emit('normal_arc', location, count-1, count, s, offset, 1,
                                 centre-(count-1), arc_ends(t, f, v, side))

    occurrences = {}
    local_edges = tuple(combinations(range(4), 2))
    edge_owners = {}
    for t in range(len(rows)):
        for a, b in local_edges:
            local = _edge(t, a, b)
            edge_owners.setdefault(prepared['edge_roots'][local], (t, a, b))
    for t, f in prepared['boundary_faces']:
        for a, b in combinations((v for v in range(4) if v != f), 2):
            root = prepared['edge_roots'][_edge(t, a, b)]
            occurrences.setdefault(root, []).append((t, f, a, b))

    def edge_parts(t, f, a, b):
        centre, arms = original[t, f]
        left = rows[t][a]+rows[t][4+_quad(f, a)]
        right = rows[t][b]+rows[t][4+_quad(f, b)]
        count = left+right
        parts = [(0, left, 1, arms[a]), (left, left+1, 1, centre-left),
                 (left+1, count+1, -1, arms[b]+count)]
        reverse = prepared['edge_orientations'][_edge(t, a, b)]
        return [(count-hi+1, count-lo+1, -s, o+s*count) if reverse else (lo, hi, s, o)
                for lo, hi, s, o in parts if lo < hi]

    for root, incident in sorted(occurrences.items()):
        check()
        if len(incident) != 2:
            raise ArithmeticError('boundary edge has wrong incidence')
        (t, f, a, b), (u, g, c, d) = sorted(incident)
        count = analysed['weights'][root]
        parity = prepared['edge_orientations'][_edge(t, a, b)]
        end_roots = [prepared['vertex_roots'][4*t+a], prepared['vertex_roots'][4*t+b]]
        if parity:
            end_roots.reverse()
        for lo, hi, sa, oa in edge_parts(t, f, a, b):
            for low, stop, sb, ob in edge_parts(u, g, c, d):
                start, end = max(lo, low), min(hi, stop)
                if start >= end:
                    continue
                cuts = sorted({start, end, *(x for x in (1, count) if start < x < end)})
                for first, last in zip(cuts, cuts[1:]):
                    if first == last:
                        continue
                    left = [0, old_ids[end_roots[0]]] if first == 0 else [1, cut_vertices[root][1]-1]
                    right = [0, old_ids[end_roots[1]]] if first == count else [1, cut_vertices[root][0]]
                    emit('boundary_edge', dict(edge=root, tetrahedron=t, face=f,
                         target_tetrahedron=u, target_face=g), first, last, sa, oa, sb, ob, [left, right])

    def band_key(b):
        if b['kind'] == 'normal_arc':
            return (0, b['tetrahedron'], b['face'], b['corner'], b['side'], b['rank_start'])
        return (1, b['edge'], b['rank_start'])
    bands.sort(key=band_key)
    pairings, weights, edge_size = [], [], 0
    def indicator(lo, hi, value):
        if lo < hi:
            weights.append((lo, hi, value))
    for family in faces:
        indicator(family['start'], family['stop'], [1, int(family['kind'] == 'horizontal'),
                                                   int(family['kind'] != 'horizontal')])
    for band in bands:
        lo, hi = band['rank_start'], band['rank_stop']
        s, o = band['source']; r, p = band['target']
        left = sorted((s*lo+o, s*(hi-1)+o)); right = sorted((r*lo+p, r*(hi-1)+p))
        pairings.append(IntervalPairing(*left, *right, s != r))
        indicator(left[0], left[1]+1, [-1, 0, 0])
        band['edge_start'], band['edge_stop'] = edge_size, edge_size+hi-lo
        edge_size += hi-lo
    for root, (t, a, b) in sorted(edge_owners.items()):
        check()
        for column, count in enumerate(rows[t]):
            crosses = column in (a, b) if column < 4 else column-4 != _quad(a, b)
            if crosses:
                for side in (0, 1):
                    indicator(horizontal[t][column][side], horizontal[t][column][side]+count, [1, 0, 0])
    owned_vertices = set()
    for t, f in prepared['boundary_faces']:
        centre, arms = original[t, f]
        for v in arms:
            root = prepared['vertex_roots'][4*t+v]
            if root not in owned_vertices:
                owned_vertices.add(root)
                count = rows[t][v]+rows[t][4+_quad(f, v)]
                point = arms[v] if count else centre
                indicator(point, point+1, [1, 0, 0])

    # Locate every boundary polygon in its original cut chamber. Carriers
    # join the boundary system to the established full chamber graph.
    chambers, chamber_size, chamber_families = [], 0, []
    for t, row in enumerate(rows):
        q = sum(row[4:]); kind = next((j for j in range(3) if row[4+j]), None)
        chain = chamber_size
        chamber_families.append(dict(kind='chain', tetrahedron=t, start=chain, stop=chain+q+1))
        chamber_size += q+1; tips = []
        for v, count in enumerate(row[:4]):
            tips.append(chamber_size)
            if count:
                chamber_families.append(dict(kind='triangle_arm', tetrahedron=t, corner=v,
                                             start=chamber_size, stop=chamber_size+count))
            chamber_size += count
        chambers.append((chain, tips, q, kind))
    carriers = []
    def carry(lo, hi, first, last):
        if lo < hi:
            carriers.append(dict(face_start=lo, face_stop=hi, chamber_start=min(first, last),
                                 chamber_stop=max(first, last)+1, reverse=first > last))
    for t, row in enumerate(rows):
        check(); chain, tips, q, kind = chambers[t]
        for v, count in enumerate(row[:4]):
            carry(horizontal[t][v][0], horizontal[t][v][0]+count, tips[v], tips[v]+count-1)
            start = horizontal[t][v][1]
            if count > 1:
                carry(start, start+count-1, tips[v]+1, tips[v]+count-1)
            if count:
                endpoint = chain+(q if kind is not None and v not in (0, kind+1) else 0)
                carry(start+count-1, start+count, endpoint, endpoint)
        if kind is not None:
            for side in (0, 1):
                start = horizontal[t][4+kind][side]
                carry(start, start+q, chain+side, chain+side+q-1)
    for t, f in prepared['boundary_faces']:
        centre, arms = original[t, f]; chain, tips, q, kind = chambers[t]
        point = chain+(q if kind is not None and f in (0, kind+1) else 0)
        carry(centre, centre+1, point, point)
        for v, start in arms.items():
            m = rows[t][v]
            carry(start, start+m, tips[v], tips[v]+m-1)
            if kind is not None and _quad(f, v) == kind:
                s = 1 if v in (0, kind+1) else -1
                first = chain+(0 if s == 1 else q)
                carry(start+m, start+m+q, first, first+s*(q-1))
    carriers.sort(key=lambda c: c['face_start'])
    covered = 0
    for carrier in carriers:
        if carrier['face_start'] != covered:
            raise ArithmeticError('boundary carrier partition failed')
        covered = carrier['face_stop']
    if covered != face_size:
        raise ArithmeticError('boundary carrier partition incomplete')
    csize, cpairs = _chamber_system(prepared, rows, check)
    if csize != chamber_size:
        raise ArithmeticError('cut chamber layout disagrees')
    _cycle_recipes(prepared, rows, faces, check)
    geometry = dict(face_points=face_size, edge_points=edge_size, vertex_points=vertex_size,
                    chamber_points=chamber_size, faces=faces, edges=bands, vertices=vertices,
                    chambers=chamber_families, carriers=carriers)
    check()
    return face_size, pairings, weights, chamber_size, cpairs, carriers, geometry


def _boundary_summary(histogram, check):
    profiles = []
    for row in histogram:
        check(); chi, horizontal, original = row['weight']
        if chi % 2 or chi > 2 or horizontal+original < 1:
            raise ArithmeticError('invalid closed orientable boundary profile')
        profiles.append(dict(euler_characteristic=chi, genus=1-chi//2,
                             horizontal_polygons=horizontal, original_polygons=original,
                             multiplicity=row['orbits']))
    return profiles


def _piece_summary(histogram, check):
    profiles = []
    for row in histogram:
        check(); chi, boundary, horizontal, original, chambers = row['weight']
        if boundary < 1 or chi % 2 or chi > 2*boundary or chambers < 1:
            raise ArithmeticError('invalid cut-piece boundary profile')
        profiles.append(dict(boundary_components=boundary, boundary_euler_characteristic=chi,
                             total_boundary_genus=boundary-chi//2, horizontal_polygons=horizontal,
                             original_polygons=original, chambers=chambers, multiplicity=row['orbits']))
    return profiles


def normal_cut_boundary(triangulation, coordinates, *, max_cycles=None,
                        record_certificate=False, check=lambda: None):
    """Recover compressed cut-boundary cells and cut-piece boundary profiles.

    Caps share one discovery allowance across the boundary and joint queries.
    Incomplete work returns no geometry, summary or certificate. A sphere
    boundary profile does not assert that a cut piece is a ball.
    """
    check()
    if type(record_certificate) is not bool:
        raise ValueError('record_certificate must be bool')
    if max_cycles is not None and (type(max_cycles) is not int or max_cycles < 0):
        raise ValueError('max_cycles must be nonnegative or None')
    prepared = _prepare(triangulation, check); analysed = _coordinates(prepared, coordinates, check)
    size, pairs, weights, csize, cpairs, carriers, geometry = _boundary_system(prepared, analysed, check)
    boundary = orbit_transversal(size, pairs, max_cycles=max_cycles, record_certificate=True, check=check)
    result = dict(status='INCONCLUSIVE', tetrahedra=len(analysed['rows']),
                  trust='source-labelled cut-boundary geometry and boundary profiles; no ball or knot verdict',
                  stats=dict(boundary=boundary['stats']))
    if boundary['status'] != 'COMPLETE':
        return result
    boundary_weights = weighted_histogram_from_orbit_certificate(size, pairs, weights,
        boundary['certificate']['orbit_proof'], dimension=3, record_certificate=record_certificate, check=check)
    joint_pairs = list(pairs)+[IntervalPairing(p.a+size, p.b+size, p.c+size, p.d+size, p.reverse) for p in cpairs]
    for carrier in carriers:
        joint_pairs.append(IntervalPairing(carrier['face_start'], carrier['face_stop']-1,
            size+carrier['chamber_start'], size+carrier['chamber_stop']-1, carrier['reverse']))
    joint_weights = [(lo, hi, [v[0], 0, v[1], v[2], 0]) for lo, hi, v in weights]
    joint_weights.extend((lo, hi, [0, 1, 0, 0, 0]) for lo, hi in boundary['representative_intervals'])
    joint_weights.append((size, size+csize, [0, 0, 0, 0, 1]))
    remaining = None if max_cycles is None else max_cycles-boundary['stats']['orbit_cycles']
    pieces = weighted_orbit_histogram(size+csize, joint_pairs, joint_weights, dimension=5,
        max_cycles=remaining, record_certificate=record_certificate, check=check)
    result['stats'].update(boundary_weights=boundary_weights['stats'], pieces=pieces['stats'])
    if pieces['status'] != 'COMPLETE':
        return result
    bprofiles = _boundary_summary(boundary_weights['histogram'], check)
    pprofiles = _piece_summary(pieces['histogram'], check)
    bcount = sum(r['multiplicity'] for r in bprofiles)
    bchi = sum(r['multiplicity']*r['euler_characteristic'] for r in bprofiles)
    if (bcount != sum(r['multiplicity']*r['boundary_components'] for r in pprofiles)
            or bchi != 2*analysed['euler_characteristic']
            or bchi != sum(r['multiplicity']*r['boundary_euler_characteristic'] for r in pprofiles)):
        raise ArithmeticError('cut boundary conservation failed')
    summary = dict(boundary_components=bcount, boundary_euler_characteristic=bchi,
                   cut_components=pieces['orbit_count'], boundary_profiles=bprofiles, piece_profiles=pprofiles)
    result.update(status='COMPLETE', geometry=geometry, summary=summary)
    if record_certificate:
        result['certificate'] = dict(schema='normal-cut-boundary-v1', input_sha256=_fingerprint(triangulation, analysed, check),
            geometry=geometry, summary=summary, boundary_transversal=boundary['certificate'],
            boundary_weights=boundary_weights['certificate'], pieces=pieces['certificate'])
    check(); return result
