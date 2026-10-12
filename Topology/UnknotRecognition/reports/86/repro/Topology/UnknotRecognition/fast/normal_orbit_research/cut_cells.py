"""Literal chain-map and homology checks for source-labelled 3D cuts."""
from collections import Counter, defaultdict


def _add(vector, index, value):
    value += vector.get(index, 0)
    if value: vector[index] = value
    else: vector.pop(index, None)


def _compose(left, right):
    for column in right:
        result = {}
        for i, coefficient in column.items():
            for j, value in left[i].items(): _add(result, j, coefficient*value)
        assert not result, result


def _rank(columns, prime):
    if prime == 2:
        basis = {}
        for column in columns:
            value = sum(1 << i for i, v in column.items() if v % 2)
            while value:
                pivot = value.bit_length()-1
                if pivot in basis: value ^= basis[pivot]
                else: basis[pivot] = value; break
        return len(basis)
    basis = {}
    for column in columns:
        vector = {i: v % prime for i, v in column.items() if v % prime}
        while vector:
            pivot = min(vector)
            if pivot not in basis:
                inverse = pow(vector[pivot], -1, prime)
                basis[pivot] = {i: v*inverse % prime for i, v in vector.items()}; break
            scale = vector[pivot]
            for i, value in basis[pivot].items():
                updated = (vector.get(i, 0)-scale*value) % prime
                if updated: vector[i] = updated
                else: vector.pop(i, None)
    return len(basis)


def literal_chains(triangulation, geometry, *, max_cells=10000, primes=(2, 3)):
    """Expand only a capped finite reference and check integral d^2=0."""
    counts = [geometry[k+'_points'] for k in ('vertex', 'edge', 'face', 'chamber')]
    if sum(counts) > max_cells: raise ValueError('literal cut-cell expansion exceeds its cap')
    vsize, esize, fsize, csize = counts
    normal, gaps, endpoints = {}, {}, {}
    declared = [dict() for _ in range(fsize)]
    edge_incidences = defaultdict(list)
    boundary_edges, boundary_vertices, boundary_faces = set(), set(), set()
    for family in geometry['vertices']:
        if family['boundary']: boundary_vertices.update(range(family['start'], family['stop']))
    for family in geometry['edges']:
        if family['kind'] == 'normal_arc': normal[family['tetrahedron'], family['face'], family['corner'], family['side']] = family
        else: gaps[family['edge']] = family
        for rank in range(family['stop']-family['start']):
            edge = family['start']+rank
            ends = family.get('ends')
            if ends is None: ends = next(p['ends'] for p in family['endpoint_pieces'] if p['rank_start'] <= rank < p['rank_stop'])
            endpoints[edge] = tuple(s*rank+o for s, o in ends)
            if family['boundary']: boundary_edges.add(edge)
        for incidence in family['incidences']:
            for rank in range(incidence['rank_start'], incidence['rank_stop']):
                edge = family['start']+rank; s, o = incidence['face']; face = s*rank+o
                assert 0 <= face < fsize
                _add(declared[face], edge, incidence['sign'])
                edge_incidences[edge].append((face, incidence['sign']))
    d1 = [dict() for _ in range(esize)]
    for edge, (a, b) in endpoints.items():
        assert 0 <= a < vsize and 0 <= b < vsize
        _add(d1[edge], a, -1); _add(d1[edge], b, 1)
    d2 = [dict() for _ in range(fsize)]
    ordered = {}
    for family in geometry['faces']:
        t = family['tetrahedron']
        for face in range(family['start'], family['stop']):
            rank = face-family['start']; cycle = []
            if family['boundary']: boundary_faces.add(face)
            for recipe in family['cycle']:
                if rank < recipe.get('minimum_rank', 0): continue
                s, o = recipe['rank']; r = s*rank+o; forward = recipe['forward']
                if recipe['kind'] == 'normal_arc':
                    f, v, side = recipe['face'], recipe['corner'], recipe['side']
                    owner_t, owner_f, owner_v = t, f, v
                    entry = triangulation['tetrahedra'][t][f]
                    if entry is not None:
                        u, p = entry['tetrahedron'], entry['permutation']; g = p[f]
                        if (u, g) < (t, f):
                            owner_t, owner_f, owner_v = u, g, p[v]
                            others = [x for x in range(4) if x not in (v, f)]
                            if p[others[0]] > p[others[1]]: forward = not forward
                    edge_family = normal[owner_t, owner_f, owner_v, side]
                else: edge_family = gaps[recipe['edge']]
                assert 0 <= r < edge_family['stop']-edge_family['start']
                edge = edge_family['start']+r; sign = 1 if forward else -1
                _add(d2[face], edge, sign); cycle.append((edge, sign))
            assert 3 <= len(cycle) <= 6
            corners = [endpoints[e] if s == 1 else endpoints[e][::-1] for e, s in cycle]
            assert all(a[1] == b[0] for a, b in zip(corners, corners[1:]+corners[:1])), (face, family, corners)
            ordered[face] = cycle
            assert d2[face] == declared[face], (face, d2[face], declared[face])
    d3 = [dict() for _ in range(csize)]; face_uses = defaultdict(list)
    for incidence in geometry['face_incidence']:
        for face in range(incidence['face_start'], incidence['face_stop']):
            s, o = incidence['chamber']; chamber = s*face+o
            assert 0 <= chamber < csize
            _add(d3[chamber], face, incidence['sign']); face_uses[face].append((chamber, incidence['sign']))
    for face in range(fsize):
        uses = face_uses[face]
        assert len(uses) == (1 if face in boundary_faces else 2), (face, uses)
        if face not in boundary_faces: assert sum(s for _, s in uses) == 0
    _compose(d1, d2); _compose(d2, d3)
    assert all(set(d1[e]) <= boundary_vertices for e in boundary_edges)
    assert all(set(d2[f]) <= boundary_edges for f in boundary_faces)
    # The marked boundary is a closed oriented surface with connected links.
    parent = {f: f for f in boundary_faces}
    def find(f):
        while parent[f] != f: parent[f] = parent[parent[f]]; f = parent[f]
        return f
    flags = {(f, i): (f, i) for f in boundary_faces for i in range(len(ordered[f]))}
    def flag_find(x):
        while flags[x] != x: flags[x] = flags[flags[x]]; x = flags[x]
        return x
    for edge in boundary_edges:
        # Self-identified polygons can have repeated incidences; select flags
        # directly from their cycles instead of the aggregate incidence list.
        occurrences = [(f, i, s) for f in {f for f, _ in edge_incidences[edge] if f in boundary_faces}
                       for i, (e, s) in enumerate(ordered[f]) if e == edge]
        assert len(occurrences) == 2 and sum(s for _, _, s in occurrences) == 0, (edge, occurrences)
        (a, i, _), (b, j, _) = occurrences; parent[find(a)] = find(b)
        flags[flag_find((a, i))] = flag_find((b, (j+1) % len(ordered[b])))
        flags[flag_find((a, (i+1) % len(ordered[a])))] = flag_find((b, j))
    links = defaultdict(set); vertex_owner = {}
    for face in boundary_faces:
        for i, (edge, sign) in enumerate(ordered[face]):
            v = endpoints[edge][0 if sign == 1 else 1]; links[v].add(flag_find((face, i)))
            assert vertex_owner.setdefault(v, find(face)) == find(face)
    assert set(links) == boundary_vertices and all(len(value) == 1 for value in links.values())
    total = defaultdict(lambda: [0, 0, 0])
    for v, f in vertex_owner.items(): total[f][0] += 1
    for edge in boundary_edges:
        face = next(f for f, _ in edge_incidences[edge] if f in boundary_faces); total[find(face)][1] += 1
    for face in boundary_faces: total[find(face)][2] += 1
    boundary_genera = Counter(1-(v-e+f)//2 for v, e, f in total.values())
    betti = {}
    for prime in primes:
        ranks = [_rank(columns, prime) for columns in (d1, d2, d3)]
        betti[prime] = [vsize-ranks[0], esize-ranks[0]-ranks[1], fsize-ranks[1]-ranks[2], csize-ranks[2]]
    return dict(counts=counts, betti=betti, boundary_genera=boundary_genera,
                edge_face_incidences=sum(len(cycle) for cycle in ordered.values()),
                face_chamber_incidences=sum(map(len, face_uses.values())),
                chain_zero_checks=fsize+csize, boundary_vertex_links=len(links))


def regina_cut_homology(triangulation, coordinates):
    from normal_orbit_research.fixtures import regina_triangulation, regina_surface
    cut = regina_surface(regina_triangulation(triangulation), coordinates).cutAlong()
    first = cut.homology(1); second = cut.homology(2)
    betti = {p: [cut.countComponents(), first.rank()+first.torsionRank(p),
                  second.rank()+first.torsionRank(p), 0] for p in (2, 3)}
    genera = Counter((2-b.eulerChar())//2 for b in cut.boundaryComponents())
    return betti, genera, cut.size(), cut.eulerCharManifold()


def audit(output):
    from contextlib import ExitStack
    from hashlib import sha256
    import json
    from pathlib import Path
    import random
    from time import perf_counter
    from unittest.mock import patch
    import regina
    from fastunknot.integer_codec import json_safe
    from fastunknot.normal_cut_cells import normal_cut_cell_complex
    from fastunknot.normal_cut_cells_verify import verify_normal_cut_cell_complex
    from normal_orbit_research.fixtures import layered_torus
    from normal_orbit_research import seeds
    from tests.test_normal_surface_orbits import relabel
    root = Path(__file__).resolve().parents[2]; data = root/'synthesis/data'; began = perf_counter(); pins = seeds.sources()
    bank = {r['id']: r for r in json.loads((root/'reports/57/results/discovery_corpus.json').read_text())['records']}
    pilot = json.loads((data/'complement-chamber-pilot.json').read_text())
    old = json.loads((data/'cut-complement-audit.json').read_text())
    cases = [(f"pilot/{r['id']}/{r['index']}", bank[r['id']]['triangulation'], r['coordinates']) for r in pilot['records']]
    cases.extend((r['id'], r['triangulation'], r['coordinates']) for r in old['source_proofs'] if '/mixed' in r['id'])
    source, meridian = layered_torus(1)
    for kind, base in (('meridian', meridian), ('link', [[1, 1, 1, 1, 0, 0, 0]]), ('mobius', [[0, 0, 0, 0, 0, 1, 0]])):
        for n in range(12): cases.append((f'analytic/{kind}/{n}', source, [[n*x for x in row] for row in base]))
    rng = random.Random(26101132)
    for t in (1, 2, 4):
        raw, base = layered_torus(t); rows = [[3*x for x in row] for row in base]
        for i in range(12):
            changed, vector = relabel(raw, rows, rng); cases.append((f'relabel/{t}/{i}', changed, vector))
    disabled = ('fastunknot.normal_cut_cells._cut_cells', 'fastunknot.normal_cut_cells._orientations',
                'fastunknot.normal_cut_cells._summary', 'fastunknot.normal_cut_cells.normal_cut_cell_complex',
                'fastunknot.normal_cut_boundary._cycle_recipes', 'fastunknot.normal_cut_boundary._boundary_system',
                'fastunknot.normal_cut_complement._chamber_system', 'fastunknot.interval_orbits.count_orbits')
    def encode(value): return json.dumps(json_safe(value), sort_keys=True, separators=(',', ':')).encode()
    def replay(raw, rows, proof):
        with ExitStack() as stack:
            for name in disabled: stack.enter_context(patch(name, side_effect=AssertionError('producer used')))
            assert verify_normal_cut_cell_complex(raw, rows, proof)
    records, proofs, kept = [], [], set(); edge_inc = face_inc = zero_checks = 0
    for i, (name, raw, rows) in enumerate(cases):
        result = normal_cut_cell_complex(raw, rows, record_certificate=True); replay(raw, rows, result['certificate'])
        literal = literal_chains(raw, result['geometry'])
        betti, genera, tetrahedra, chi = regina_cut_homology(raw, rows)
        assert literal['betti'] == betti and literal['boundary_genera'] == genera, name
        assert result['summary']['euler_characteristic'] == chi, name
        edge_inc += literal['edge_face_incidences']; face_inc += literal['face_chamber_incidences']; zero_checks += literal['chain_zero_checks']
        records.append(dict(id=name, source_tetrahedra=len(rows), normal_discs=sum(map(sum, rows)), counts=literal['counts'],
                            betti=betti, boundary_genera=[[g, n] for g, n in sorted(genera.items())],
                            euler_characteristic=chi, cut_tetrahedra=tetrahedra, proof_sha256=sha256(encode(result['certificate'])).hexdigest()))
        group = name.split('/')[1] if name.startswith('pilot/') else name
        retain = (name.startswith('pilot/') and group not in kept) or '/mixed' in name or name.startswith('relabel/') and name.endswith('/0')
        if retain:
            kept.add(group); proofs.append(dict(id=name, triangulation=raw, coordinates=rows, certificate=result['certificate']))
        if i % 200 == 0: print('finite cells', i+1, flush=True)
    large = []
    for t, bits in ((1, 128), (1, 500), (4, 128), (4, 500), (16, 128), (16, 500), (1, 16384)):
        raw, base = layered_torus(t); n = 1 << bits; rows = [[n*x for x in row] for row in base]
        result = normal_cut_cell_complex(raw, rows, record_certificate=True)
        assert result['summary']['euler_characteristic'] == n
        replay(raw, json_safe(rows), json.loads(encode(result['certificate'])))
        proofs.append(dict(id=f'binary/meridian/{t}/{bits}', triangulation=raw, coordinates=rows, certificate=result['certificate']))
        g = result['geometry']; large.append(dict(kind='meridian', tetrahedra=t, multiplicity_bits=n.bit_length(),
            vertex_families=len(g['vertices']), edge_families=len(g['edges']), face_families=len(g['faces']), chamber_families=len(g['chambers'])))
    raw, _ = layered_torus(1)
    for kind, base, n, chi in (('link', [[1, 1, 1, 1, 0, 0, 0]], 1 << 500, 1 << 500),
                             ('mobius-even', [[0, 0, 0, 0, 0, 1, 0]], 1 << 500, 0),
                             ('mobius-odd', [[0, 0, 0, 0, 0, 1, 0]], (1 << 500)+1, 0)):
        rows = [[n*x for x in row] for row in base]; result = normal_cut_cell_complex(raw, rows, record_certificate=True)
        assert result['summary']['euler_characteristic'] == chi; replay(raw, rows, result['certificate'])
        proofs.append(dict(id='binary/'+kind, triangulation=raw, coordinates=rows, certificate=result['certificate']))
        g = result['geometry']; large.append(dict(kind=kind, tetrahedra=1, multiplicity_bits=n.bit_length(),
            vertex_families=len(g['vertices']), edge_families=len(g['edges']), face_families=len(g['faces']), chamber_families=len(g['chambers'])))
    case = bank['solid_torus_sum_rp3']; rows = case['standard_vertices'][6]['coordinates']; raw = case['triangulation']
    result = normal_cut_cell_complex(raw, rows, record_certificate=True); literal = literal_chains(raw, result['geometry'])
    assert literal['betti'] == {2: [1, 1, 1, 0], 3: [1, 0, 0, 0]}
    replay(raw, rows, result['certificate']); proofs.append(dict(id='sphere-boundary-torsion', triangulation=raw, coordinates=rows, certificate=result['certificate']))
    assert pins == seeds.sources()
    result = dict(native_source_sha256=pins, regina_version=regina.versionString(), finite_cases=len(records), pilot_cases=len(pilot['records']),
        integral_zero_checks=zero_checks, edge_face_incidences=edge_inc, face_chamber_incidences=face_inc,
        large_binary_cases=large, records=records, source_proofs=proofs, sphere_boundary_betti=literal['betti'],
        native_seconds=perf_counter()-began, pilot_sha256=sha256((data/'complement-chamber-pilot.json').read_bytes()).hexdigest(),
        corpus_sha256=sha256((root/'reports/57/results/discovery_corpus.json').read_bytes()).hexdigest())
    Path(output).write_bytes(encode(result)+b'\n')
    print(json.dumps({k:result[k] for k in ('finite_cases', 'pilot_cases', 'integral_zero_checks', 'edge_face_incidences', 'face_chamber_incidences', 'native_seconds')}), flush=True)


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__); parser.add_argument('--output', required=True)
    args = parser.parse_args(); audit(args.output)
