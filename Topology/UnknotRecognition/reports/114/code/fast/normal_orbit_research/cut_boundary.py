"""Literal boundary cell audits and independent Regina cut-boundary oracles."""
from collections import Counter, defaultdict


def literal_complex(triangulation, geometry, *, max_faces=10000):
    """Expand only a small supplied cell complex and audit every attaching map.

    This reference checks cyclic closure, signed edge incidence, connected
    vertex links and exact face/edge/vertex component inventories. It is not
    used by the binary producer or certificate verifier.
    """
    size = geometry['face_points']
    if size > max_faces:
        raise ValueError('literal boundary expansion exceeds its explicit cap')
    arc_bands, gap_bands = defaultdict(list), defaultdict(list)
    for band in geometry['edges']:
        if band['kind'] == 'normal_arc':
            arc_bands[band['tetrahedron'], band['face'], band['corner'], band['side']].append(band)
        else:
            gap_bands[band['edge']].append(band)
    edge_vertices = {}
    for band in geometry['edges']:
        for rank in range(band['rank_start'], band['rank_stop']):
            index = band['edge_start']+rank-band['rank_start']
            edge_vertices[index] = tuple(s*rank+o for s, o in band['ends'])
    cells, incidences, kinds = {}, defaultdict(list), {}
    for family in geometry['faces']:
        t = family['tetrahedron']
        for face in range(family['start'], family['stop']):
            rank = face-family['start']; boundary = []
            for recipe in family['cycle']:
                if rank < recipe.get('minimum_rank', 0):
                    continue
                s, o = recipe['rank']; r = s*rank+o; forward = recipe['forward']
                if recipe['kind'] == 'normal_arc':
                    f, v, side = recipe['face'], recipe['corner'], recipe['side']
                    entry = triangulation['tetrahedra'][t][f]
                    source_t, source_f, source_v = t, f, v
                    if entry is not None:
                        u, p = entry['tetrahedron'], entry['permutation']; g = p[f]
                        if (u, g) < (t, f):
                            source_t, source_f, source_v = u, g, p[v]
                            others = [x for x in range(4) if x not in (f, v)]
                            if p[others[0]] > p[others[1]]:
                                forward = not forward
                    candidates = arc_bands[source_t, source_f, source_v, side]
                else:
                    candidates = gap_bands[recipe['edge']]
                matches = [b for b in candidates if b['rank_start'] <= r < b['rank_stop']]
                assert len(matches) == 1, (face, recipe, r, matches)
                b = matches[0]; edge = b['edge_start']+r-b['rank_start']
                direction = 1 if forward else -1
                boundary.append((edge, direction))
                incidences[edge].append((face, len(boundary)-1, direction))
            assert 3 <= len(boundary) <= 6, (family, rank, boundary)
            endpoints = [edge_vertices[e] if s == 1 else edge_vertices[e][::-1] for e, s in boundary]
            assert all(a[1] == b[0] for a, b in zip(endpoints, endpoints[1:]+endpoints[:1])), (family, rank, endpoints)
            cells[face] = boundary
            kinds[face] = family['kind'] == 'horizontal'
    assert len(cells) == size
    assert set(incidences) == set(range(geometry['edge_points']))
    parent = list(range(size))
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]; x = parent[x]
        return x
    flags = {(face, i): (face, i) for face, boundary in cells.items() for i in range(len(boundary))}
    def flag_find(x):
        while flags[x] != x:
            flags[x] = flags[flags[x]]; x = flags[x]
        return x
    def join_flags(a, b): flags[flag_find(a)] = flag_find(b)
    for edge, attached in incidences.items():
        assert len(attached) == 2 and sum(s for _, _, s in attached) == 0, (edge, attached)
        (a, i, sa), (b, j, sb) = attached
        parent[find(a)] = find(b)
        # Opposite directed incidences identify an outgoing corner with the
        # incoming corner on the other polygon, and vice versa.
        join_flags((a, i), (b, (j+1) % len(cells[b])))
        join_flags((a, (i+1) % len(cells[a])), (b, j))
    vertex_links = defaultdict(set)
    vertex_owner = {}
    for face, boundary in cells.items():
        for i, (edge, sign) in enumerate(boundary):
            vertex = edge_vertices[edge][0 if sign == 1 else 1]
            vertex_links[vertex].add(flag_find((face, i)))
            owner = find(face)
            assert vertex_owner.setdefault(vertex, owner) == owner
    assert set(vertex_links) == set(range(geometry['vertex_points']))
    assert all(len(links) == 1 for links in vertex_links.values()), 'disconnected vertex link'
    counts = defaultdict(lambda: [0, 0, 0, 0, 0])  # V,E,F,horizontal,original
    for vertex, owner in vertex_owner.items(): counts[owner][0] += 1
    for attached in incidences.values(): counts[find(attached[0][0])][1] += 1
    for face in cells:
        row = counts[find(face)]; row[2] += 1; row[3 if kinds[face] else 4] += 1
    histogram = Counter((v-e+f, h, o) for v, e, f, h, o in counts.values())
    return dict(boundary_components=len(counts), boundary_histogram=histogram,
                faces=len(cells), edges=len(incidences), vertices=len(vertex_links),
                oriented_edge_incidences=2*len(incidences), connected_vertex_links=len(vertex_links))


def regina_profiles(triangulation, coordinates):
    """Actual 3D cuts, independent of every native cell constructor."""
    from normal_orbit_research.fixtures import regina_triangulation, regina_surface
    cut = regina_surface(regina_triangulation(triangulation), coordinates).cutAlong()
    boundary = Counter((2-b.eulerChar())//2 for b in cut.boundaryComponents())
    pieces = Counter((len(c.boundaryComponents()), sum((2-b.eulerChar())//2 for b in c.boundaryComponents()))
                     for c in cut.components())
    return boundary, pieces, cut.size()


def native_profiles(summary):
    boundary, pieces = Counter(), Counter()
    for row in summary['boundary_profiles']: boundary[row['genus']] += row['multiplicity']
    for row in summary['piece_profiles']: pieces[row['boundary_components'], row['total_boundary_genus']] += row['multiplicity']
    return boundary, pieces


def audit(output):
    """Retain exact finite CW checks, 3D oracle outcomes and binary proofs."""
    from contextlib import ExitStack
    from hashlib import sha256
    import json
    from pathlib import Path
    import random
    import sys
    from time import perf_counter
    from unittest.mock import patch
    import regina
    from fastunknot.normal_cut_boundary import normal_cut_boundary
    from fastunknot.normal_cut_boundary_verify import verify_normal_cut_boundary
    from fastunknot.integer_codec import json_safe
    from normal_orbit_research.fixtures import layered_torus, regina_triangulation, regina_surface
    from normal_orbit_research import seeds
    from tests.test_normal_surface_orbits import relabel

    root = Path(__file__).resolve().parents[2]; data = root/'synthesis/data'
    pins = seeds.sources(); began = perf_counter()
    bank = {r['id']: r for r in json.loads((root/'reports/57/results/discovery_corpus.json').read_text())['records']}
    pilot = json.loads((data/'complement-chamber-pilot.json').read_text())
    old = json.loads((data/'cut-complement-audit.json').read_text())
    cases = [('pilot/'+c['id']+'/'+str(c['index']), bank[c['id']]['triangulation'], c['coordinates']) for c in pilot['records']]
    cases += [(c['id'], c['triangulation'], c['coordinates']) for c in old['source_proofs'] if '/mixed' in c['id']]
    raw, meridian = layered_torus(1)
    for kind, base in (('meridian', meridian), ('link', [[1, 1, 1, 1, 0, 0, 0]]), ('mobius', [[0, 0, 0, 0, 0, 1, 0]])):
        for n in range(12): cases.append((f'analytic/{kind}/{n}', raw, [[n*x for x in row] for row in base]))
    rng = random.Random(26101122)
    for t in (1, 2, 4):
        source, base = layered_torus(t); base = [[3*x for x in row] for row in base]
        for i in range(12):
            changed, rows = relabel(source, base, rng); cases.append((f'relabel/{t}/{i}', changed, rows))
    proofs, records, retained, total_incidences = [], [], set(), 0
    disabled = ('fastunknot.normal_cut_boundary._boundary_system', 'fastunknot.normal_cut_boundary._cycle_recipes',
                'fastunknot.normal_cut_boundary._boundary_summary', 'fastunknot.normal_cut_boundary._piece_summary',
                'fastunknot.normal_cut_boundary.normal_cut_boundary', 'fastunknot.normal_cut_complement._chamber_system',
                'fastunknot.orbit_transversal.orbit_transversal', 'fastunknot.orbit_transversal._forward_selector',
                'fastunknot.weighted_orbits.weighted_orbit_histogram',
                'fastunknot.weighted_orbits.weighted_histogram_from_orbit_certificate', 'fastunknot.interval_orbits.count_orbits')
    def replay(source, rows, proof):
        with ExitStack() as stack:
            for name in disabled: stack.enter_context(patch(name, side_effect=AssertionError('producer used')))
            assert verify_normal_cut_boundary(source, rows, proof)
    def encoded(value): return json.dumps(json_safe(value), sort_keys=True, separators=(',', ':')).encode()
    def keep(name, source, rows, result):
        proofs.append(dict(id=name, triangulation=source, coordinates=rows, certificate=result['certificate']))
    for i, (name, source, rows) in enumerate(cases):
        result = normal_cut_boundary(source, rows, record_certificate=True)
        replay(source, rows, result['certificate'])
        literal = literal_complex(source, result['geometry'])
        wanted = Counter()
        for row in result['summary']['boundary_profiles']:
            wanted[row['euler_characteristic'], row['horizontal_polygons'], row['original_polygons']] += row['multiplicity']
        assert literal['boundary_histogram'] == wanted, name
        expected_boundary, expected_pieces, tetrahedra = regina_profiles(source, rows)
        assert native_profiles(result['summary']) == (expected_boundary, expected_pieces), name
        total_incidences += literal['oriented_edge_incidences']
        records.append(dict(id=name, source_tetrahedra=len(rows), normal_discs=sum(map(sum, rows)),
            boundary_components=result['summary']['boundary_components'], cut_components=result['summary']['cut_components'],
            cell_faces=literal['faces'], cell_edges=literal['edges'], cell_vertices=literal['vertices'],
            cut_tetrahedra=tetrahedra, piece_types=[list(k)+[v] for k, v in sorted(expected_pieces.items())],
            proof_sha256=sha256(encoded(result['certificate'])).hexdigest()))
        group = name.split('/')[1] if name.startswith('pilot/') else name
        retain = (name.startswith('pilot/') and group not in retained) or '/mixed' in name or name.endswith('/0') and name.startswith('relabel/')
        if retain: retained.add(group); keep(name, source, rows, result)
        if i % 200 == 0: print('finite cases', i+1, flush=True)
    large = []
    for t, bits in ((1, 128), (1, 500), (4, 128), (4, 500), (16, 128), (16, 500), (1, 16384)):
        source, base = layered_torus(t); n = 1 << bits; rows = [[n*x for x in row] for row in base]
        result = normal_cut_boundary(source, rows, record_certificate=True)
        assert native_profiles(result['summary']) == (Counter({0: n}), Counter({(1, 0): n}))
        replay(source, json_safe(rows), json.loads(encoded(result['certificate'])))
        keep(f'binary/meridian/{t}/{bits}', source, rows, result)
        large.append(dict(kind='meridian', tetrahedra=t, multiplicity_bits=n.bit_length(),
                          face_families=len(result['geometry']['faces']), edge_families=len(result['geometry']['edges']),
                          discovery_cycles=result['stats']['boundary']['orbit_cycles']+result['stats']['pieces']['orbit_cycles']))
    source, _ = layered_torus(1)
    for kind, base, n in (('link', [[1, 1, 1, 1, 0, 0, 0]], 1 << 500),
                          ('mobius-even', [[0, 0, 0, 0, 0, 1, 0]], 1 << 500),
                          ('mobius-odd', [[0, 0, 0, 0, 0, 1, 0]], (1 << 500)+1)):
        rows = [[n*x for x in row] for row in base]; result = normal_cut_boundary(source, rows, record_certificate=True)
        expected = (Counter({0: n, 1: 1}), Counter({(1, 0): n, (1, 1): 1})) if kind == 'link' else (Counter({1: n//2+1}), Counter({(1, 1): n//2+1}))
        assert native_profiles(result['summary']) == expected
        replay(source, rows, result['certificate']); keep('binary/'+kind, source, rows, result)
        large.append(dict(kind=kind, tetrahedra=1, multiplicity_bits=n.bit_length(), face_families=len(result['geometry']['faces']),
                          edge_families=len(result['geometry']['edges']),
                          discovery_cycles=result['stats']['boundary']['orbit_cycles']+result['stats']['pieces']['orbit_cycles']))
    counter = bank['solid_torus_sum_rp3']; rows = counter['standard_vertices'][6]['coordinates']; source = counter['triangulation']
    result = normal_cut_boundary(source, rows, record_certificate=True)
    cut = regina_surface(regina_triangulation(source), rows).cutAlong()
    assert native_profiles(result['summary'])[1] == Counter({(1, 0): 1}) and not cut.isBall() and cut.homology().str() == 'Z_2'
    replay(source, rows, result['certificate']); keep('sphere-boundary-nonball', source, rows, result)
    obstruction = dict(source_id=counter['id'], standard_vertex=6, boundary_components=1, total_boundary_genus=0,
                       regina_is_ball=False, regina_homology='Z_2')
    assert pins == seeds.sources()
    answer = dict(native_source_sha256=pins, regina_version=regina.versionString(), python=sys.version.split()[0],
        finite_cases=len(records), pilot_cases=len(pilot['records']), oriented_edge_incidences=total_incidences,
        large_binary_cases=large, sphere_boundary_obstruction=obstruction, records=records, source_proofs=proofs,
        corpus_sha256=sha256((root/'reports/57/results/discovery_corpus.json').read_bytes()).hexdigest(),
        pilot_sha256=sha256((data/'complement-chamber-pilot.json').read_bytes()).hexdigest(),
        native_seconds=perf_counter()-began)
    Path(output).write_bytes(encoded(answer)+b'\n')
    print(json.dumps({k:answer[k] for k in ('finite_cases', 'pilot_cases', 'oriented_edge_incidences', 'native_seconds')}), flush=True)


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    args = parser.parse_args(); audit(args.output)
