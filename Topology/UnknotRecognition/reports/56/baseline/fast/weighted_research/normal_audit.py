#!/usr/bin/env python3
"""External Regina oracle for weighted normal-component and disc-count routines.

The project package is used only for calls under test and comparison. Every
expected component is expanded and classified by Regina 7.4, subject to an
explicit small-disc cap.  No producer geometry, pairing builder, or weighted
transport helper is used to form an expected answer.

Run from fast/: python weighted_research/normal_audit.py --output results/NAME.json
The companion NAME_corpus.json stores face pairings, input normal vectors,
Regina component vectors, and expected component invariants.  Replaying the
saved corpus still requires Regina to reconstruct native edge labels.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict, deque
from itertools import combinations, product
import json
from pathlib import Path
import random
import sys
import time
import traceback

import regina


SEED = 20261009
MAX_NORMAL_DISCS = 4096
LOCAL_EDGES = tuple(combinations(range(4), 2))


def integer(value):
    return int(str(value))


def native_surface(triangulation, rows):
    return regina.NormalSurface(triangulation, regina.NormalCoords.Standard,
        [regina.LargeInteger(str(x)) for row in rows for x in row])


def surface_rows(surface):
    return [[integer(surface.triangles(t, v)) for v in range(4)] +
            [integer(surface.quads(t, q)) for q in range(3)]
            for t in range(surface.triangulation().size())]


def export_triangulation(triangulation):
    return {'tetrahedra': [[None if tet.adjacentTetrahedron(f) is None else {
        'tetrahedron': tet.adjacentTetrahedron(f).index(),
        'permutation': [tet.adjacentGluing(f)[v] for v in range(4)]}
        for f in range(4)] for tet in triangulation.tetrahedra()]}


def import_triangulation(raw):
    triangulation = regina.Triangulation3()
    for _ in raw['tetrahedra']:
        triangulation.newTetrahedron()
    for t, row in enumerate(raw['tetrahedra']):
        for f, target in enumerate(row):
            if target is not None and triangulation.tetrahedron(t).adjacentTetrahedron(f) is None:
                triangulation.tetrahedron(t).join(f,
                    triangulation.tetrahedron(target['tetrahedron']),
                    regina.Perm4(*target['permutation']))
    return triangulation


def vector_sum(vectors, coefficients):
    return [[sum(c*v[t][j] for c, v in zip(coefficients, vectors))
             for j in range(7)] for t in range(len(vectors[0]))]


def compatible(vectors):
    return all(sum(any(v[t][4+q] for v in vectors) for q in range(3)) <= 1
               for t in range(len(vectors[0])))


def boundary_cap(triangulation):
    """Native face gluing of an extra ball; adds one boundary vertex."""
    result = regina.Triangulation3(triangulation)
    t, f = next((tet.index(), f) for tet in result.tetrahedra()
                for f in range(4) if tet.adjacentTetrahedron(f) is None)
    permutation = [0]*4
    permutation[f] = 3
    for image, vertex in enumerate(v for v in range(4) if v != f):
        permutation[vertex] = image
    new = result.newTetrahedron()
    result.tetrahedron(t).join(f, new, regina.Perm4(*permutation))
    return result


def relabel(triangulation, vectors, seed):
    rng = random.Random(seed)
    images = list(range(triangulation.size()))
    rng.shuffle(images)
    permutations = []
    iso = regina.Isomorphism3(triangulation.size())
    for t in range(triangulation.size()):
        p = list(range(4))
        rng.shuffle(p)
        permutations.append(p)
        iso.setTetImage(t, images[t])
        iso.setFacePerm(t, regina.Perm4(*p))
    transformed = []
    for rows in vectors:
        out = [[0]*7 for _ in rows]
        for t, row in enumerate(rows):
            p = permutations[t]
            for v in range(4):
                out[images[t]][p[v]] = row[v]
            for q in range(3):
                a, b = regina.quadDefn[q][0], regina.quadDefn[q][1]
                new_q = regina.quadSeparating[p[a]][p[b]]
                out[images[t]][4+new_q] = row[4+q]
        transformed.append(out)
    return iso(triangulation), transformed, {
        'seed': seed, 'tetrahedron_images': images, 'vertex_permutations': permutations}


def boundary_data(triangulation, surface):
    """Regina edge weights; independent coboundary test for total boundary class."""
    weights = {edge.index(): integer(surface.edgeWeight(edge.index()))
               for edge in triangulation.edges() if edge.isBoundary()}
    graph = defaultdict(list)
    for edge in triangulation.edges():
        if edge.isBoundary():
            u, v = edge.vertex(0).index(), edge.vertex(1).index()
            graph[u].append((v, weights[edge.index()] & 1))
            graph[v].append((u, weights[edge.index()] & 1))
    assigned = {}
    nonzero = False
    for start in graph:
        if start in assigned:
            continue
        assigned[start] = 0
        queue = deque([start])
        while queue:
            u = queue.popleft()
            for v, parity in graph[u]:
                required = assigned[u] ^ parity
                if v not in assigned:
                    assigned[v] = required
                    queue.append(v)
                elif assigned[v] != required:
                    nonzero = True
    arcs = sum(integer(surface.arcs(face.index(), v))
               for face in triangulation.triangles() if face.isBoundary()
               for v in range(3))
    points = sum(weights.values())
    assert arcs == points, (arcs, points)
    return {'boundary_edge_weights': [[e, weights[e]] for e in sorted(weights)],
            'boundary_points': points, 'boundary_arcs': arcs,
            'boundary_mod2_nonzero': nonzero}


def expected_from_regina(triangulation, rows):
    assert sum(map(sum, rows)) <= MAX_NORMAL_DISCS
    surface = native_surface(triangulation, rows)
    assert surface.embedded() and surface.isCompact()
    components = surface.components()
    grouped = {}
    for component in components:
        coords = surface_rows(component)
        flat = tuple(x for row in coords for x in row)
        if flat not in grouped:
            boundary = boundary_data(triangulation, component)
            chi = integer(component.eulerChar())
            orientable = component.isOrientable()
            count_boundary = component.countBoundaries()
            is_disc = chi == 1 and orientable and count_boundary == 1
            # Regina's native test cuts and retriangulates a candidate disc.
            compressing = component.isCompressingDisc(True) if is_disc else False
            assert compressing == (is_disc and boundary['boundary_mod2_nonzero'])
            grouped[flat] = dict(coordinates=coords, multiplicity=0,
                euler_characteristic=chi, normal_disks=sum(flat),
                orientable=orientable, two_sided=component.isTwoSided(),
                boundary_components=count_boundary, is_disc=is_disc,
                compressing_disk=compressing, **boundary)
        grouped[flat]['multiplicity'] += 1
    records = [grouped[k] for k in sorted(grouped)]
    reconstructed = [0]*(7*triangulation.size())
    for record in records:
        for i, value in enumerate(x for row in record['coordinates'] for x in row):
            reconstructed[i] += value*record['multiplicity']
    assert reconstructed == [x for row in rows for x in row]
    whole = boundary_data(triangulation, surface)
    result = dict(components=len(components),
        euler_characteristic=integer(surface.eulerChar()),
        normal_disks=sum(map(sum, rows)),
        boundary_components=surface.countBoundaries(),
        orientable=surface.isOrientable(), component_records=records, **whole)
    result['compressing_disk_components'] = sum(r['multiplicity'] for r in records
                                               if r['compressing_disk'])
    result['contains_compressing_disk'] = bool(result['compressing_disk_components'])
    assert result['euler_characteristic'] == sum(r['euler_characteristic']*r['multiplicity']
                                               for r in records)
    assert result['boundary_components'] == sum(r['boundary_components']*r['multiplicity']
                                               for r in records)
    return result


def fixture_families():
    families = []
    for a, b in [(1, 2), (2, 3), (3, 5), (5, 8), (8, 13), (1, 3), (2, 5)]:
        families.append((f'lst_{a}_{b}', regina.Example3.lst(a, b),
                         {'operation': 'regina.Example3.lst', 'parameters': [a, b]}))
    capped = regina.Example3.lst(1, 2)
    for n in (1, 2, 3):
        capped = boundary_cap(capped)
        families.append((f'boundary_caps_{n}', regina.Triangulation3(capped),
                         {'operation': 'boundary_cap', 'base': [1, 2], 'caps': n}))
    # Native 1-4 moves reproduce the intended interior-vertex test class.
    for a, b in [(1, 2), (5, 8)]:
        triangulation = regina.Example3.lst(a, b)
        assert triangulation.pachner(triangulation.tetrahedron(0))
        families.append((f'interior_vertex_{a}_{b}', triangulation,
                         {'operation': '1-4 Pachner move on tetrahedron 0', 'base': [a, b]}))
    for name in ('trefoil', 'figureEight'):
        triangulation = getattr(regina.Example3, name)()
        initial = triangulation.isoSig()
        assert triangulation.idealToFinite()
        triangulation.simplify()
        families.append((f'finite_{name}', triangulation,
                         {'operation': 'idealToFinite then simplify',
                          'base': f'regina.Example3.{name}', 'initial_isosig': initial}))
        if name == 'trefoil':
            interior = regina.Triangulation3(triangulation)
            assert interior.pachner(interior.tetrahedron(0))
            families.append(('interior_finite_trefoil', interior,
                {'operation': '1-4 Pachner move on finite trefoil tetrahedron 0',
                 'base': 'finite_trefoil'}))
    return families


def vectors_for(triangulation, family_id, rng):
    native = list(regina.NormalSurfaces(triangulation, regina.NormalCoords.Standard))
    basis = [surface_rows(s) for s in native]
    # Include diverse topological signatures before selecting extra surfaces.
    chosen, signatures = [], set()
    for i, s in enumerate(native):
        signature = (integer(s.eulerChar()), s.isOrientable(), s.countBoundaries(),
                     boundary_data(triangulation, s)['boundary_mod2_nonzero'],
                     s.isCompressingDisc(True) if integer(s.eulerChar()) == 1 else False)
        if signature not in signatures:
            chosen.append(i)
            signatures.add(signature)
    rest = [i for i in range(len(basis)) if i not in chosen]
    rng.shuffle(rest)
    chosen += rest[:max(0, 12-len(chosen))]
    vectors = {}

    def add(rows, category, recipe):
        if sum(map(sum, rows)) <= MAX_NORMAL_DISCS:
            key = tuple(x for row in rows for x in row)
            vectors.setdefault(key, (rows, category, recipe))

    add([[0]*7 for _ in range(triangulation.size())], 'empty', [])
    for i in chosen:
        for coefficient in (1, 2, 3):
            add(vector_sum([basis[i]], [coefficient]), 'vertex_surface_multiple',
                [[i, coefficient]])
    for _ in range(60):
        indices = rng.sample(range(len(basis)), min(3, len(basis)))
        if compatible([basis[i] for i in indices]):
            coefficients = [rng.randrange(1, 5) for _ in indices]
            add(vector_sum([basis[i] for i in indices], coefficients),
                'compatible_mixture', list(map(list, zip(indices, coefficients))))
    discs = [i for i, s in enumerate(native) if integer(s.eulerChar()) == 1
             and s.isCompressingDisc(True)]
    vertex_links = [i for i, v in enumerate(basis)
                    if all(not any(row[4:]) for row in v)]
    for i in discs[:2]:
        for coefficient in (2, 4, 7):
            add(vector_sum([basis[i]], [coefficient]), 'parallel_meridians', [[i, coefficient]])
        for j in vertex_links:
            for coefficient in (2, 11, 37):
                add(vector_sum([basis[i], basis[j]], [2, coefficient]),
                    'meridians_plus_vertex_links', [[i, 2], [j, coefficient]])
    if family_id.startswith('interior_'):
        spheres = [i for i, s in enumerate(native) if integer(s.eulerChar()) == 2
                   and s.countBoundaries() == 0]
        trivial_discs = [i for i, s in enumerate(native) if integer(s.eulerChar()) == 1
                         and not s.isCompressingDisc(True)]
        mobius = [i for i, s in enumerate(native) if integer(s.eulerChar()) == 0
                  and not s.isOrientable() and s.countBoundaries() == 1]
        if spheres and trivial_discs and mobius:
            indices = [spheres[-1], trivial_discs[-1], mobius[0]]
            assert compatible([basis[i] for i in indices])
            for coefficients in product(range(4), repeat=3):
                add(vector_sum([basis[i] for i in indices], coefficients),
                    'sphere_disc_mobius_mixture', list(map(list, zip(indices, coefficients))))
        for sphere in spheres[:1]:
            for i, s in enumerate(native):
                if integer(s.eulerChar()) < 0 and compatible([basis[sphere], basis[i]]):
                    add(vector_sum([basis[sphere], basis[i]], [1, 1]),
                        'sphere_plus_negative_chi', [[sphere, 1], [i, 1]])
    return list(vectors.values()), len(native)


def fixture_metadata(identifier, triangulation, construction, native_count):
    assert triangulation.isValid() and triangulation.isOrientable()
    assert not triangulation.isIdeal() and triangulation.countBoundaryComponents() == 1
    boundary = triangulation.boundaryComponent(0)
    assert boundary.eulerChar() == 0 and boundary.isOrientable()
    return dict(id=identifier, construction=construction,
        triangulation=export_triangulation(triangulation), regina_isosig=triangulation.isoSig(),
        tetrahedra=triangulation.size(), vertices=triangulation.countVertices(),
        boundary_vertices=boundary.countVertices(), boundary_edges=boundary.countEdges(),
        boundary_triangles=boundary.countTriangles(), enumerated_vertex_surfaces=native_count)


def build_corpus():
    rng = random.Random(SEED)
    corpus = dict(schema='regina-normal-component-oracle-v1', seed=SEED,
                  regina_version=regina.versionString(), max_normal_discs=MAX_NORMAL_DISCS,
                  expected_provenance='Regina.components(), eulerChar(), edgeWeight(), arcs(), '
                    'countBoundaries(), isOrientable(), isTwoSided(), isCompressingDisc(True); '
                    'independent graph coboundary test for boundary mod-2 class',
                  triangulations=[], cases=[])
    for family_index, (identifier, triangulation, construction) in enumerate(fixture_families()):
        vectors, native_count = vectors_for(triangulation, identifier, rng)
        variants = [(identifier, triangulation, vectors, construction)]
        # Deterministic permutation of both tetrahedra and local vertex labels.
        selected = vectors[::max(1, len(vectors)//10)][:12]
        for k in range(2):
            other, transformed, transform = relabel(triangulation, [v[0] for v in selected],
                                                    SEED+100*family_index+k)
            variants.append((f'{identifier}_relabel_{k}', other,
                [(v, 'relabelled_'+source[1], source[2]) for v, source in zip(transformed, selected)],
                {'operation': 'relabel', 'base': identifier, **transform}))
        for name, tri, inputs, operation in variants:
            corpus['triangulations'].append(fixture_metadata(name, tri, operation, native_count))
            for i, (rows, category, recipe) in enumerate(inputs):
                corpus['cases'].append(dict(id=f'{name}:{i}', triangulation_id=name,
                    category=category, recipe=recipe, coordinates=rows,
                    expected=expected_from_regina(tri, rows)))
        print(f'oracle generated {identifier}: {len(vectors)} base cases', flush=True)
    return corpus


def native_basis_edges(triangulation, basis):
    """Decode the public 6*t+local-edge labels using Regina's own gluing data."""
    converted = []
    for cycle in basis:
        edges = []
        for label in cycle:
            t, local = divmod(label, 6)
            a, b = LOCAL_EDGES[local]
            edges.append(triangulation.tetrahedron(t).edge(regina.Edge3.edgeNumber[a][b]).index())
        converted.append(edges)
    # Check a homology basis independently, in Regina's global edge numbering.
    boundary_edges = [e.index() for e in triangulation.edges() if e.isBoundary()]
    indices = {edge: i for i, edge in enumerate(boundary_edges)}
    pivots = {}

    def insert(row):
        while row:
            bit = row.bit_length()-1
            if bit not in pivots:
                pivots[bit] = row
                return True
            row ^= pivots[bit]
        return False

    for face in triangulation.triangles():
        if face.isBoundary():
            vector = 0
            for e in range(3):
                vector ^= 1 << indices[face.edge(e).index()]
            insert(vector)
    assert len(converted) == 2
    for cycle in converted:
        degree, row = Counter(), 0
        for edge in cycle:
            native = triangulation.edge(edge)
            assert native.isBoundary()
            degree[native.vertex(0).index()] += 1
            degree[native.vertex(1).index()] += 1
            row ^= 1 << indices[edge]
        assert all(value % 2 == 0 for value in degree.values())
        assert insert(row), 'producer boundary cycles are dependent modulo face boundaries'
    return converted


def expected_histogram(expected, basis, mode):
    histogram = Counter()
    for record in expected['component_records']:
        edges = dict(record['boundary_edge_weights'])
        parity = tuple(sum(edges[e] for e in cycle) % 2 for cycle in basis)
        assert any(parity) == record['boundary_mod2_nonzero']
        key = (record['euler_characteristic'], *parity)
        if mode != 'disk':
            key += (record['normal_disks'], record['boundary_points'])
        if mode == 'coordinates':
            key += tuple(x for row in record['coordinates'] for x in row)
        histogram[key] += record['multiplicity']
    return histogram


def actual_histogram(answer, mode):
    histogram = Counter()
    for record in answer['component_histogram']:
        key = (record['euler_characteristic'], *record['boundary_homology_mod2'])
        if mode != 'disk':
            key += (record['normal_disks'], record['boundary_points'])
        if mode == 'coordinates':
            key += tuple(x for row in record['coordinates'] for x in row)
        histogram[key] += record['multiplicity']
        assert record['compressing_disk'] == (record['euler_characteristic'] == 1
                                               and any(record['boundary_homology_mod2']))
    return histogram


def run_audit(corpus, fast_root):
    sys.path.insert(0, str(fast_root))
    from fastunknot.normal_surface_components import normal_component_census
    from fastunknot.normal_component_verify import verify_normal_component_certificate
    from fastunknot.normal_disk_kernel import (normal_compressing_disk_count,
                                               verify_normal_disk_count_certificate)
    tris = {t['id']: import_triangulation(t['triangulation']) for t in corpus['triangulations']}
    raws = {t['id']: t['triangulation'] for t in corpus['triangulations']}
    started = time.perf_counter()
    outcome = dict(schema='regina-weighted-normal-audit-v1', regina_version=regina.versionString(),
        seed=SEED, cases=len(corpus['cases']), triangulations=len(tris),
        checks=0, certificate_replays=0, normalized_count_checks=0,
        normalized_count_certificate_replays=0,
        failures=[], modes=['disk', 'summary', 'coordinates'],
        category_counts=dict(Counter(c['category'] for c in corpus['cases'])),
        max_normal_discs=max(c['expected']['normal_disks'] for c in corpus['cases']),
        max_tetrahedra=max(t.size() for t in tris.values()))
    critical = Counter()
    reductions = Counter()
    for case_index, case in enumerate(corpus['cases']):
        native, raw = tris[case['triangulation_id']], raws[case['triangulation_id']]
        expected = case['expected']
        if expected['contains_compressing_disk'] and not expected['boundary_mod2_nonzero']:
            critical['essential_discs_with_total_homology_cancellation'] += 1
        if expected['euler_characteristic'] > 0 and not any(r['is_disc'] for r in expected['component_records']):
            critical['positive_total_chi_without_any_disc'] += 1
            if expected['euler_characteristic'] == 1 and expected['boundary_mod2_nonzero']:
                critical['chi_one_nonzero_boundary_class_without_any_disc'] += 1
                if expected['orientable']:
                    critical['orientable_chi_one_nonzero_boundary_class_without_any_disc'] += 1
        if any(not r['orientable'] for r in expected['component_records']):
            critical['nonorientable_component_inputs'] += 1
        if expected['components'] > 1:
            critical['disconnected_inputs'] += 1
        for mode in outcome['modes']:
            try:
                answer = normal_component_census(raw, case['coordinates'], mode=mode,
                                                 record_certificate=True)
                assert answer['status'] == 'COMPLETE', answer
                basis = native_basis_edges(native, answer['boundary_homology_basis'])
                observed = actual_histogram(answer, mode)
                wanted = expected_histogram(expected, basis, mode)
                assert observed == wanted, {'observed': dict(observed), 'expected': dict(wanted)}
                for field in ('components', 'compressing_disk_components', 'contains_compressing_disk',
                              'euler_characteristic', 'normal_disks'):
                    assert answer[field] == expected[field], (field, answer[field], expected[field])
                assert answer['boundary_normal_arcs'] == expected['boundary_arcs']
                assert verify_normal_component_certificate(raw, case['coordinates'], answer['certificate'])
                outcome['checks'] += 1
                outcome['certificate_replays'] += 1
            except Exception as error:
                outcome['failures'].append(dict(case=case['id'], mode=mode,
                    exception=type(error).__name__, message=str(error), traceback=traceback.format_exc()))
                if len(outcome['failures']) >= 20:
                    outcome['aborted_after_failures'] = True
                    outcome['critical_cases'] = dict(critical)
                    outcome['seconds'] = time.perf_counter()-started
                    return outcome
        try:
            answer = normal_compressing_disk_count(raw, case['coordinates'],
                                                   record_certificate=True)
            assert answer['status'] == 'COMPLETE', answer
            for field in ('compressing_disk_components', 'contains_compressing_disk'):
                assert answer[field] == expected[field], (field, answer[field], expected[field])
            assert verify_normal_disk_count_certificate(raw, case['coordinates'],
                                                        answer['certificate'])
            outcome['normalized_count_checks'] += 1
            outcome['normalized_count_certificate_replays'] += 1
            if answer['coordinate_divisor'] == 0:
                reductions['zero_quadrilateral_inputs'] += 1
            elif answer['coordinate_divisor'] > 1:
                reductions['nontrivial_quadrilateral_divisor'] += 1
            if any(record['multiplicity'] for record in answer['vertex_links']):
                reductions['positive_vertex_link_peel'] += 1
            if answer['input_coordinate_bits'] > answer['core_coordinate_bits']:
                reductions['strict_coordinate_bit_reduction'] += 1
        except Exception as error:
            outcome['failures'].append(dict(case=case['id'], mode='normalized_count',
                exception=type(error).__name__, message=str(error), traceback=traceback.format_exc()))
            if len(outcome['failures']) >= 20:
                outcome['aborted_after_failures'] = True
                outcome['critical_cases'] = dict(critical)
                outcome['normalization_cases'] = dict(reductions)
                outcome['seconds'] = time.perf_counter()-started
                return outcome
        if (case_index+1) % 50 == 0:
            print(f'audited {case_index+1}/{len(corpus["cases"])} cases; '
                  f'{len(outcome["failures"])} failures', flush=True)
    outcome['critical_cases'] = dict(critical)
    outcome['normalization_cases'] = dict(reductions)
    outcome['seconds'] = time.perf_counter()-started
    return outcome


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--corpus', type=Path)
    parser.add_argument('--fast-root', type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    if args.corpus:
        corpus = json.loads(args.corpus.read_text())
        corpus_path = args.corpus
    else:
        corpus = build_corpus()
        corpus_path = args.output.with_name(args.output.stem+'_corpus.json')
        corpus_path.write_text(json.dumps(corpus, indent=2)+'\n')
    outcome = run_audit(corpus, args.fast_root)
    outcome['corpus_file'] = corpus_path.name
    args.output.write_text(json.dumps(outcome, indent=2)+'\n')
    print(json.dumps(outcome, indent=2), flush=True)
    return int(bool(outcome['failures']))


if __name__ == '__main__':
    raise SystemExit(main())
