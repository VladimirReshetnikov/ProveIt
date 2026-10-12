"""Reproducible edge-defect discovery, layering and independent audits.

All fixtures are supplied finite solid-torus triangulations.  No benchmark
asserts a knot-diagram conversion or a change to the default recognizer.
The optional Regina audit is independent of native witness production.
"""

import argparse
from copy import deepcopy
from fractions import Fraction
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import random
import statistics
import time
from unittest.mock import patch

from fastunknot.normal_cocycle import _rank_one_cocycle_seed_details, local_coordinates
from fastunknot.normal_disk_kernel import (
    normal_compressing_disk_count, verify_normal_disk_count_certificate,
)
from fastunknot.normal_sector import build_sector_kernel, discover_in_sector
from fastunknot.normal_sector_verify import verify_sector_witness
from fastunknot.normal_surface_geometry import _prepare, _coordinates, _edge, _EDGES
from fastunknot.normal_weight_defect import (
    _build_subspace, _initial_stats, _one_vertex_data, discover_in_weight_subspace,
    enumerate_weight_subspace, local_coordinates_from_weights,
    one_edge_defect_search, weight_defect_search, weight_subspace_rays,
)
from fastunknot.pachner23 import pachner_23
from normal_orbit_research.coherent_obstruction import replay as replay_obstruction
from normal_orbit_research.fixtures import (
    export_surface, fibonacci, layered_torus, regina_surface, regina_triangulation,
)

ROOT = Path(__file__).resolve().parents[2]
OBSTRUCTION = ROOT/'synthesis/data/coherent-obstruction-certificate.json'
DISC_ONE_EDGE = [
    [2, 2, 0, 0, 0, 0, 2], [0, 0, 2, 2, 0, 2, 0],
    [0, 0, 1, 2, 0, 0, 2], [0, 2, 0, 2, 0, 0, 1],
    [2, 0, 0, 2, 0, 1, 0], [2, 3, 0, 1, 1, 0, 0],
    [2, 3, 2, 0, 0, 0, 0], [2, 3, 0, 1, 0, 0, 0],
]


def _flat(rows):
    return tuple(x for row in rows for x in row)


def _support(rows):
    return [(t, q) for t, row in enumerate(rows) for q in range(3) if row[4+q]]


def obstruction():
    record = json.loads(OBSTRUCTION.read_text())
    return replay_obstruction(record), deepcopy(DISC_ONE_EDGE)


def boundary_layer(raw, coordinates, chosen_edge):
    """Attach one tetrahedron to the two boundary faces at a chosen edge.

    The local shared edge maps to 01, the two old faces to 012 and 013.
    The oriented edge equivalences determine the full formal face charts.
    The new diagonal is 23.  The one-vertex torus charts form a parallelogram
    in cocycle heights; this identity and all normal matching are checked.
    """
    seed, prepared = _rank_one_cocycle_seed_details(raw)
    if prepared['vertices'] != 1 or chosen_edge not in prepared['boundary_incidence']:
        raise ValueError('expected an edge of the one-vertex torus boundary')
    occurrences = []
    for t, f in prepared['boundary_faces']:
        for a, b in _EDGES:
            local = _edge(t, a, b)
            if f not in (a, b) and prepared['edge_roots'][local] == chosen_edge:
                occurrences.append((t, f, a, b, prepared['edge_orientations'][local]))
    if len(occurrences) != 2:
        raise ArithmeticError('boundary layer must have two attaching edge occurrences')
    t, f, a, b, sign = occurrences[0]
    u, g, aa, bb, other_sign = occurrences[1]
    if sign != other_sign:
        aa, bb = bb, aa
    c = next(v for v in range(4) if v not in (a, b, f))
    d = next(v for v in range(4) if v not in (aa, bb, g))
    first, second = [0]*4, [0]*4
    first[a], first[b], first[c], first[f] = 0, 1, 2, 3
    second[aa], second[bb], second[d], second[g] = 0, 1, 3, 2
    index = len(raw['tetrahedra'])
    result = deepcopy(raw)
    result['tetrahedra'][t][f] = dict(tetrahedron=index, permutation=first)
    result['tetrahedra'][u][g] = dict(tetrahedron=index, permutation=second)
    result['tetrahedra'].append([None, None,
        dict(tetrahedron=u, permutation=[second.index(v) for v in range(4)]),
        dict(tetrahedron=t, permutation=[first.index(v) for v in range(4)])])
    heights = seed['heights']
    local_heights = [0, heights[t][b]-heights[t][a], heights[t][c]-heights[t][a],
                     heights[u][d]-heights[u][aa]]
    if (local_heights[1] != heights[u][bb]-heights[u][aa]
            or local_heights[0]+local_heights[1] != local_heights[2]+local_heights[3]):
        raise ArithmeticError('boundary cocycle charts did not form a parallelogram')
    extension = local_coordinates(local_heights)
    result_rows = deepcopy(coordinates)+[extension]
    new_seed, new_prepared = _rank_one_cocycle_seed_details(result)
    _coordinates(new_prepared, result_rows, lambda: None)
    if new_seed['coordinates'] != seed['coordinates']+[extension]:
        raise ArithmeticError('coherent row failed transport across boundary layering')
    record = dict(chosen_edge=chosen_edge, tetrahedron=index,
                  old_faces=[[t, f], [u, g]], charts=[first, second],
                  heights=local_heights, normal_row=extension)
    return result, result_rows, record


def layered_obstruction(layers):
    if type(layers) is not int or layers < 0:
        raise ValueError('layers must be a nonnegative integer')
    raw, disc = obstruction()
    moves = []
    for _ in range(layers):
        seed, prepared = _rank_one_cocycle_seed_details(raw)
        baseline = _coordinates(prepared, seed['coordinates'], lambda: None)['weights']
        edge = min(prepared['boundary_incidence'], key=lambda e: (baseline[e], e))
        raw, disc, record = boundary_layer(raw, disc, edge)
        moves.append(record)
    return raw, disc, moves


def family_audit(layer_counts=(0, 1, 2, 4, 8, 16, 32), *, regina=False):
    cases = []
    for layers in layer_counts:
        raw, disc, moves = layered_obstruction(layers)
        seed, prepared = _rank_one_cocycle_seed_details(raw)
        base = _coordinates(prepared, seed['coordinates'], lambda: None)
        data = _coordinates(prepared, disc, lambda: None)
        defect = {e: (data['weights'][e]-base['weights'][e])//2
                  for e in data['weights'] if data['weights'][e] != base['weights'][e]}
        assert defect == {30: 2}
        assert base['euler_characteristic'] == -3 and data['euler_characteristic'] == 1
        assert sum(map(sum, disc)) == fibonacci(layers+7)+34
        assert sum(map(sum, seed['coordinates'])) == fibonacci(layers+7)+28
        kernel = build_sector_kernel(raw, _support(disc))
        assert kernel.is_standard_ray(disc)
        result = normal_compressing_disk_count(raw, disc, record_certificate=True)
        assert result['contains_compressing_disk']
        # The verifier is deliberately run with all corresponding producers disabled.
        with patch('fastunknot.normal_disk_kernel.normal_compressing_disk_count',
                   side_effect=AssertionError), \
             patch('fastunknot.normal_weight_defect.one_edge_defect_search',
                   side_effect=AssertionError):
            assert verify_normal_disk_count_certificate(raw, disc, result['certificate'])
        independent = {}
        if regina and sum(map(sum, disc)) <= 10000:
            native = regina_triangulation(raw)
            surface = regina_surface(native, disc)
            coherent = regina_surface(native, seed['coordinates'])
            assert native.isSolidTorus() and surface.isCompressingDisc(True)
            assert coherent.isConnected() and coherent.isOrientable()
            assert coherent.countBoundaries() == 1 and int(str(coherent.eulerChar())) == -3
            independent = dict(regina_disc=True, regina_coherent_genus=2,
                               iso_signature=native.isoSig())
        elif regina:
            independent = dict(regina_disc=None,
                regina_omitted='More than 10,000 normal pieces; Regina documents that '
                'these surface-topology methods explicitly expand normal discs/arcs. '
                'Native binary certificates and exact extremality are still verified.')
        cases.append(dict(layers=layers, tetrahedra=len(raw['tetrahedra']),
            pieces=sum(map(sum, disc)), coherent_pieces=sum(map(sum, seed['coordinates'])),
            coordinate_bits=max(x.bit_length() for row in disc for x in row),
            weight_bits=max(x.bit_length() for x in data['weights'].values()),
            defect=defect, standard_vertex=True, native_replay=True,
            chi_disc=1, chi_coherent=-3, kernel_stats=kernel.stats,
            triangulation=raw, coordinates=disc, layer_records=moves,
            disk_certificate=result['certificate'], **independent))
    return dict(cases=cases, scope='supplied solid-torus triangulations; no diagram conversion')


def complete_enumeration(max_defect):
    raw, _ = obstruction()
    prepared, baseline = _one_vertex_data(raw, lambda: None)
    edges = tuple(sorted(baseline))
    stats, seen, rows = _initial_stats(), set(), []
    start = time.perf_counter()
    for size in range(max_defect+1):
        for selected in combinations(edges, size):
            subspace = _build_subspace(prepared, baseline, selected, lambda: None)
            rows.extend(weight_subspace_rays(subspace, stats=stats, seen=seen))
    elapsed = time.perf_counter()-start
    vertices, discs = 0, []
    for row in rows:
        if not any(x for values in row for x in values[4:]):
            continue
        vertices += build_sector_kernel(raw, _support(row)).is_standard_ray(row)
        if _coordinates(prepared, row, lambda: None)['euler_characteristic'] > 0:
            count = normal_compressing_disk_count(raw, row, record_certificate=True)
            assert count['status'] == 'COMPLETE'
            assert verify_normal_disk_count_certificate(raw, row, count['certificate'])
            if count['contains_compressing_disk']:
                discs.append(row)
    return dict(max_defect=max_defect, construction_seconds=elapsed, stats=stats,
                standard_vertex_rays=vertices, disc_vectors=discs,
                scope='complete arrangement construction; observer times excluded')


def _seeded_sector(raw):
    seed, _ = _rank_one_cocycle_seed_details(raw)
    return discover_in_sector(raw, _support(seed['coordinates']), phase='quadrilateral')


def benchmark(rounds=7, layer_counts=(0, 8, 32, 64)):
    rng = random.Random(261012084)
    arms = dict(coherent=lambda raw: weight_defect_search(raw, max_defect=0),
                seeded_q_sector=_seeded_sector,
                all_subspaces_k1=lambda raw: weight_defect_search(raw, max_defect=1),
                global_one_edge=one_edge_defect_search,
                supplied_edge=lambda raw: discover_in_weight_subspace(raw, [30]))
    results, witnesses, fixtures = [], {}, []
    for layers in layer_counts:
        raw, expected, _ = layered_obstruction(layers)
        label = 'obstruction_plus_'+str(layers)
        seed, _ = _rank_one_cocycle_seed_details(raw)
        sector = build_sector_kernel(raw, _support(seed['coordinates']))
        fixtures.append(dict(name=label, tetrahedra=len(raw['tetrahedra']),
                             pieces=sum(map(sum, expected)), seeded_kernel=sector.stats))
        for call in arms.values():
            call(raw)
        for iteration in range(rounds):
            order = list(arms)
            rng.shuffle(order)
            for name in order:
                start = time.perf_counter()
                answer = arms[name](raw)
                elapsed = time.perf_counter()-start
                assert answer['status'] == ('NO_VERTEX_DISC_UP_TO_EDGE_DEFECT'
                                            if name == 'coherent' else 'DISC_FOUND')
                replay_seconds, verified = None, None
                if answer['status'] == 'DISC_FOUND':
                    start = time.perf_counter()
                    if name == 'seeded_q_sector':
                        verified = verify_sector_witness(raw, answer['certificate'])
                    else:
                        verified = verify_normal_disk_count_certificate(
                            raw, answer['coordinates'], answer['certificate'])
                    replay_seconds = time.perf_counter()-start
                    assert verified
                    witnesses.setdefault(label, {})[name] = answer
                results.append(dict(fixture=label, round=iteration, arm=name,
                    seconds=elapsed, fresh_replay_seconds=replay_seconds,
                    status=answer['status'], fresh_replay=verified, stats=answer['stats']))
    summary = []
    for fixture in fixtures:
        for arm in arms:
            samples = [r for r in results if r['fixture'] == fixture['name'] and r['arm'] == arm]
            replay = [r['fresh_replay_seconds'] for r in samples
                      if r['fresh_replay_seconds'] is not None]
            summary.append(dict(fixture=fixture['name'], arm=arm,
                median_seconds=statistics.median(r['seconds'] for r in samples),
                min_seconds=min(r['seconds'] for r in samples),
                max_seconds=max(r['seconds'] for r in samples),
                median_fresh_replay_seconds=statistics.median(replay) if replay else None,
                status=samples[0]['status'], stats=samples[0]['stats']))
    return dict(rounds=rounds, warmup_rounds=1, fixtures=fixtures, samples=results,
                summary=summary, witnesses=witnesses,
                measurement='Each discovery time includes cocycle preparation, candidate '
                'construction, native disc observer, and internal independent replay. '
                'Fresh replay is separately timed once more and is outside discovery time.',
                scope='supplied triangulations only; finite structured family; '
                'coherent arm has restricted exhaustion, not a knottedness verdict')


def regina_audit():
    import regina
    rng = random.Random(261012089)
    fixtures = []
    for initial in (1, 2):
        raw, _ = layered_torus(initial)
        fixtures.append(raw)
        for _ in range(6):
            sites = [(t, f) for t, row in enumerate(raw['tetrahedra'])
                     for f, record in enumerate(row)
                     if record is not None and record['tetrahedron'] != t]
            if not sites:
                break
            raw = pachner_23(raw, *rng.choice(sites))['triangulation']
            fixtures.append(raw)
    records = []
    total_surfaces, coverage_queries, meridians = 0, 0, 0
    for index, raw in enumerate(fixtures):
        tri = regina_triangulation(raw)
        assert tri.isSolidTorus()
        seed, prepared = _rank_one_cocycle_seed_details(raw)
        base = _coordinates(prepared, seed['coordinates'], lambda: None)['weights']
        surfaces = list(regina.NormalSurfaces(tri, regina.NS_STANDARD))
        cache = {}
        for surface in surfaces:
            rows = export_surface(surface)
            data = _coordinates(prepared, rows, lambda: None)
            for t, row in enumerate(rows):
                local = [data['weights'][prepared['edge_roots'][_edge(t, a, b)]]
                         for a, b in _EDGES]
                assert local_coordinates_from_weights(local) == row
            total_surfaces += 1
            if not surface.isCompressingDisc(True):
                continue
            meridians += 1
            delta = {e: data['weights'][e]-base[e] for e in base}
            assert all(x >= 0 and x % 2 == 0 for x in delta.values())
            exceptional = tuple(e for e in sorted(base) if delta[e])
            if len(exceptional) <= 2:
                if exceptional not in cache:
                    candidates, _ = enumerate_weight_subspace(raw, list(exceptional))
                    cache[exceptional] = {_flat(candidate) for candidate in candidates}
                    coverage_queries += 1
                assert _flat(rows) in cache[exceptional]
            if len(exceptional) <= 1:
                assert one_edge_defect_search(raw)['status'] == 'DISC_FOUND'
        records.append(dict(fixture=index, tetrahedra=len(raw['tetrahedra']),
                            iso_signature=tri.isoSig(), vertex_surfaces=len(surfaces)))
    return dict(regina_version=regina.versionString(), fixtures=records,
                reconstructed_vertex_surfaces=total_surfaces, meridians=meridians,
                exact_subspace_coverage_queries=coverage_queries,
                family=family_audit(regina=True))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=('family', 'enumeration', 'benchmark', 'regina', 'all'))
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rounds', type=int, default=7)
    args = parser.parse_args()
    if args.rounds < 1:
        parser.error('--rounds must be positive')
    result = {}
    if args.mode in ('family', 'all'):
        result['family'] = family_audit()
    if args.mode in ('enumeration', 'all'):
        result['enumeration'] = [complete_enumeration(k) for k in (0, 1, 2)]
    if args.mode in ('benchmark', 'all'):
        result['benchmark'] = benchmark(args.rounds)
    if args.mode in ('regina', 'all'):
        result['regina'] = regina_audit()
    paths = [Path(__file__), ROOT/'fast/fastunknot/normal_weight_defect.py',
             ROOT/'fast/tests/test_normal_weight_defect.py',
             ROOT/'fast/fastunknot/normal_sector.py', ROOT/'fast/fastunknot/normal_cocycle.py']
    result['source_sha256'] = {str(p.relative_to(ROOT)): sha256(p.read_bytes()).hexdigest()
                               for p in paths}
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({key: ('complete' if key != 'source_sha256' else value)
                      for key, value in result.items()}))


if __name__ == '__main__':
    main()
