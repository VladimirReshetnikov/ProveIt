"""Seeded source relabelling audit for successful forest choices.

Every instance is the same supplied solid torus with relabelled tetrahedra
and corners.  This tests a labelled algorithm, not new knot types.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random
import sys
import time


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--baseline-fast', type=Path, required=True)
    parser.add_argument('--dual-pack', type=Path, required=True)
    parser.add_argument('--homological-pack', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--count', type=int, default=256)
    args = parser.parse_args()
    overlay = args.dual_pack/'native/Topology/UnknotRecognition/fast'
    homo = args.homological_pack
    sys.path[:0] = [str(args.baseline_fast), str(overlay),
                    str(homo/'research/experiments'), str(Path(__file__).parent)]
    import fastunknot
    fastunknot.__path__.extend([str(overlay/'fastunknot'),
                               str(homo/'runtime/fast/fastunknot')])
    from fastunknot.core_handlebody import _forest
    from fastunknot.core_dual_forest import core_dual_forest
    from fastunknot.disk_bundle_absorption import source_core_circle
    from fastunknot.normal_parallelity import normal_cut_parallelity
    from fastunknot.normal_parallelity_geometry import _parallelity_geometry
    from fastunknot.normal_surface_geometry import _prepare, _coordinates
    from fastunknot.parallelity_boundary_words import normal_parallelity_boundary_words
    from source_core_dual_research.matrix_audit import make_problem
    from core_dual_fixtures import interior_loop_torus, vertex_link_coordinates, relabel
    from study import finite_raw_rows, capped, column_profile, independent_tree_oracle
    original = interior_loop_torus()
    coordinates = vertex_link_coordinates(original)
    rng = random.Random(20261012471)
    records = []
    started = time.perf_counter()
    for trial in range(args.count):
        order = list(range(len(coordinates)))
        rng.shuffle(order)
        corners = []
        for _ in order:
            p = list(range(4)); rng.shuffle(p); corners.append(p)
        raw, coords = relabel(original, coordinates, order, corners)
        prepared = _prepare(raw, lambda: None)
        analysed = _coordinates(prepared, coords, lambda: None)
        g = _parallelity_geometry(prepared, analysed, lambda: None)
        forest, _ = _forest(g['core'], lambda: None)
        summary = normal_cut_parallelity(raw, coords)['summary']
        skeleton = normal_parallelity_boundary_words(raw, coords)['skeleton']
        rows, width, annuli = finite_raw_rows(g, summary, skeleton,
                                             source_core_circle, set(forest))
        # Retain uncapped counts for the full-matrix cycle-parity gate.
        problem, ids = make_problem(g, rows, width)
        oracle = independent_tree_oracle(problem)
        assert oracle['status'] == 'COMPLETE'
        successes = {tuple(t) for t in oracle['successful_trees']}
        result = {'trial': trial, 'tetrahedron_permutation': order,
                  'corner_permutations': corners, 'primal_forest': forest,
                  'source': {'triangulation': raw, 'coordinates': coords},
                  'problem': problem, 'native_row_ids': ids,
                  'profile': column_profile(rows, width), 'oracle': oracle}
        for strategy in ('bfs', 'max_weight'):
            plan = core_dual_forest(g, strategy=strategy)
            assert plan['status'] == 'COMPLETE'
            native = [e for _, e in plan['certificate']['cancellations']]
            selected = tuple(sorted(ids.index(e) for e in native))
            result[strategy] = {'tree': list(selected),
                                'success': selected in successes,
                                'stats': plan['stats']}
        records.append(result)
        if trial % 32 == 0:
            print(json.dumps({'completed': trial+1,
                              'both_miss': sum(r['oracle']['exists'] and not
                                r['bfs']['success'] and not r['max_weight']['success']
                                for r in records)}), flush=True)
    totals = {'cases': len(records),
              'exists': sum(r['oracle']['exists'] for r in records),
              'bfs_successes': sum(r['bfs']['success'] for r in records),
              'max_weight_successes': sum(r['max_weight']['success'] for r in records),
              'both_miss': sum(r['oracle']['exists'] and not r['bfs']['success']
                               and not r['max_weight']['success'] for r in records),
              'k_histogram': dict(Counter(r['profile']['k'] for r in records))}
    out = {'seed': 20261012471, 'count': args.count,
           'scope': 'Relabelled zero cuts of one five-tetrahedron solid torus; finite forest selection.',
           'elapsed_seconds': time.perf_counter()-started,
           'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           'totals': totals, 'cases': records}
    args.output.write_text(json.dumps(out, indent=2)+'\n')
    print(json.dumps(totals), flush=True)


if __name__ == '__main__':
    main()
