"""Native chamber-graph audit; all literal expansion is bounded to small cases.

Usage: python chamber_graph_audit.py --fast-root PATH --output result.json
An optional --examples directory receives complete source-bound packets.
"""

import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import platform
import sys
import time
import unittest


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--fast-root', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--examples', type=Path)
    args = parser.parse_args()
    root = args.fast_root.resolve()
    sys.path.insert(0, str(root))
    from fastunknot.integer_codec import encoded_integer, json_safe
    from fastunknot.normal_chamber_graph import normal_chamber_graph
    from fastunknot.normal_chamber_graph_verify import verify_normal_chamber_graph
    from normal_orbit_research.fixtures import layered_torus
    from tests.test_normal_chamber_graph import check_literal_graph

    corpus = root / 'marked_parallelity_research/corpus.json'
    bank = json.loads(corpus.read_text())['cases']
    files = [corpus, root / 'fastunknot/normal_chamber_graph.py',
             root / 'fastunknot/normal_chamber_graph_verify.py',
             root / 'tests/test_normal_chamber_graph.py',
             root / 'normal_orbit_research/fixtures.py']
    test = unittest.TestCase()
    cases, counts, subset_checks = [], Counter(), 0
    for case in bank:
        rows = [[encoded_integer(x) for x in row] for row in case['coordinates']]
        if sum(map(sum, rows)) > 500:
            answer = normal_chamber_graph(case['triangulation'], rows, record_certificate=True)
            test.assertEqual(answer['status'], 'INCONCLUSIVE')
            test.assertEqual(answer['reason'], 'representatives_do_not_label_components')
            counts['binary_incomplete_labels'] += 1
            cases.append(dict(id=case['id'], normal_disks=sum(map(sum, rows)),
                              maximum_coordinate_bits=max(x.bit_length() for row in rows for x in row),
                              status=answer['status'], reason=answer['reason'], stats=answer['stats']))
            continue
        start = time.perf_counter()
        answer, checked = check_literal_graph(test, case['triangulation'], rows)
        elapsed = time.perf_counter() - start
        subset_checks += checked
        counts[answer.get('reason', 'COMPLETE')] += 1
        record = dict(id=case['id'], normal_disks=sum(map(sum, rows)),
                      status=answer['status'], reason=answer.get('reason'),
                      exhaustive_subsets=checked, audit_seconds=elapsed)
        if answer['status'] == 'COMPLETE':
            record.update(graph=answer['graph'], components=answer['surface_components'],
                          representatives=answer['representatives'], stats=answer['stats'])
            if args.examples and case['id'] == 'relabel/1/0':
                args.examples.mkdir(parents=True, exist_ok=True)
                packet = dict(source=case['id'], triangulation=case['triangulation'],
                              coordinates=rows, certificate=answer['certificate'])
                (args.examples / 'three_parallel_meridians.json').write_text(
                    json.dumps(json_safe(packet), indent=2) + '\n')
        cases.append(record)

    stress = []
    for t in (16, 32, 64, 128):
        raw, rows = layered_torus(t)
        reps = [dict(tetrahedron=0, column=6, rank=rows[0][6] - 1)]
        start = time.perf_counter()
        answer = normal_chamber_graph(raw, rows, reps, record_certificate=True)
        produce = time.perf_counter() - start
        start = time.perf_counter()
        verified = verify_normal_chamber_graph(raw, rows, answer['certificate'])
        replay = time.perf_counter() - start
        test.assertEqual(answer['status'], 'COMPLETE')
        test.assertTrue(verified)
        test.assertEqual(answer['graph'], dict(vertices=1, edges=[[0, 0]], chamber_masks=[3], cycle_rank=1))
        encoded = json.dumps(json_safe(answer['certificate']), separators=(',', ':')).encode()
        stress.append(dict(tetrahedra=t, normal_disks=answer['normal_disks'],
                           maximum_coordinate_bits=max(x.bit_length() for row in rows for x in row),
                           surface_points=answer['surface_points'], chamber_points=answer['chamber_points'],
                           graph=answer['graph'], certificate_bytes=len(encoded),
                           producer_seconds=produce, replay_seconds=replay, stats=answer['stats']))
        if args.examples and t == 128:
            packet = dict(source='layered_torus(128)', triangulation=raw, coordinates=rows,
                          certificate=answer['certificate'])
            (args.examples / 'exponential_meridian_128.json').write_text(
                json.dumps(json_safe(packet), separators=(',', ':')) + '\n')
    result = dict(schema='native-chamber-graph-audit-v1', python=platform.python_version(),
                  scope='source-bound observer, independent literal subcuts and certificate replay; no full-recognition speedup claim',
                  source_sha256={str(p.relative_to(root)): sha256(p.read_bytes()).hexdigest() for p in files},
                  counts=dict(counts), small_native_cases=sum(c.get('exhaustive_subsets', 0) >= 0
                        for c in cases if 'exhaustive_subsets' in c),
                  exhaustive_subbatch_checks=subset_checks, cases=cases, connected_binary_stress=stress)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(json_safe(result), indent=2) + '\n')
    print(json.dumps(dict(counts=dict(counts), exhaustive_subbatch_checks=subset_checks,
                         connected_binary_stress=stress), indent=2))


if __name__ == '__main__':
    main()
