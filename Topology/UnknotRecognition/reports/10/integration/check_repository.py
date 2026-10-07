#!/usr/bin/env python3
"""Read-only integration validation against a local ProveIt checkout.

This script is supplied but was NOT run against the complete repository while
preparing this package. It does not alter the checkout. Source hashes, comparisons,
and optional whole closed-PD scans are reported as JSON.
SPDX-License-Identifier: MIT-0
"""
from __future__ import annotations
import argparse
import hashlib
import itertools
import json
import random
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT/'code'), str(ROOT/'tests')]
from component_kernel import ComponentAlgebra, ComponentPlan
from reference_planar import matchings
from fixtures import zipper_triple

AUDITED = {
    'planar.py': '1078526e7e7dbaf0b7267728105d870d94136769',
    'scan_fast.py': '2c1ad52d14296b109376af19668ae0eebb4c6fdd',
}


def blob_sha(path: Path) -> str:
    data = path.read_bytes().replace(b'\r\n', b'\n')
    return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--fast-root', type=Path, required=True,
                    help='.../ProveIt/Topology/UnknotRecognition/fast')
    ap.add_argument('--random-triples', type=int, default=400)
    ap.add_argument('--scan-examples', action='store_true',
                    help='also compare direct closed-PD FastScan runs, not pipeline verdicts')
    ap.add_argument('--max-crossings', type=int, default=14)
    ap.add_argument('--max-objects', type=int, default=20000)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    fast = args.fast_root.resolve()
    if not (fast/'fastunknot'/'planar.py').is_file():
        ap.error('--fast-root must contain fastunknot/planar.py')
    if args.random_triples < 0 or args.max_crossings < 1 or args.max_objects < 1:
        ap.error('invalid work limit')
    sys.path.insert(0, str(fast))
    from fastunknot.planar import Planar
    rng = random.Random(20261007)
    report = {'source_hashes': {}, 'matching_comparisons': 0,
              'positive_genus_skips': 0, 'scan_examples': [], 'status': 'running'}
    for name, expected in AUDITED.items():
        actual = blob_sha(fast/'fastunknot'/name)
        report['source_hashes'][name] = {'actual': actual, 'audited': expected,
                                         'matches_audited': actual == expected}
    for m in range(4):
        alg = Planar()
        ids = [alg.intern(x) for x in matchings(tuple(range(2*m)))]
        for a,b,c in itertools.product(ids, repeat=3):
            plan = alg.compose_plan(a,b,c)
            if plan is None:
                report['positive_genus_skips'] += 1
                continue
            kernel = ComponentPlan(plan[0])
            for f in range(1 << (1 << kernel.dim.left)):
                for g in range(1 << (1 << kernel.dim.right)):
                    assert kernel.compose(f,g) == alg.compose(a,b,c,f,g)
                    report['matching_comparisons'] += 1
    alg = Planar()
    ids = [alg.intern(x) for x in matchings(tuple(range(12)))]
    for _ in range(args.random_triples):
        a,b,c = (rng.choice(ids) for _ in range(3))
        plan = alg.compose_plan(a,b,c)
        if plan is None:
            report['positive_genus_skips'] += 1
            continue
        kernel = ComponentPlan(plan[0])
        f,g = rng.getrandbits(1 << kernel.dim.left), rng.getrandbits(1 << kernel.dim.right)
        assert kernel.compose(f,g) == alg.compose(a,b,c,f,g)
        report['matching_comparisons'] += 1
    alg = Planar()
    a,b,c = map(alg.intern, zipper_triple(5,2))
    adapter = ComponentAlgebra(alg)
    for _ in range(30):
        f,g = rng.getrandbits(1024), rng.getrandbits(1024)
        assert adapter.compose(a,b,c,f,g) == alg.compose(a,b,c,f,g)
        report['matching_comparisons'] += 1
    report['adapter_stats'] = adapter.kernel_stats
    if args.scan_examples:
        from fastunknot.scan_fast import FastScan
        from fastunknot.geometry import ScanLimit
        for path in sorted((fast/'examples').glob('*.json')):
            data = json.loads(path.read_text())
            pd = data.get('pd')
            if not pd or len(pd) > args.max_crossings:
                continue
            row = {'name': path.name, 'crossings': len(pd)}
            try:
                scanners = [FastScan(max_objects=args.max_objects) for _ in range(2)]
                scanners[1].algebra = ComponentAlgebra(scanners[1].algebra,
                                                       check=scanners[1]._check)
                for slots in pd:
                    for scanner in scanners:
                        scanner.add_crossing(tuple(slots))
                        scanner.check_d_squared()
                assert scanners[0].points == scanners[1].points == frozenset()
                ranks = [scanner.ranks_by_degree() for scanner in scanners]
                assert ranks[0] == ranks[1]
                assert scanners[0].total_rank() == scanners[1].total_rank()
                row.update(status='equal', unreduced_ranks=ranks[0],
                           kernel_stats=scanners[1].algebra.kernel_stats)
            except ScanLimit as exc:
                row.update(status='budget_exhausted_not_a_verdict', detail=str(exc))
            report['scan_examples'].append(row)
    report['status'] = 'all completed comparisons equal'
    text = json.dumps(report, indent=2)+'\n'
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end='')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
