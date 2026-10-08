#!/usr/bin/env python3
"""Diagnostic runner for a LOCAL ProveIt fast/ checkout. Not run in this bundle.

It observes every proper prefix, then completes the original scanner and checks
all lower bounds against its reduced rank. This is not a production recognizer:
the read-only observer currently has no interruptible determinant deadline.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import random
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from detshadow.diagram import from_braid
from detshadow.continuation import observe_scan
from detshadow.cube import reduced_homology


def git_blob_sha(path: Path) -> str:
    data = path.read_bytes()
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--fast-root', type=Path, required=True, help='Path to ProveIt/Topology/UnknotRecognition/fast')
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--random', type=int, default=20)
    ap.add_argument('--max-objects', type=int, default=50000)
    args = ap.parse_args()
    if not (args.fast_root / 'fastunknot' / 'scan_fast.py').is_file():
        ap.error('--fast-root does not contain fastunknot/scan_fast.py')
    if args.random < 0 or args.max_objects < 1:
        ap.error('invalid diagnostic budget')
    sys.path.insert(0, str(args.fast_root.resolve()))
    from fastunknot.scan_fast import FastScan
    from fastunknot.component_scan import ComponentScan
    from fastunknot.geometry import ScanLimit
    cases = [('trefoil', from_braid(2, [1]*3)),
             ('figure_eight', from_braid(3, [1,-2]*2)),
             ('torus_3_5', from_braid(3, [1,2]*5)),
             ('cancelled_word_unknot', from_braid(3, [1,2,1,-1,2,-2]))]
    rng = random.Random(20261007)
    while len(cases) < 4 + args.random:
        strands = rng.randrange(2,5)
        word = [rng.choice((-1,1))*rng.randrange(1,strands) for _ in range(rng.randrange(1,9))]
        d = from_braid(strands,word)
        if d.pd and not d.free_circles and d.orientation_data()[0] == 1:
            cases.append((f'random_{len(cases)-4}',d))
    records = []
    for name, d in cases:
        if d.orientation_data()[0] != 1:
            raise ValueError(f'{name}: not a knot')
        n = len(d.pd)
        natural = list(range(n))
        shuffled = natural.copy()
        rng.shuffle(shuffled)
        for order in (natural, shuffled):
            root = order[-1]
            marked_label = d.pd[root][0]
            for scanner in (FastScan, ComponentScan):
                scan = scanner(max_objects=args.max_objects, shape_cache=False)
                rows = []
                try:
                    rows.append(observe_scan(scan, [d.pd[j] for j in order], marked_label=marked_label))
                    for i,j in enumerate(order):
                        scan.add_crossing(d.pd[j])
                        scan.check_d_squared()
                        if i+1 < n:
                            rows.append(observe_scan(scan, [d.pd[k] for k in order[i+1:]], marked_label=marked_label))
                    if scan.points or any(scan.out[v] for v,a in enumerate(scan.mid) if a is not None):
                        raise ArithmeticError('completed scan is not reduced and closed')
                    rank = (scan.total_rank() if isinstance(scan,ComponentScan)
                            else sum(a is not None for a in scan.mid))
                    if rank % 2:
                        raise ArithmeticError('odd unreduced knot rank')
                    bounds = [r['reduced_rank_lower_bound'] for r in rows]
                    if any(a > b for a,b in zip(bounds,bounds[1:])) or any(b > rank//2 for b in bounds):
                        raise ArithmeticError('continuation inequality or monotonicity failed')
                    independent = reduced_homology(d)['rank'] if n <= 10 else None
                    if independent is not None and independent != rank//2:
                        raise ArithmeticError('independent reduced cube disagrees')
                    records.append(dict(name=name, pd=d.pd, order=order, scanner=scanner.__name__,
                                        status='checked', reduced_rank=rank//2, independent_rank=independent,
                                        observations=rows))
                except ScanLimit as exc:
                    records.append(dict(name=name, order=order, scanner=scanner.__name__,
                                        status='UNKNOWN', reason=str(exc), observations=rows))
    hashes = {name:git_blob_sha(args.fast_root/'fastunknot'/name)
              for name in ('scan_fast.py','component_scan.py','planar.py')}
    result = dict(scope='local upstream diagnostic, not a speed benchmark', source_blobs=hashes,
                  records=records, all_completed=all(r['status']=='checked' for r in records))
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'runs':len(records),'all_completed':result['all_completed']}))

if __name__ == '__main__':
    main()
