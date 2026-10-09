"""Look for whole single-matching blocks in actual production scans.

This bypasses recognition filters and scans to closure or a recorded limit.
It does not fabricate a block or interpret a missed opportunity as a theorem.
"""
import argparse
import hashlib
import json
from pathlib import Path
import random
import sys
from time import monotonic

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'fast'))
from fastunknot import Diagram
from fastunknot.component_scan import components
from fastunknot.closure_scan import certify_block, complete_matching
from fastunknot.geometry import ScanLimit
from fastunknot.ordering import best_scan_order
from fastunknot.scan_fast import FastScan


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--attempts', type=int, default=1200)
    args = parser.parse_args()
    rng = random.Random(2801)
    records, witnesses = [], []
    totals = dict(validated=0, scans=0, completed=0, limited=0, stages=0,
                  singletons=0, nonsingleton_jet=0, nonsingleton_pure=0)
    for _ in range(args.attempts):
        strands = rng.randrange(2, 6)
        word = [rng.choice((-1, 1)) * rng.randrange(1, strands)
                for _ in range(rng.randrange(1, 15))]
        try:
            diagram = Diagram.from_braid(strands, word)
        except ValueError:
            continue
        totals['validated'] += 1
        shuffled = list(range(diagram.crossings))
        rng.shuffle(shuffled)
        for label, order in [('random', shuffled), ('width', best_scan_order(diagram.pd))]:
            scan = FastScan(max_objects=3000, deadline=monotonic() + .25)
            stages, observed = 0, 0
            try:
                for stage, index in enumerate(order, 1):
                    scan.add_crossing(diagram.pd[index])
                    stages += 1
                    if stage == len(order):
                        continue
                    for group in components(scan):
                        data = certify_block(scan, group, scan._check)
                        if data is None:
                            continue
                        totals['singletons' if len(group) == 1 else 'nonsingleton_jet'] += 1
                        if len(group) > 1:
                            totals['nonsingleton_pure'] += int(data['pure'])
                            residual, count = complete_matching(
                                [diagram.pd[i] for i in order[stage:]],
                                scan.algebra.pairs[data['matching']], scan._check)
                            observed += 1
                            witnesses.append(dict(strands=strands, word=word, order=order,
                                                  stage=stage, block=data, residual=residual,
                                                  completion_components=count))
                status = 'complete'
                totals['completed'] += 1
            except ScanLimit:
                status = 'limited'
                totals['limited'] += 1
            totals['scans'] += 1
            totals['stages'] += stages
            records.append(dict(strands=strands, word=word, policy=label, order=order,
                                status=status, stages=stages, nonsingleton=observed))
    sources = [Path(__file__), ROOT/'fast/fastunknot/closure_scan.py',
               ROOT/'fast/fastunknot/scan_fast.py', ROOT/'fast/fastunknot/planar.py']
    out = dict(seed=2801, attempts=args.attempts, limits=dict(seconds=.25, max_objects=3000),
               totals=totals, records=records, witnesses=witnesses,
               scope=__doc__, sources={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                                       for p in sources})
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2)+'\n')
    print(json.dumps(totals))


if __name__ == '__main__':
    main()
