"""Reproduce exact local contraction and complete-scanner comparisons."""
import argparse
import json
from pathlib import Path
import random
import time
from collections import Counter
import sys

PACKAGE_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(PACKAGE_ROOT / 'implementation' / 'fast'))

from fastunknot import Diagram
from fastunknot.diagram import DiagramError
from fastunknot.scan_fast import FastScan
from fastunknot.geometry import ScanLimit
from fastunknot.ordering import best_scan_order
from fastunknot.graded_transfer import GradedTransferScan, GradedAdaptiveScan, transfer, check_certificate
from synthetic import dense_radical_control, long_transfer_control


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--examples', type=Path,
                        default=PACKAGE_ROOT / 'implementation' / 'fast' / 'examples')
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_name('validation_reproduced.json'))
    parser.add_argument('--random', type=int, default=80)
    args = parser.parse_args()
    seed, start = 2026100802, time.perf_counter()
    rng = random.Random(seed)
    cases = [(name, Diagram.from_json(json.loads((args.examples / (name + '.json')).read_text())))
             for name in ('trefoil', 'figure_eight', 'hard_unknot_8', 'conway',
                          'kinoshita_terasaka', 'torus_3_5')]
    accepted = 0
    while accepted < args.random:
        strands = rng.randrange(2, 6)
        word = [rng.choice((-1,1))*rng.randrange(1, strands)
                for _ in range(rng.randrange(1,12))]
        try:
            diagram = Diagram.from_braid(strands, word)
        except DiagramError:
            continue
        cases.append((f'random_{accepted}', diagram))
        accepted += 1
    rows, stages = [], 0
    for name, diagram in cases:
        orders = [list(range(diagram.crossings)), best_scan_order(diagram.pd)]
        shuffled = orders[0][:]
        rng.shuffle(shuffled)
        orders.append(shuffled)
        for order in orders:
            a = FastScan(max_objects=50000)
            b = GradedTransferScan(certificates=True, max_objects=50000)
            c = GradedAdaptiveScan(certificates=True, max_objects=50000)
            d = GradedTransferScan(max_objects=50000)
            for j in order:
                a.add_crossing(diagram.pd[j])
                b.add_crossing(diagram.pd[j])
                c.add_crossing(diagram.pd[j])
                d.add_crossing(diagram.pd[j])
                b.check_d_squared()
                stages += 1
            if a.ranks_by_degree() != b.ranks_by_degree() or a.ranks_by_degree() != c.ranks_by_degree():
                raise ArithmeticError('scan homology mismatch')
            quantum_counts = lambda scan: Counter((scan.deg[v], scan.qshift[v])
                                                  for v,m in enumerate(scan.mid) if m is not None)
            if quantum_counts(b) != quantum_counts(c) or quantum_counts(b) != quantum_counts(d):
                raise ArithmeticError('quantum-resolved rank mismatch')
            rows.append(dict(name=name, pd=diagram.pd, order=order,
                             by_degree=a.ranks_by_degree()))
    controls = []
    for size in (1,2,3,5,10,20,32):
        scan = dense_radical_control(size)
        result = transfer(scan, certificates=True)
        identities = check_certificate(scan, result)
        assert result['out'] == [{1:2},{}]
        FastScan.eliminate(scan, update_budget=1)
        resumed = transfer(scan, certificates=True)
        check_certificate(scan, resumed)
        assert resumed['out'] == [{1:2},{}]
        controls.append(dict(kind='dense nonzero radical', size=size, identities=identities))
    for length in range(1,9):
        scan = long_transfer_control(length)
        result = transfer(scan, certificates=True)
        identities = check_certificate(scan,result)
        assert result['out'] == [{1:1 << ((1 << length)-1)}, {}]
        controls.append(dict(kind='long perturbation chain', length=length, identities=identities))
    scan = long_transfer_control(2)
    matching = scan.algebra.intern(((0,1),))
    scan.mid = [matching]*scan.live
    scan.points = frozenset((0,1))
    for a,row in enumerate(scan.out):
        for b,value in list(row.items()):
            if value != 1:
                row[b] = 2
    result = transfer(scan,certificates=True)
    check_certificate(scan,result)
    assert result['out'] == [{},{}]
    controls.append(dict(kind='source-band rejection of x squared', status='passed'))
    scan = dense_radical_control(32)
    scan.max_transfer_objects = 0
    scan.eliminate()
    assert scan.live == 2 and scan.stats['graded_transfer_capacity_fallbacks'] == 1
    controls.append(dict(kind='capacity fallback retains nonzero radical map',status='passed'))
    scan = dense_radical_control(32)
    scan.deadline = time.monotonic()-1
    try:
        scan.eliminate()
    except ScanLimit:
        pass
    else:
        raise ArithmeticError('expired deadline failed to propagate')
    controls.append(dict(kind='expired deadline propagates ScanLimit',status='passed'))
    result = dict(status='passed', seed=seed, diagrams=len(cases), scans=len(rows),
                  modes_per_scan=4, quantum_resolved_comparison=True,
                  exact_stage_contractions=stages, identities_per_contraction=8,
                  controls=controls, seconds=time.perf_counter()-start, data=rows)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('data','controls')},indent=2))


if __name__ == '__main__':
    main()
