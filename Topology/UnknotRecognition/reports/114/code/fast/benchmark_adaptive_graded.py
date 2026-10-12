"""Adaptive cancellation on dense *graded* synthetic two-term complexes.

All entries are scalar identities between equal matchings, with quantum shifts
zero. Construction is excluded from timing. These satisfy the recovered grading
constraint but are not asserted to occur during a supplied knot scan.
"""
import argparse
import json
from pathlib import Path
import platform
import random
import statistics
from time import perf_counter

from benchmark_residue import dense_two_term
from fastunknot.residue import AdaptiveScan
from fastunknot.scan_fast import FastScan


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rounds', type=int, default=7)
    args = parser.parse_args()
    rng = random.Random(2026100804)
    rows = []
    for size in (32, 64, 128, 256):
        samples, metrics = [], {}
        for _ in range(args.rounds):
            arms = ['standard', 'control', 'adaptive']
            rng.shuffle(arms)
            sample = dict(order=arms)
            for arm in arms:
                scan = dense_two_term(AdaptiveScan if arm == 'adaptive' else FastScan, size, graded=True)
                assert all(f == 1 and scan.mid[a] == scan.mid[b]
                           for a, row in enumerate(scan.out) for b, f in row.items())
                scan.check_d_squared()
                start = perf_counter()
                scan.eliminate()
                sample[arm] = perf_counter() - start
                assert scan.live == 1 and scan.ranks_by_degree() == {0: 1} and not any(scan.out)
                metrics[arm] = dict(scan.stats)
            samples.append(sample)
        row = dict(size=size, objects=2*size+1, samples=samples, stats=metrics,
                   median_speedup=statistics.median(s['standard']/s['adaptive'] for s in samples),
                   median_aa=statistics.median(s['standard']/s['control'] for s in samples))
        rows.append(row)
        print(size, round(row['median_speedup'], 3), round(row['median_aa'], 3), flush=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(dict(python=platform.python_version(), seed=2026100804,
        rounds=args.rounds, scope=__doc__, cases=rows), indent=2) + '\n')


if __name__ == '__main__':
    main()
