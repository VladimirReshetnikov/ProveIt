"""Paired kernel and complete raw-scanner measurements with an A/A control.

The packaged implementation and controls are resolved relative to this file.
Construction, validation, order selection and cloning are excluded. No
recognition filter is timed. Certificates are validated separately.
"""
import argparse
import hashlib
import subprocess
import copy
import gc
import json
from pathlib import Path
import platform
import random
from statistics import median
import time
import sys

PACKAGE_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PACKAGE_ROOT))

from fastunknot import Diagram
from fastunknot.ordering import best_scan_order
from fastunknot.scan_fast import FastScan
from fastunknot.graded_transfer import GradedTransferScan, GradedAdaptiveScan
from synthetic import dense_radical_control


def summarize(samples):
    return dict(baseline_over_transfer=median(row['baseline'] / row['transfer'] for row in samples),
                baseline_over_adaptive=median(row['baseline'] / row['adaptive'] for row in samples),
                aa_ratio=median(row['baseline'] / row['aa'] for row in samples),
                median_seconds={key: median(row[key] for row in samples)
                                for key in ('baseline', 'aa', 'transfer', 'adaptive')})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--examples', type=Path,
                        default=PACKAGE_ROOT / 'examples')
    parser.add_argument('--output', type=Path,
                        required=True)
    parser.add_argument('--rounds', type=int, default=7)
    args = parser.parse_args()
    rng = random.Random(2026100804)
    modes = dict(baseline=FastScan, aa=FastScan,
                 transfer=GradedTransferScan, adaptive=GradedAdaptiveScan)
    rows = []
    for name in ('hard_unknot_8', 'conway', 'kinoshita_terasaka', 'unknot_braid40', 'stress_braid5_36'):
        diagram = Diagram.from_json(json.loads((args.examples / (name + '.json')).read_text()))
        order = best_scan_order(diagram.pd)
        expected = None
        stats, samples = {}, []
        calls = 1 if name == 'stress_braid5_36' else 8
        for round_index in range(-1, args.rounds):
            arm_order = list(modes)
            rng.shuffle(arm_order)
            times = {}
            for mode in arm_order:
                prepared = [modes[mode](max_objects=50000) for _ in range(calls)]
                gc.collect()
                gc.disable()
                start = time.perf_counter()
                try:
                    for scan in prepared:
                        for index in order:
                            scan.add_crossing(diagram.pd[index])
                    times[mode] = (time.perf_counter() - start) / calls
                finally:
                    gc.enable()
                for scan in prepared:
                    actual = scan.ranks_by_degree()
                    if expected is not None and expected != actual:
                        raise ArithmeticError('whole-scan rank mismatch')
                    expected = actual
                stats[mode] = dict(scan.stats)
            if round_index >= 0:
                samples.append(times)
        row = dict(kind='whole raw scan', name=name, pd=diagram.pd, order=order,
                   calls_per_sample=calls, by_degree=expected,
                   samples=samples, stats=stats, **summarize(samples))
        rows.append(row)
        print(json.dumps({k: v for k, v in row.items() if k not in ('pd', 'order', 'by_degree', 'samples', 'stats')}), flush=True)
    for size in (16, 32, 64, 128):
        template = dense_radical_control(size)
        stats, samples = {}, []
        calls = max(2, 256 // size)
        for round_index in range(-1, args.rounds):
            arm_order = list(modes)
            rng.shuffle(arm_order)
            times = {}
            for mode in arm_order:
                prepared = [copy.deepcopy(template) for _ in range(calls)]
                gc.collect()
                gc.disable()
                start = time.perf_counter()
                try:
                    for scan in prepared:
                        modes[mode].eliminate(scan)
                    times[mode] = (time.perf_counter() - start) / calls
                finally:
                    gc.enable()
                for scan in prepared:
                    if scan.live != 2:
                        raise ArithmeticError('wrong minimal multiplicity in kernel control')
                    values = [value for row in scan.out if row for value in row.values()]
                    if values != [2]:
                        raise ArithmeticError('lost nonzero radical minimal map')
                stats[mode] = dict(scan.stats)
            if round_index >= 0:
                samples.append(times)
        row = dict(kind='synthetic graded kernel, not a diagram', size=size,
                   objects=4*size+2, survivors=2, minimal_differential='x',
                   calls_per_sample=calls, samples=samples, stats=stats, **summarize(samples))
        rows.append(row)
        print(json.dumps({k: v for k, v in row.items() if k not in ('samples', 'stats')}), flush=True)
    result = dict(seed=2026100804, rounds=args.rounds, python=platform.python_version(),
                  platform=platform.platform(),
                  measurement='per-call operation time; setup excluded; cyclic GC disabled only while timing',
                  data=rows)
    result['repository_parent_commit'] = subprocess.check_output(['git','rev-parse','HEAD'], cwd=PACKAGE_ROOT, text=True).strip()
    result['source_sha256'] = {name: hashlib.sha256((PACKAGE_ROOT/'fastunknot'/name).read_bytes()).hexdigest() for name in ('graded_transfer.py','scan_fast.py','planar.py')}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
