"""Reproduce paired incidence-planner timings and exact work counts.

These are abstract matrix kernels, not end-to-end knot-recognition timings.
The unchanged comparator is the pinned native core_handlebody module, retained
in baseline/.  Source construction, verification and file output are untimed.
"""

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import platform
import statistics
import sys
import time


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'code'))
from column_peeling import column_peeling_plan
from column_peeling_verify import verify_column_peeling_certificate


BASELINE = ROOT / 'baseline' / 'core_handlebody_7046006.py'
spec = importlib.util.spec_from_file_location('pinned_core_handlebody', BASELINE)
native = importlib.util.module_from_spec(spec)
spec.loader.exec_module(native)


def source(family, size):
    if family == 'rectangular_chain':
        return {r: {r: 1, r + 1: 1} for r in range(size)}
    if family == 'rectangular_fan':
        return {r: {r: 1, size: 1 << 256} for r in range(size)}
    if family == 'cyclic_stopping_core':
        return {r: {r: 1, (r + 1) % size: 1} for r in range(size)}
    raise ValueError('unknown benchmark family')


def timed(function, counts):
    start = time.perf_counter_ns()
    value = function(counts)
    return time.perf_counter_ns() - start, value


def measure(family, size, rounds):
    counts = source(family, size)
    a_times, b_times, aa_first, aa_second, verify_times = [], [], [], [], []
    expected = family != 'cyclic_stopping_core'
    for iteration in range(rounds):
        if iteration % 2:
            b, new = timed(column_peeling_plan, counts)
            a, old = timed(native.capped_cancellation_plan, counts)
        else:
            a, old = timed(native.capped_cancellation_plan, counts)
            b, new = timed(column_peeling_plan, counts)
        a1, _ = timed(native.capped_cancellation_plan, counts)
        a2, _ = timed(native.capped_cancellation_plan, counts)
        started = time.perf_counter_ns()
        assert verify_column_peeling_certificate(counts, new['certificate'])
        verify_times.append(time.perf_counter_ns() - started)
        assert (not old['remaining_rows']) == expected
        assert (new['status'] == 'COMPLETE') == expected
        a_times.append(a); b_times.append(b)
        aa_first.append(a1); aa_second.append(a2)
    median = statistics.median
    return dict(family=family, rows=size, columns=size + int(expected),
                source_nonzeros=2 * size, rounds=rounds,
                complete=expected,
                old_cancellations=len(old['cancellations']),
                new_cancellations=len(new['cancellations']),
                baseline_stats=old['stats'], new_stats=new['stats'],
                baseline_ns=a_times, new_ns=b_times,
                aa_first_ns=aa_first, aa_second_ns=aa_second,
                verification_ns=verify_times,
                median_baseline_ms=median(a_times) / 1e6,
                median_new_ms=median(b_times) / 1e6,
                median_verification_ms=median(verify_times) / 1e6,
                ratio_baseline_over_new=median(a_times) / median(b_times),
                ratio_aa=median(aa_first) / median(aa_second))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--sizes', type=int, nargs='+', default=[32, 128, 512])
    parser.add_argument('--rounds', type=int, default=7)
    parser.add_argument('--output', type=Path,
                        default=ROOT / 'results' / 'column_peeling_benchmark.json')
    arguments = parser.parse_args()
    if arguments.rounds < 1 or any(size < 3 for size in arguments.sizes):
        parser.error('positive rounds and sizes at least three are required')
    records = [measure(family, size, arguments.rounds)
               for family in ('rectangular_chain', 'rectangular_fan',
                              'cyclic_stopping_core')
               for size in arguments.sizes]
    report = dict(scope='abstract incidence planner kernels; not knot recognition',
                  python=sys.version, platform=platform.platform(),
                  baseline_commit='704600626606a9097cfd89d4e3d2bbc63c8dd1cb',
                  baseline_path='Topology/UnknotRecognition/fast/fastunknot/core_handlebody.py',
                  baseline_sha256=hashlib.sha256(BASELINE.read_bytes()).hexdigest(),
                  baseline_method='capped_cancellation_plan',
                  new_method='column_peeling_plan',
                  source_construction_timed=False, certificate_replay_timed_separately=True,
                  records=records)
    arguments.output.parent.mkdir(parents=True, exist_ok=True)
    arguments.output.write_text(json.dumps(report, indent=2) + '\n')
    for row in records:
        print(f"{row['family']:24s} {row['rows']:5d} "
              f"old={row['median_baseline_ms']:.3f}ms "
              f"new={row['median_new_ms']:.3f}ms "
              f"ratio={row['ratio_baseline_over_new']:.2f} "
              f"A/A={row['ratio_aa']:.3f}")


if __name__ == '__main__':
    main()
