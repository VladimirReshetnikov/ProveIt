"""Paired complete native calls, with matching result obligations and A/A controls.

Run after all other experiment processes have stopped. No Regina oracle is
timed. Input JSON loading, module imports and output serialization are excluded;
source reconstruction is included. Verified tasks include discovery of a fresh
certificate and its independent replay on every repetition.
"""

import argparse
import json
from pathlib import Path
import platform
import statistics
import sys
import time

from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from normal_cut_saturation import normal_cut_saturation
from normal_cut_saturation_verify import verify_normal_cut_saturation


ROOT = Path(__file__).resolve().parents[1]


def call(case, method, verified):
    raw, rows = case['triangulation'], case['coordinates']
    if method == 'pinned':
        answer = normal_cut_handlebodies(raw, rows, record_certificate=verified)
        if verified:
            assert verify_normal_cut_handlebodies(raw, rows, answer['certificate'])
    else:
        answer = normal_cut_saturation(raw, rows, record_certificate=verified,
                                       precheck_core=(method == 'precheck'))
        if verified:
            assert verify_normal_cut_saturation(raw, rows, answer['certificate'])
    return answer


def timed(case, method, verified):
    start = time.perf_counter_ns()
    result = call(case, method, verified)
    return time.perf_counter_ns() - start, result


def equivalent(a, b):
    assert a['status'] == b['status']
    if a['status'] == 'COMPLETE':
        assert a['census']['histogram'] == b['census']['histogram']
    else:
        # Different proof sizes are the purpose of the precheck: both declare
        # failure of this fixed raw model, without any topological negative.
        assert a['reason'] == 'full_raw_cancellation_obstructed'
        assert b['reason'] == 'original_core_raw_obstruction'


def measure(case, left, right, verified, rounds):
    a0, b0 = call(case, left, verified), call(case, right, verified)
    equivalent(a0, b0)
    a_times, b_times, a1_times, a2_times = [], [], [], []
    for i in range(rounds):
        if i % 2:
            b, rb = timed(case, right, verified)
            a, ra = timed(case, left, verified)
        else:
            a, ra = timed(case, left, verified)
            b, rb = timed(case, right, verified)
        a1, _ = timed(case, left, verified)
        a2, _ = timed(case, left, verified)
        equivalent(ra, rb)
        a_times.append(a)
        b_times.append(b)
        a1_times.append(a1)
        a2_times.append(a2)
    med = statistics.median
    return dict(id=case['id'], left=left, right=right,
                task='discovery_and_independent_replay' if verified else 'discovery',
                rounds=rounds, status=a0['status'],
                left_ns=a_times, right_ns=b_times,
                aa_first_ns=a1_times, aa_second_ns=a2_times,
                median_left_ms=med(a_times) / 1e6, median_right_ms=med(b_times) / 1e6,
                ratio_left_over_right=med(a_times) / med(b_times),
                ratio_aa=med(a1_times) / med(a2_times))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--rounds', type=int, default=7)
    parser.add_argument('--output', type=Path, default=ROOT / 'data/native_benchmark.json')
    args = parser.parse_args()
    if args.rounds < 1:
        parser.error('rounds must be positive')
    bank = json.loads((ROOT / 'data/native_corpus.json').read_text())['cases']
    tasks = [(i, 'pinned', 'saturated') for i in (0, 52, 98, 100)]
    tasks += [(i, 'saturated', 'precheck') for i in (3, 9, 20, 42)]
    records = []
    for i, left, right in tasks:
        for verified in (False, True):
            row = measure(bank[i], left, right, verified, args.rounds)
            records.append(row)
            print(f"{row['id']} {left}/{right} {row['task']}: "
                  f"{row['median_left_ms']:.3f}/{row['median_right_ms']:.3f} ms, "
                  f"ratio {row['ratio_left_over_right']:.3f}, A/A {row['ratio_aa']:.3f}",
                  flush=True)
    report = dict(python=sys.version, platform=platform.platform(),
                  source_revision='704600626606a9097cfd89d4e3d2bbc63c8dd1cb',
                  scope='Supplied normal-cut query tasks; not full knot recognition.',
                  source_reconstruction_timed=True, json_io_timed=False,
                  record_certificate_and_replay_in_verified_task=True,
                  isolation='Run sequentially after native audit and regression processes exited.',
                  records=records)
    args.output.write_text(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    main()
