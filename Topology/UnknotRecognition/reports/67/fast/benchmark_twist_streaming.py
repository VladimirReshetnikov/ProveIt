"""Paired full-homology timings with A/A control and separate memory tracing.

Every arm performs a fresh computation on the identical signed-run input.
The original backend, an identical original-backend control, and the streamed
backend all return and compare every homological degree and boundary rank.
When the closure has one component an additional early-decision arm reports
only a verdict and a certified partial rank lower bound.  No simplification,
Alexander/determinant filter, scanner selection, or cached homology is used.

Tracemalloc measurements are SEPARATE executions outside the timed rounds.
They report peak newly traced Python allocations, not peak process RSS.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict
import gc
import json
from pathlib import Path
import platform
import random
import statistics
import sys
from time import perf_counter
import tracemalloc

# Works both from a checkout's fast/ and from this package's tools/ directory.
_fast_directory = Path(__file__).resolve().parents[1] / 'fast'
if (_fast_directory / 'fastunknot').is_dir():
    sys.path.insert(0, str(_fast_directory))

from fastunknot.twist import Budget, Run, components, homology as original_homology
from fastunknot.twist.streaming import StreamBudget, homology, recognize


CASES = (
    ('two_strand_801', 2, ((1, 801),)),
    ('two_strand_10001', 2, ((1, 10001),)),
    ('opposite_blocks_41_40', 2, ((1, 41), (1, -40))),
    ('mixed_signed_3_strands', 3, ((1, 5), (2, -4), (1, 3), (2, -2))),
    ('conjugated_unknot_15', 3, ((1, 15), (2, 1), (1, -14))),
    ('mixed_four_strand_31', 4, ((1, 31), (2, 1), (3, -1), (2, 1),
                                  (3, 1), (1, 1), (2, -1))),
    ('weaving_3_4', 3, ((1, 1), (2, -1)) * 4),
    # Existing repository benchmark case, preserved verbatim by signed runs.
    ('morton_four_strand', 4, ((3, -2), (2, 1), (3, -1), (2, 1),
                              (1, 3), (2, -1), (1, 1), (2, -1))),
)


def signature(result):
    return tuple(result[k] for k in (
        'reduced_rank', 'by_degree', 'chain_dimensions', 'boundary_ranks'))


def traced_peak(call, expected, *, decision=False):
    gc.collect()
    tracemalloc.start()
    result = call()
    retained, peak = tracemalloc.get_traced_memory()
    tracemalloc.stop()
    if decision:
        assert result['status'] == ('UNKNOT' if expected[0] == 1 else 'KNOTTED')
    else:
        assert signature(result) == expected
    return {'retained_bytes': retained, 'peak_bytes': peak}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rounds', type=int, default=7)
    parser.add_argument('--batch', type=int, default=5,
                        help='fresh repetitions averaged within each arm and round')
    parser.add_argument('--case', action='append', default=[], help='select named cases')
    args = parser.parse_args()
    if args.rounds < 1:
        parser.error('--rounds must be positive')
    if args.batch < 1:
        parser.error('--batch must be positive')
    selected = [case for case in CASES if not args.case or case[0] in args.case]
    if not selected or any(name not in {c[0] for c in CASES} for name in args.case):
        parser.error('unknown or empty case selection')
    seed = 2026100801
    rng = random.Random(seed)
    baseline_budget = Budget(seconds=120)
    stream_budget = StreamBudget(seconds=120)
    rows = []
    for name, strands, encoded_runs in selected:
        runs = tuple(Run(*r) for r in encoded_runs)
        calls = {
            'original': lambda: original_homology(strands, runs, budget=baseline_budget),
            'control': lambda: original_homology(strands, runs, budget=baseline_budget),
            'stream': lambda: homology(strands, runs, budget=stream_budget),
        }
        if components(strands, runs) == 1:
            calls['decision'] = lambda: recognize(strands, runs, budget=stream_budget)
        baseline = original_homology(strands, runs, budget=baseline_budget, check_d2=True)
        expected = signature(baseline)
        del baseline
        checked = homology(strands, runs, budget=stream_budget, check_d2=True)
        assert signature(checked) == expected, name
        del checked
        # Warm all arms once.  Each still creates fresh state and caches.
        for arm, call in calls.items():
            result = call()
            if arm == 'decision':
                assert result['status'] == ('UNKNOT' if expected[0] == 1 else 'KNOTTED')
            else:
                assert signature(result) == expected, (name, arm)
        del result
        samples = []
        latest = {}
        for _ in range(args.rounds):
            order = list(calls)
            rng.shuffle(order)
            sample = {'order': order}
            for arm in order:
                gc.collect()
                durations = []
                for _ in range(args.batch):
                    started = perf_counter()
                    result = calls[arm]()
                    durations.append(perf_counter() - started)
                    # Validation is outside every recorded duration.
                    if arm == 'decision':
                        assert result['status'] == (
                            'UNKNOT' if expected[0] == 1 else 'KNOTTED')
                    else:
                        assert signature(result) == expected, (name, arm)
                    latest[arm] = result
                sample[arm] = statistics.mean(durations)
                sample[arm + '_repetitions'] = durations
            samples.append(sample)
        memory = {
            arm: traced_peak(call, expected, decision=arm == 'decision')
            for arm, call in calls.items() if arm != 'control'
        }
        medians = {arm: statistics.median(s[arm] for s in samples) for arm in calls}
        row = {
            'name': name, 'strands': strands, 'runs': encoded_runs,
            'components': components(strands, runs), 'samples': samples,
            'median_seconds': medians,
            'median_paired_original_over_stream': statistics.median(
                s['original'] / s['stream'] for s in samples),
            'median_paired_aa': statistics.median(
                s['original'] / s['control'] for s in samples),
            'tracemalloc_separate_runs': memory,
            'peak_allocation_ratio_original_over_stream': (
                memory['original']['peak_bytes'] / memory['stream']['peak_bytes']),
            'original_result': latest['original'],
            'stream_result': latest['stream'],
            'decision_result': latest.get('decision'),
        }
        rows.append(row)
        print(name, 'rank', expected[0], 'time ratio',
              round(row['median_paired_original_over_stream'], 3),
              'A/A', round(row['median_paired_aa'], 3),
              'peak allocation ratio',
              round(row['peak_allocation_ratio_original_over_stream'], 3), flush=True)
        # Checkpoint after each completed case, using the same final format.
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps({
            'repository_parent_commit': '8126705bcb003b1082f117c87e4af7136b1d2c43',
            'python': platform.python_version(), 'platform': platform.platform(),
            'seed': seed, 'rounds': args.rounds, 'timing_scope': __doc__,
            'repetitions_per_arm_per_round': args.batch,
            'baseline_budget': asdict(baseline_budget),
            'stream_budget': asdict(stream_budget), 'cases': rows,
        }, indent=2) + '\n')


if __name__ == '__main__':
    main()
