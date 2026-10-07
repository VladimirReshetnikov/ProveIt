#!/usr/bin/env python3
"""Paired numerical-kernel benchmark; this does not time knot recognition."""
from __future__ import annotations
import argparse
import gc
import json
import platform
import random
import statistics
import sys
import time
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT / 'code'), str(ROOT / 'tests')]
from component_kernel import ComponentPlan
from reference_planar import ReferencePlanar, component
from fixtures import zipper_triple


def make_baseline(components):
    # Exact repository composition loop via its excerpt, with a fresh per-call
    # numerical memo. Geometry is precompiled for both A and B.
    ref = ReferencePlanar()
    ref.compose_plans[(0, 0, 0)] = (components, {})
    def run(f, g):
        ref.compose_plans[(0, 0, 0)] = (components, {})
        return ref.compose(0, 0, 0, f, g)
    return run


def timed(fn, f, g, repetitions):
    start = time.perf_counter_ns()
    answer = None
    for _ in range(repetitions):
        answer = fn(f, g)
    return (time.perf_counter_ns() - start) / (1e9 * repetitions), answer


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--rounds', type=int, default=11)
    args = ap.parse_args()
    if args.rounds < 3:
        ap.error('at least three rounds are required')
    rng = random.Random(20261007)
    cases = []
    for k in (4, 6, 8, 10):
        plan = tuple(component(1 << j, 1 << j, 1 << j, 0) for j in range(k))
        cases.append((f'dense_endomorphism_{k}', plan, 'dense', 'real matching endomorphism'))
    plan = tuple(component(1 << j, 1 << j, 1 << j, 0) for j in range(10))
    cases.append(('sparse_endomorphism_10', plan, 'sparse', 'real matching endomorphism'))
    ref = ReferencePlanar()
    ids = tuple(map(ref.intern, zipper_triple(5, 2)))
    plan = ref.compose_plan(*ids)[0]
    assert plan == (component(31, 31, 1, 0), component(992, 992, 2, 0))
    cases.append(('dense_two_component_10_10_2', plan, 'dense',
                  'real 36-endpoint planar zipper triple, d=5, blocks=2'))
    results = []
    for name, components, density, scope in cases:
        start = time.perf_counter_ns()
        fast = ComponentPlan(components)
        compile_s = (time.perf_counter_ns() - start) / 1e9
        old = make_baseline(components)
        def operand(r):
            n = 1 << r
            if density == 'sparse':
                return sum(1 << j for j in rng.sample(range(n), 4))
            return rng.getrandbits(n) | 1
        f, g = operand(fast.dim.left), operand(fast.dim.right)
        pilot, answer = timed(old, f, g, 1)
        assert fast.compose(f, g) == answer
        reps = max(1, min(20, int(0.001 / max(pilot, 1e-9))))
        records = []
        for round_id in range(args.rounds):
            f, g = operand(fast.dim.left), operand(fast.dim.right)
            expected = old(f, g)
            assert fast.compose(f, g) == expected
            gc.collect()
            # ABAB / BABA alternation, with two independent A measurements.
            runs = (('A1', old), ('B1', fast.compose), ('A2', old), ('B2', fast.compose))
            if round_id % 2:
                runs = (runs[1], runs[0], runs[3], runs[2])
            row = {'round': round_id, 'pairs': f.bit_count() * g.bit_count()}
            for label, fn in runs:
                seconds, answer = timed(fn, f, g, reps)
                assert answer == expected
                row[label] = seconds
            row['new_old'] = (row['B1'] + row['B2']) / (row['A1'] + row['A2'])
            row['AA'] = row['A2'] / row['A1']
            records.append(row)
        oldmed = statistics.median((r['A1'] + r['A2']) / 2 for r in records)
        newmed = statistics.median((r['B1'] + r['B2']) / 2 for r in records)
        ratios = sorted(r['new_old'] for r in records)
        aa = sorted(r['AA'] for r in records)
        # Full observed ranges are not confidence intervals.
        result = {'case': name, 'scope': scope, 'dimensions': fast.dim.__dict__,
                  'domain_entries': fast.dim.domain_entries,
                  'plan_compilation_seconds': compile_s, 'repetitions': reps,
                  'median_old_seconds': oldmed, 'median_new_seconds': newmed,
                  'median_paired_new_old': statistics.median(ratios),
                  'median_paired_speedup': 1 / statistics.median(ratios),
                  'paired_ratio_observed_range': [min(ratios), max(ratios)],
                  'AA_observed_range': [min(aa), max(aa)],
                  'AA_median': statistics.median(aa),
                  'median_input_pairs': statistics.median(r['pairs'] for r in records),
                  'records': records}
        results.append(result)
        print(f"{name:34s} old={oldmed*1e3:10.4f} ms new={newmed*1e3:10.4f} ms "
              f"paired speedup={result['median_paired_speedup']:.2f}x", flush=True)
    report = {'python': sys.version, 'platform': platform.platform(), 'rounds': args.rounds,
              'seed': 20261007,
              'protocol': 'precompiled topology; component quotient tables precompiled and separately timed; '
                          'fresh numerical memo for each baseline invocation; no new numerical-result cache; '
                          'alternating ABAB/BABA and A/A controls; all outputs checked',
              'scope': 'microbenchmarks only; NOT full scanner or recognizer speedups',
              'cases': results}
    (ROOT / 'results' / 'benchmark.json').write_text(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    main()
