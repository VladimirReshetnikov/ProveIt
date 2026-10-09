#!/usr/bin/env python3
"""Paired raw-maintenance benchmark on PREVERIFIED supplied schedules.

Includes state initialization, every update, and the exact rank-one endpoint.
Excludes schedule discovery and independent replay (performed before timing).
The reference is a verbatim upstream updater on the standalone Arena, not the
complete fastunknot pipeline. Eager export is a deliberate workload ablation.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import platform
import random
import statistics
import sys
import time
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'src'))
from anchored_unknot import AnchoredState, replay
from anchored_unknot.fixtures import power_chain, power_star
from anchored_unknot.reference_update import apply_projection, native_witnesses


def make_case(name, rank, bits):
    source = power_star(rank, 1 << bits, duplicate=True) if name == 'star' else power_chain(rank, 1 << bits)
    state = AnchoredState(source)
    proof = state.run(max_pairs=1)
    assert replay(source, proof).rank_one_zero
    return source, state.steps


def anchored(source, batches, eager=False):
    state = AnchoredState(source)
    max_export = 0
    for batch in batches:
        state.apply_planned(batch)
        if eager:
            arena, roots = source.materialize(state.images, state.dead)
            max_export = max(max_export, len(arena.rules))
    assert state.rank_one_zero()
    return {'persistent_source_nodes': len(source.rules), 'image_records': len(state.images),
            'max_export_nodes': max_export, 'cooperative_work': state.work,
            'max_exponent_bits': max(abs(k).bit_length() for _, k in state.images.values())}


def chained(source, batches):
    arena, roots = source.materialize({g: (g, 1) for g in source.generators}, set())
    alive = set(source.generators)
    for batch in batches:
        apply_projection(arena, roots, alive, native_witnesses(batch))
    assert len(alive) == 1
    # Independent exact one-generator exponent scan on the materialized state.
    vals = {0: 0}
    for node in arena._reachable(roots):
        rule = arena.rules[node]
        vals[node] = (1 if rule[1] > 0 else -1) if rule[0] == 't' else vals[rule[1]] + vals[rule[2]]
    assert all(vals[v] == 0 for v in roots)
    return {'allocated_grammar_nodes': len(arena.rules), 'cooperative_work': arena.stats.get('work', 0)}


def main(output, rounds):
    rng = random.Random(2026100802)
    cases = [('star', r, 16) for r in (32, 64, 128, 256)] + [('chain', r, 16) for r in (16, 32, 64)]
    arms = ['anchored', 'anchored_control', 'chained', 'chained_control', 'anchored_eager']
    all_results = []
    started = time.perf_counter()
    for kind, rank, bits in cases:
        source, batches = make_case(kind, rank, bits)
        def execute(arm):
            if arm.startswith('chained'):
                return chained(source, batches)
            return anchored(source, batches, eager=arm == 'anchored_eager')
        warmups = {}
        for arm in arms:
            t = time.perf_counter(); metrics = execute(arm)
            warmups[arm] = {'seconds': time.perf_counter() - t, 'metrics': metrics}
        samples = []
        for iteration in range(rounds):
            order = arms[:]; rng.shuffle(order)
            row = {'round': iteration, 'order': order, 'arms': {}}
            for arm in order:
                t = time.perf_counter(); metrics = execute(arm)
                row['arms'][arm] = {'seconds': time.perf_counter() - t, 'metrics': metrics}
            samples.append(row)
        medians = {arm: statistics.median(row['arms'][arm]['seconds'] for row in samples) for arm in arms}
        ratios = {
            'chained_over_anchored': statistics.median(row['arms']['chained']['seconds'] /
                                                      row['arms']['anchored']['seconds'] for row in samples),
            'anchored_A_over_A': statistics.median(row['arms']['anchored']['seconds'] /
                                                  row['arms']['anchored_control']['seconds'] for row in samples),
            'chained_A_over_A': statistics.median(row['arms']['chained']['seconds'] /
                                                 row['arms']['chained_control']['seconds'] for row in samples),
            'eager_over_lazy': statistics.median(row['arms']['anchored_eager']['seconds'] /
                                                 row['arms']['anchored']['seconds'] for row in samples)}
        item = {'family': kind, 'rank': rank, 'power_bit_parameter': bits,
                'source_sha256': source.digest, 'source_nodes': len(source.rules),
                'rounds_in_schedule': len(batches), 'median_seconds': medians,
                'paired_median_ratios': ratios, 'warmups': warmups, 'samples': samples}
        all_results.append(item)
        print(kind, rank, ratios, flush=True)
    payload = {'scope': __doc__, 'status': 'PASS', 'seed': 2026100802,
               'measured_rounds_per_arm': rounds, 'warmups_per_arm': 1,
               'python': sys.version, 'platform': platform.platform(),
               'cases': all_results, 'total_seconds': time.perf_counter() - started}
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(payload, indent=2) + '\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, default=Path('data/benchmark.json'))
    parser.add_argument('--rounds', type=int, default=5)
    args = parser.parse_args()
    if args.rounds < 1:
        parser.error('rounds must be positive')
    main(args.output, args.rounds)
