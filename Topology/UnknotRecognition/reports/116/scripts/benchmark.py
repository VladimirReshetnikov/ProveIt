#!/usr/bin/env python3
"""Paired component measurements; all samples retained, no censored inference.

New kernel versus an explicit subset oracle is an algorithmic comparison, not
versus the maintained ordered-interface solver and not an end-to-end knot test.
"""
from __future__ import annotations
import argparse, gc, json, platform, random, statistics, sys, time
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from cycleblocks import (optimize_counts, verify_plan, transport_circuit,
                         evaluate_circuit, periodic_cycle_optimum,
                         verify_power_certificate, Limits)
from tests.oracles import brute_private, literal_transport, cactus_counts


def paired(new, old, rounds, seed):
    rng = random.Random(seed)
    expected = old()
    assert new() == expected
    samples = []
    # The old and control arms are deliberately identical A/A controls.
    for k in range(rounds):
        order = ['new', 'old', 'control']; rng.shuffle(order)
        row = {'round': k, 'order': order}
        for name in order:
            gc.collect()
            start = time.perf_counter_ns()
            value = new() if name == 'new' else old()
            row[name + '_ns'] = time.perf_counter_ns() - start
            assert value == expected
        samples.append(row)
    return {'rounds': rounds, 'samples': samples,
            'new_median_ms': statistics.median(x['new_ns'] for x in samples) / 1e6,
            'old_median_ms': statistics.median(x['old_ns'] for x in samples) / 1e6,
            'paired_old_over_new': statistics.median(x['old_ns']/x['new_ns'] for x in samples),
            'control_old_over_old': statistics.median(x['control_ns']/x['old_ns'] for x in samples)}


def matrix_cases(rounds):
    out = []
    for blocks in [1, 2, 4, 6, 8]:
        counts = cactus_counts(blocks)
        weights = {r: 1 for r in counts}
        def new():
            p = optimize_counts(counts, weights, prepeel=False)
            assert p['status'] == 'OPTIMAL_MATRIX_PLAN'
            assert verify_plan(counts, p, weights)
            # Same result quantity as the reference; certificate work is included.
            return p['matched_weight']
        def old(): return brute_private(counts, weights)
        row = {'family': 'unit_cactus', 'blocks': blocks, 'rows': len(counts),
               'incidences': sum(map(len, counts.values()))}
        row.update(paired(new, old, rounds, 20261012 + blocks))
        out.append(row)
    return out


def transport_cases(rounds):
    out = []
    for n in [2, 8, 32, 128, 512]:
        # Nonunit columns are not optimization vertices, but must survive.
        counts = {0: {0: 1, **{j: 2 for j in range(1, n + 1)}}}
        counts.update({r: {0: 1} for r in range(1, n + 1)})
        weights = {r: (n + 1 if r == 0 else 1) for r in counts}
        plan = optimize_counts(counts, weights)
        assert plan['cancellations'] == [[0, 0]]
        observable = {j: 1 for j in range(1, n + 1)}
        def new():
            c = transport_circuit(counts, plan, weights)
            values = evaluate_circuit(c, observable)
            return json.dumps(values, sort_keys=True, separators=(',', ':'))
        def old():
            assert verify_plan(counts, plan, weights)
            residual = literal_transport(counts, plan['cancellations'])
            return json.dumps({r: sum(row.values()) for r, row in residual.items()},
                              sort_keys=True, separators=(',', ':'))
        row = {'family': 'dense_passive_fill', 'passive_rows': n,
               'outside_columns': n, 'input_incidences': 2*n + 1,
               'explicit_residual_entries': n*n}
        row.update(paired(new, old, rounds, 20262000 + n))
        out.append(row)
    return out


def power_cases(rounds):
    out = []
    for bits in [16, 64, 256, 1024]:
        n = 1 << bits
        rows = []
        for k in range(rounds + 1):
            gc.collect()
            start = time.perf_counter_ns()
            result = periodic_cycle_optimum(n, certificate=True)
            assert verify_power_certificate(result['certificate'])
            data = json.dumps(result, sort_keys=True, separators=(',', ':')).encode()
            elapsed = time.perf_counter_ns() - start
            assert result['matched_weight'] == n-1 and result['deferred_weight'] == 1
            if k: rows.append(elapsed)
        out.append({'half_length_exponent': bits, 'products': result['matrix_products'],
                    'serialized_bytes': len(data), 'samples_ns': rows,
                    'median_ms': statistics.median(rows)/1e6})
    return out


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--suite', choices=['matrix', 'transport', 'power', 'all'], default='all')
    p.add_argument('--rounds', type=int, default=7)
    p.add_argument('--output', type=Path)
    args = p.parse_args()
    if not 1 <= args.rounds <= 100: p.error('rounds must be between 1 and 100')
    output = {'python': sys.version, 'platform': platform.platform(),
              'clock': 'perf_counter_ns', 'seed': 20261012,
              'scope': 'standalone component measurements; no native geometry or knot timings',
              'warmup': 'one complete untimed query per arm; gc.collect outside timed regions'}
    for name, func in [('matrix', matrix_cases), ('transport', transport_cases), ('power', power_cases)]:
        if args.suite in [name, 'all']:
            output[name] = func(args.rounds)
            print(name, json.dumps(output[name]), flush=True)
    dest = args.output or ROOT/'results'/f'benchmark_{args.suite}.json'
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(json.dumps(output, indent=2) + '\n')
if __name__ == '__main__': main()
