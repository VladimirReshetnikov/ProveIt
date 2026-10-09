#!/usr/bin/env python3
"""Paired subsystem benchmarks; no whole-knot or geometric workload claims.

Four arms on eight completed dense/sparse workloads; two arms on three
sparse-only scale workloads. Exact histogram comparisons are outside timing.
All raw timings, ordering, work counts and source hashes are retained.
"""
import argparse
import csv
import hashlib
import json
import platform
import random
import statistics
import time
import bootstrap
from fastunknot.interval_orbits import IntervalPairing
from fastunknot.interval_incidence import analyze_port_incidence
from fastunknot.sparse_incidence import analyze_sparse_port_incidence
from fastunknot.sparse_incidence_verify import verify_sparse_port_incidence_certificate
from fastunknot.integer_codec import json_safe


def workloads():
    n, r = 1 << 500, 12
    disjoint = [[(3 * i, 3 * i + 1)] for i in range(r)]
    out = [
        dict(name='static-coincident-12', n=n, pairs=[], ports=[[(0, n // 2)]] * r),
        dict(name='static-nested-12', n=n, pairs=[], ports=[[(0, 3 * (i + 1))] for i in range(r)]),
        dict(name='static-disjoint-12', n=n, pairs=[], ports=disjoint),
        dict(name='periodic-disjoint-12', n=n, pairs=[IntervalPairing(0, n - 18, 17, n - 1)],
             ports=[[(i, i + 1)] for i in range(r)]),
        dict(name='reflection-disjoint-12', n=n,
             pairs=[IntervalPairing(0, n - 1, 0, n - 1, True)], ports=disjoint),
        dict(name='static-overlap-8', n=4096, pairs=[],
             ports=[[(10 * i, 10 * i + 45)] for i in range(8)]),
    ]
    for rank, repeats in [(3, 100), (4, 20)]:
        out.append(dict(name=f'full-support-{rank}', n=1 << rank, pairs=[],
                        ports=[[(j, j + 1) for j in range(1 << rank) if j & (1 << i)]
                               for i in range(rank)], repeats=repeats))
    for item in out:
        item.setdefault('repeats', 20 if item['name'].startswith('static-coincident') else
                        10 if item['name'].startswith('static-nested') else 1)
        item['paired_dense'] = True
    out.extend([
        dict(name='sparse-only-disjoint-32', n=n, pairs=[],
             ports=[[(3 * i, 3 * i + 1)] for i in range(32)],
             repeats=1, paired_dense=False),
        dict(name='sparse-only-nested-64', n=n, pairs=[],
             ports=[[(0, 3 * (i + 1))] for i in range(64)],
             repeats=1, paired_dense=False),
        dict(name='sparse-only-coincident-128', n=1 << 16000, pairs=[],
             ports=[[(0, 1 << 15999)]] * 128,
             repeats=5, paired_dense=False),
    ])
    return out


def run_arm(item, arm):
    n, pairs, ports = item['n'], item['pairs'], item['ports']
    if arm == 'dense':
        return analyze_port_incidence(n, pairs, ports, max_ports=len(ports))
    result = analyze_sparse_port_incidence(n, pairs, ports,
                                           record_certificate=arm == 'certified')
    if arm == 'certified':
        if not verify_sparse_port_incidence_certificate(n, pairs, ports, result['certificate']):
            raise AssertionError('certificate replay failed')
    return result


def signature(result, arm):
    if result['status'] != 'COMPLETE':
        raise AssertionError('a benchmark was incomplete')
    if arm == 'dense':
        return [[i, v] for i, v in enumerate(result['histogram']) if v]
    return result['histogram']


def static_reference(n, ports):
    # Endpoint-sweep reference: no orbit kernel and no expanded universe.
    endpoints = sorted({0, n} | {x for port in ports for pair in port for x in pair})
    hist = {}
    for a, b in zip(endpoints, endpoints[1:]):
        mask = sum(1 << i for i, port in enumerate(ports)
                   if any(lo <= a < hi for lo, hi in port))
        hist[mask] = hist.get(mask, 0) + b - a
    return [[mask, count] for mask, count in sorted(hist.items()) if count]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--rounds', type=int, default=7)
    parser.add_argument('--scale-rounds', type=int, default=3)
    args = parser.parse_args()
    if min(args.rounds, args.scale_rounds) < 1:
        parser.error('--rounds must be positive')
    rng = random.Random(261008492)
    samples, summary, inputs = [], [], []
    for item in workloads():
        arms = ['dense', 'sparse', 'sparse-control', 'certified'] if item['paired_dense'] else ['sparse', 'certified']
        expected = signature(run_arm(item, 'sparse'), 'sparse')
        if not item['pairs']:
            assert expected == static_reference(item['n'], item['ports'])
        elif item['name'].startswith('periodic'):
            assert expected == [[0, 5]] + [[1 << i, 1] for i in range(12)]
        elif item['name'].startswith('reflection'):
            assert expected == [[0, item['n'] // 2 - 12]] + [[1 << i, 1] for i in range(12)]
        last = {}
        rounds = args.rounds if item['paired_dense'] else args.scale_rounds
        for round_no in range(-1, rounds):
            ordering = list(arms)
            rng.shuffle(ordering)
            for order, arm in enumerate(ordering):
                start = time.perf_counter_ns()
                for _ in range(item['repeats']):
                    result = run_arm(item, arm)
                elapsed = (time.perf_counter_ns() - start) / 1e9 / item['repeats']
                assert signature(result, arm) == expected
                last[arm] = result
                samples.append(dict(workload=item['name'], round=round_no, order=order,
                                    arm=arm, repeats=item['repeats'], seconds_per_call=elapsed,
                                    orbit_queries=result['stats']['orbit_queries'],
                                    orbit_cycles=result['stats']['orbit_cycles']))
        medians = {arm: statistics.median(row['seconds_per_call'] for row in samples
                       if row['workload'] == item['name'] and row['arm'] == arm and row['round'] >= 0)
                   for arm in arms}
        pair_ratios = []
        controls = []
        if item['paired_dense']:
            for j in range(args.rounds):
                times = {row['arm']: row['seconds_per_call'] for row in samples
                         if row['workload'] == item['name'] and row['round'] == j}
                pair_ratios.append(times['dense'] / times['sparse'])
                controls.append(times['sparse-control'] / times['sparse'])
        cert_bytes = len(json.dumps(json_safe(last['certified']['certificate']),
                                    separators=(',', ':')).encode())
        row = dict(name=item['name'], r=len(item['ports']), k=len(item['pairs']),
                   endpoint_bits=item['n'].bit_length(), support=len(expected),
                   dense_slots=str(1 << len(item['ports'])), paired_dense=item['paired_dense'],
                   medians_seconds=medians,
                   median_paired_dense_over_sparse=statistics.median(pair_ratios) if pair_ratios else None,
                   median_paired_control_over_sparse=statistics.median(controls) if controls else None,
                   query_counts={arm: last[arm]['stats']['orbit_queries'] for arm in arms},
                   sparse_stats=last['sparse']['stats'], certificate_json_bytes=cert_bytes,
                   retained_proofs=len(last['certified']['certificate']['proofs']))
        summary.append(row)
        (bootstrap.ROOT / 'results' / 'benchmark_checkpoint.json').write_text(
            json.dumps(dict(summary=summary, samples=samples), indent=2) + '\n')
        inputs.append(dict(name=item['name'], size=item['n'], ports=item['ports'],
                           pairings=[[p.a, p.b, p.c, p.d, -1 if p.reverse else 1] for p in item['pairs']]))
        print(item['name'], 'support', row['support'], 'queries', row['query_counts'],
              'ms', {key: round(value * 1000, 3) for key, value in medians.items()}, flush=True)
    source_hashes = {}
    for subdir in ('reference/fastunknot', 'overlay/fast/fastunknot', 'experiments'):
        for path in sorted((bootstrap.ROOT / subdir).glob('*.py')):
            source_hashes[str(path.relative_to(bootstrap.ROOT))] = hashlib.sha256(path.read_bytes()).hexdigest()
    report = dict(seed=261008492, measured_rounds=args.rounds,
                  scale_rounds=args.scale_rounds, warmup_rounds=1,
                  python=platform.python_version(), implementation=platform.python_implementation(),
                  platform=platform.platform(), processor=platform.processor(),
                  clock='perf_counter_ns', summary=summary, samples=samples,
                  source_hashes=source_hashes, scope='interval-relation subsystem only; not whole-knot recognition')
    results = bootstrap.ROOT / 'results'
    (results / 'benchmark.json').write_text(json.dumps(report, indent=2) + '\n')
    (results / 'benchmark_inputs.json').write_text(json.dumps(json_safe(inputs), indent=2) + '\n')
    with (results / 'benchmark_samples.csv').open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=list(samples[0]))
        writer.writeheader()
        writer.writerows(samples)


if __name__ == '__main__':
    main()
