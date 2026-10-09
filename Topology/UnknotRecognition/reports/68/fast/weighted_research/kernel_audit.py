#!/usr/bin/env python3
"""Reproduce finite-oracle checks and abstract weighted-AHT kernel measurements.

These are interval-equivalence inputs, not knot diagrams or normal surfaces.
The dimension parameter t in benchmarks is synthetic. Full 7*t-coordinate
histograms and compact three-coordinate histograms solve the same projected
task, with projection and histogram coalescing included in the full arm.
"""

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import platform
import random
import statistics
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from fastunknot.integer_codec import json_safe
from fastunknot.interval_orbits import IntervalPairing, count_orbits
from fastunknot.weighted_orbits import weighted_orbit_histogram
from fastunknot.weighted_orbit_verify import verify_weighted_orbit_certificate


PINNED_BASELINE = '04a66388e25507922595eb68a3ec581b4df4fb6b'
SEED = 73091


def metadata():
    sources = ['interval_orbits.py', 'interval_orbit_verify.py', 'integer_codec.py',
               'weighted_orbits.py', 'weighted_orbit_verify.py']
    return dict(timestamp_utc=datetime.now(timezone.utc).isoformat(),
                python=platform.python_version(), platform=platform.platform(),
                pinned_repository_sha=PINNED_BASELINE,
                source_sha256={name: hashlib.sha256((ROOT/'fastunknot'/name).read_bytes()).hexdigest()
                               for name in sources},
                driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())


def oracle(size, pairs, intervals, dimension):
    parents = list(range(size))

    def find(point):
        while parents[point] != point:
            parents[point] = parents[parents[point]]
            point = parents[point]
        return point

    for pair in pairs:
        for point in range(pair.a, pair.b+1):
            parents[find(point)] = find(pair.image(point))
    values = [[0]*dimension for _ in range(size)]
    for lo, hi, value in intervals:
        for point in range(lo, hi):
            for j, entry in enumerate(value):
                values[point][j] += entry
    totals = {}
    for point, value in enumerate(values):
        total = totals.setdefault(find(point), [0]*dimension)
        for j, entry in enumerate(value):
            total[j] += entry
    return dict(Counter(tuple(value) for value in totals.values()))


def mapping(answer):
    return {tuple(record['weight']): record['orbits'] for record in answer['histogram']}


def input_rows(pairs):
    return [[pair.a, pair.b, pair.c, pair.d, -1 if pair.reverse else 1] for pair in pairs]


def random_input(randomizer):
    size = randomizer.randrange(61)
    pairs = []
    if size:
        for _ in range(randomizer.randrange(14)):
            width = randomizer.randrange(1, size+1)
            a = randomizer.randrange(size-width+1)
            c = randomizer.randrange(size-width+1)
            pairs.append(IntervalPairing(a, a+width-1, c, c+width-1,
                                        bool(randomizer.randrange(2))))
    intervals = []
    for _ in range(randomizer.randrange(9)):
        lo = randomizer.randrange(size+1)
        hi = randomizer.randrange(lo, size+1)
        intervals.append((lo, hi, [randomizer.randrange(-4, 5) for _ in range(3)]))
    return size, pairs, intervals


def audit(cases, seed):
    randomizer = random.Random(seed)
    digest = hashlib.sha256()
    counter = Counter()
    maximum = Counter()
    started = time.perf_counter()
    for case in range(cases):
        size, pairs, intervals = random_input(randomizer)
        source = dict(size=size, pairings=input_rows(pairs), weights=intervals)
        digest.update(json.dumps(source, sort_keys=True, separators=(',', ':')).encode())
        rule = 'aht' if case & 1 else 'fine_wilf'
        result = weighted_orbit_histogram(size, pairs, intervals, dimension=3,
                                          periodic_rule=rule, record_certificate=True)
        if mapping(result) != oracle(size, pairs, intervals, 3):
            raise AssertionError(('literal mismatch', case, source, result))
        if not verify_weighted_orbit_certificate(size, pairs, intervals,
                                                  result['certificate'], dimension=3):
            raise AssertionError(('independent replay failed', case, source, result))
        stats = result['stats']
        if stats['maximum_weight_runs'] > (stats['input_weight_runs']
                + 2*(stats['translation_pushes']+stats['reflection_pushes'])):
            raise AssertionError(('run-count theorem failed', case, stats))
        counter[rule] += 1
        for key in ('translation_pushes', 'reflection_pushes', 'replay_events'):
            counter[key] += stats[key]
        counter['literal_points'] += size
        maximum['weight_runs'] = max(maximum['weight_runs'], stats['maximum_weight_runs'])
        maximum['histogram_rows'] = max(maximum['histogram_rows'], len(result['histogram']))
        maximum['run_growth'] = max(maximum['run_growth'],
                                    stats['maximum_weight_runs']-stats['input_weight_runs'])
    huge = []
    for bits in (64, 256, 4096, 20000):
        size = 1 << bits
        weights = [(0, size, (3, -(1 << 127), 7))]
        for family, pairs, expected in (
                ('one_orbit', [IntervalPairing(0, size-2, 1, size-1)],
                 [dict(weight=[3*size, -(1 << 127)*size, 7*size], orbits=1)]),
                ('reflection', [IntervalPairing(0, size-1, 0, size-1, True)],
                 [dict(weight=[6, -(1 << 128), 14], orbits=size//2)])):
            result = weighted_orbit_histogram(size, pairs, weights, record_certificate=True)
            if result['histogram'] != expected:
                raise AssertionError(('huge closed-form mismatch', bits, family))
            if not verify_weighted_orbit_certificate(size, pairs, weights,
                                                      json_safe(result['certificate'])):
                raise AssertionError(('huge replay failed', bits, family))
            huge.append(dict(family=family, size_bits=bits+1,
                             input=dict(size=size, pairings=input_rows(pairs), weights=weights),
                             histogram=result['histogram'], stats=result['stats']))
    return dict(kind='weighted_interval_kernel_audit', metadata=metadata(), seed=seed,
                status='PASS', cases=cases, input_stream_sha256=digest.hexdigest(),
                counters=dict(counter), maxima=dict(maximum), huge_cases=huge,
                elapsed_seconds=time.perf_counter()-started,
                scope='Finite pointwise oracles and exact huge abstract interval systems; '
                      'these are not knot diagrams or normal-surface benchmarks.')


def benchmark_input(family, bits, synthetic_t):
    scale = (1 << bits)+117
    if family == 'translation':
        size = scale
        period = max(2, scale//17)
        pairs = [IntervalPairing(0, size-period-1, period, size-1)]
    elif family == 'reflection':
        size = scale
        pairs = [IntervalPairing(0, size-1, 0, size-1, True)]
    elif family == 'sharp_threshold':
        q = scale
        size = 2*q+2
        pairs = [IntervalPairing(0, q, q+1, 2*q+1),
                 IntervalPairing(2, q+1, q+2, 2*q+1)]
    elif family == 'disjoint_transmission':
        size = 5*scale+17
        pairs = [IntervalPairing(0, scale-1, 3*scale, 4*scale-1),
                 IntervalPairing(3*scale, 3*scale+scale//3-1,
                                 3*scale+2*scale//3, 3*scale+scale//3+2*scale//3-1, True)]
    else:
        raise ValueError(family)
    dimension = 7*synthetic_t
    count = 2*synthetic_t+1
    compact, full = [], []
    for index in range(count):
        lo, hi = index*size//count, (index+1)*size//count
        core = [index % 5-2, 3*index % 7-3, index % 2]
        extra = [0]*(dimension-3)
        extra[index % len(extra)] = 1
        compact.append((lo, hi, core))
        full.append((lo, hi, core+extra))
    return size, pairs, compact, full


def projected(answer):
    result = Counter()
    for row in answer['histogram']:
        result[tuple(row['weight'][:3])] += row['orbits']
    return dict(result)


def measured_benchmark(rounds, seed):
    randomizer = random.Random(seed)
    records = []
    for family in ('translation', 'reflection', 'sharp_threshold', 'disjoint_transmission'):
        for bits, synthetic_t in ((32, 4), (256, 16), (4096, 64)):
            size, pairs, compact, full = benchmark_input(family, bits, synthetic_t)
            compact_reply = weighted_orbit_histogram(size, pairs, compact, record_certificate=True)
            full_reply = weighted_orbit_histogram(size, pairs, full, record_certificate=True)
            expected = mapping(compact_reply)
            if projected(full_reply) != expected:
                raise AssertionError('full and compact projected tasks disagree')

            def produce(intervals):
                return weighted_orbit_histogram(size, pairs, intervals, record_certificate=True)

            def replay(intervals, certificate):
                if not verify_weighted_orbit_certificate(size, pairs, intervals, certificate):
                    raise AssertionError('independent replay failed')

            def complete(intervals):
                answer = produce(intervals)
                replay(intervals, answer['certificate'])
                result = projected(answer)
                if result != expected:
                    raise AssertionError('timed projected histogram differs')
                return result

            arms = dict(
                count=lambda: count_orbits(size, pairs, record_certificate=True),
                count_aa=lambda: count_orbits(size, pairs, record_certificate=True),
                compact_producer=lambda: produce(compact),
                full_producer=lambda: produce(full),
                compact_replay=lambda: replay(compact, compact_reply['certificate']),
                full_replay=lambda: replay(full, full_reply['certificate']),
                compact_checked=lambda: complete(compact),
                compact_checked_aa=lambda: complete(compact),
                full_checked_projected=lambda: complete(full),
            )
            for _ in range(2):
                for call in arms.values():
                    call()
            samples = []
            for round_index in range(rounds):
                order = list(arms)
                randomizer.shuffle(order)
                values = {}
                for name in order:
                    started = time.perf_counter_ns()
                    arms[name]()
                    values[name] = (time.perf_counter_ns()-started)/1e9
                samples.append(dict(round=round_index, order=order, seconds=values))
            medians = {name: statistics.median(row['seconds'][name] for row in samples)
                       for name in arms}
            ratios = dict(
                full_over_compact=statistics.median(
                    row['seconds']['full_checked_projected']/row['seconds']['compact_checked']
                    for row in samples),
                compact_aa=statistics.median(
                    row['seconds']['compact_checked_aa']/row['seconds']['compact_checked']
                    for row in samples),
                count_aa=statistics.median(row['seconds']['count_aa']/row['seconds']['count']
                                           for row in samples))
            records.append(dict(family=family, bits=bits, synthetic_t=synthetic_t,
                dimensions=dict(compact=3, full=7*synthetic_t),
                input=dict(size=size, pairings=input_rows(pairs),
                           compact_weights=compact, full_weights=full),
                expected_projected_histogram=compact_reply['histogram'],
                compact_stats=compact_reply['stats'], full_stats=full_reply['stats'],
                histogram_rows=dict(compact=len(compact_reply['histogram']), full=len(full_reply['histogram'])),
                proof_bytes=dict(compact=len(json.dumps(json_safe(compact_reply['certificate']))),
                                 full=len(json.dumps(json_safe(full_reply['certificate'])))),
                warmup_calls_per_arm=2, raw_samples=samples, median_seconds=medians,
                paired_median_ratios=ratios))
    return dict(kind='weighted_interval_kernel_benchmark', metadata=metadata(), seed=seed,
        rounds=rounds, records=records,
        scope='Abstract weighted interval systems, not normal surfaces or whole-knot calls. '
              'The synthetic t controls vector dimension; it is not a tetrahedron count. '
              'Full and compact checked arms include source construction of the orbit proof, '
              'weight propagation, independent replay, and identical three-coordinate output; '
              'the full arm additionally projects and coalesces its detailed histogram. '
              'Source interval lists are prebuilt, process startup and JSON serialization excluded. '
              'Count-only arms compute a smaller output and are controls, not same-task competitors.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['audit', 'benchmark'])
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--seed', type=int, default=SEED)
    parser.add_argument('--cases', type=int, default=10000)
    parser.add_argument('--rounds', type=int, default=9)
    args = parser.parse_args()
    if args.cases < 1 or args.rounds < 1:
        parser.error('cases and rounds must be positive')
    result = audit(args.cases, args.seed) if args.mode == 'audit' else measured_benchmark(args.rounds, args.seed)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(json_safe(result), indent=2)+'\n')
    print(json.dumps(dict(status=result.get('status', 'COMPLETE'), output=str(args.output),
                          cases=result.get('cases'), records=len(result.get('records', [])))))


if __name__ == '__main__':
    main()
