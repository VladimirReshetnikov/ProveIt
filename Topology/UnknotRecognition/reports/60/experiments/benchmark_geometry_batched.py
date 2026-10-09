#!/usr/bin/env python3
"""Batched follow-up on four prespecified small dense/sparse port workloads.

The exact inputs and expected histograms are read from geometry_benchmark.json.
Each whole batch is timed before dividing by its number of complete calls.
All output comparisons are outside timing. The sparse_verified arm includes
certificate creation and verification inside each timed call. No result or
regression is filtered. Production modules are read and hashed, never modified.
"""

import argparse
from datetime import datetime, timezone
import gc
import hashlib
import json
from pathlib import Path
import platform
import random
import statistics
import sys
import time


SEED = 261009217
ROUNDS = 7
SELECTION = (
    ('static_disjoint_4', 128),
    ('static_nested_12', 8),
    ('meridian_identical_8', 16),
    ('parallel_identical_8', 16),
)
ARMS = ('dense', 'dense_control', 'sparse', 'sparse_verified')


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fast', type=Path, required=True)
    parser.add_argument('--input', type=Path,
                        default=Path('results/geometry_benchmark.json'))
    parser.add_argument('--output', type=Path,
                        default=Path('results/geometry_batched.json'))
    parser.add_argument('--log', type=Path)
    args = parser.parse_args()
    args.fast = args.fast.resolve()
    args.log = args.log or args.output.with_suffix('.log')
    sys.path.insert(0, str(args.fast))
    from fastunknot.integer_codec import encoded_integer, json_safe
    from fastunknot.interval_orbits import IntervalPairing
    from fastunknot.interval_incidence import analyze_port_incidence
    from fastunknot.sparse_port_incidence import (
        sparse_port_incidence, verify_sparse_port_certificate,
    )

    input_bytes = args.input.read_bytes()
    reference = json.loads(input_bytes)
    cases_by_name = {case['name']: case for case in reference['results']}
    if len(cases_by_name) != len(reference['results']):
        raise ValueError('duplicate case names in the reference benchmark')
    modules = sorted((args.fast / 'fastunknot').rglob('*.py'))
    def sources():
        return {str(path.relative_to(args.fast)): digest(path.read_bytes())
                for path in modules}
    before = sources()
    if before != reference['source_sha256']:
        raise AssertionError('production sources differ from the frozen reference benchmark')
    own_hash = digest(Path(__file__).read_bytes())
    rng = random.Random(SEED)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.log.parent.mkdir(parents=True, exist_ok=True)
    all_start = time.perf_counter()
    totals = {'measured_calls': 0, 'warmup_calls': 0,
              'measured_batches': 0, 'warmup_batches': 0,
              'measured_verifications': 0, 'warmup_verifications': 0,
              'correctness_checked_calls': 0}
    serial_call = 0
    results = []

    with args.log.open('w') as logfile:
        def emit(value):
            line = json.dumps(value, sort_keys=True)
            print(line, flush=True)
            logfile.write(line + '\n')
            logfile.flush()
        emit({'event': 'start', 'seed': SEED, 'measured_rounds': ROUNDS,
              'excluded_warmup_rounds': 1, 'source_modules': len(before),
              'reference_json_sha256': digest(input_bytes), 'driver_sha256': own_hash})

        for name, batch in SELECTION:
            source = cases_by_name[name]
            size = encoded_integer(source['size'])
            pairs = []
            for row in source['pairings']:
                if len(row) != 5 or type(row[4]) is not bool:
                    raise ValueError('reference pairings require four endpoints and a boolean')
                pairs.append(IntervalPairing(*(encoded_integer(x) for x in row[:4]),
                                              reverse=row[4]))
            ports = [[(encoded_integer(lo), encoded_integer(hi)) for lo, hi in port]
                     for port in source['ports']]
            expected = [[encoded_integer(mask), encoded_integer(count)]
                        for mask, count in source['histogram']]

            def call(arm):
                if arm in ('dense', 'dense_control'):
                    return analyze_port_incidence(size, pairs, ports)
                answer = sparse_port_incidence(size, pairs, ports,
                                                record_certificate=arm == 'sparse_verified')
                if arm == 'sparse_verified':
                    if not verify_sparse_port_certificate(size, pairs, ports,
                                                           answer['certificate']):
                        raise AssertionError('certificate verification failed inside timed call')
                return answer

            samples, orders = [], []
            for round_index in range(-1, ROUNDS):
                order = list(ARMS)
                rng.shuffle(order)
                orders.append({'round': round_index, 'arms': order})
                round_times = {}
                for arm in order:
                    # Allocate only the result slots before timing. Retain all
                    # complete outputs so every call can be checked afterward.
                    answers = [None] * batch
                    gc.collect()
                    first_call = serial_call + 1
                    start = time.perf_counter_ns()
                    for i in range(batch):
                        answers[i] = call(arm)
                    elapsed_ns = time.perf_counter_ns() - start
                    serial_call += batch
                    round_times[arm] = elapsed_ns / batch / 1e9

                    # No histogram normalization/comparison occurs in timing.
                    for answer in answers:
                        if answer['status'] != 'COMPLETE':
                            raise AssertionError((name, arm, 'unlimited call incomplete'))
                        if arm in ('dense', 'dense_control'):
                            actual = [[mask, count] for mask, count in
                                      enumerate(answer['histogram']) if count]
                        else:
                            actual = [[item['mask'], item['orbits']]
                                      for item in answer['histogram']]
                        if actual != expected:
                            raise AssertionError((name, arm, 'reference histogram mismatch'))
                    phase = 'warmup' if round_index < 0 else 'measured'
                    totals[phase + '_calls'] += batch
                    totals[phase + '_batches'] += 1
                    totals['correctness_checked_calls'] += batch
                    if arm == 'sparse_verified':
                        totals[phase + '_verifications'] += batch
                    sample = {'round': round_index, 'arm': arm, 'batch': batch,
                              'first_call_id': first_call, 'last_call_id': serial_call,
                              'batch_nanoseconds': elapsed_ns,
                              'seconds_per_call': elapsed_ns / batch / 1e9,
                              'correctness_checked_calls': batch,
                              'all_histograms_match': True,
                              'timed_verification_calls': batch if arm == 'sparse_verified' else 0,
                              'last_stats': answers[-1]['stats']}
                    if arm == 'sparse_verified':
                        proof = json.dumps(json_safe(answers[-1]['certificate']),
                                           sort_keys=True, separators=(',', ':')).encode()
                        sample['last_certificate_bytes'] = len(proof)
                        sample['last_certificate_sha256'] = digest(proof)
                    samples.append(sample)
                    del answers
                emit({'event': 'round', 'case': name, 'round': round_index,
                      'order': order, 'batch': batch, 'seconds_per_call': round_times,
                      'all_histograms_match': True})

            measured = [row for row in samples if row['round'] >= 0]
            by_round = {index: {row['arm']: row['seconds_per_call'] for row in measured
                                if row['round'] == index} for index in range(ROUNDS)}
            medians = {arm: statistics.median(row['seconds_per_call'] for row in measured
                                              if row['arm'] == arm) for arm in ARMS}
            ratio_samples = {arm: [by_round[index]['dense'] / by_round[index][arm]
                                   for index in range(ROUNDS)]
                             for arm in ARMS if arm != 'dense'}
            ratios = {arm: statistics.median(values) for arm, values in ratio_samples.items()}
            result = {'name': name, 'batch': batch,
                      'size': source['size'], 'size_bits': size.bit_length(),
                      'pairings': source['pairings'], 'ports': source['ports'],
                      'style': source['style'], 'histogram': expected,
                      'reference_case_sha256': digest(json.dumps(source, sort_keys=True,
                          separators=(',', ':')).encode()),
                      'orders': orders, 'samples': samples, 'medians': medians,
                      'paired_ratio_samples': ratio_samples, 'paired_ratios': ratios,
                      'measured_calls': batch * len(ARMS) * ROUNDS,
                      'warmup_calls': batch * len(ARMS),
                      'all_histograms_match': True}
            results.append(result)
            emit({'event': 'case_complete', 'case': name, 'batch': batch,
                  'medians': medians, 'paired_ratios': ratios,
                  'measured_calls': result['measured_calls'],
                  'warmup_calls': result['warmup_calls']})

        after = sources()
        if before != after:
            raise AssertionError('production source hashes changed during the benchmark')
        if args.input.read_bytes() != input_bytes:
            raise AssertionError('reference benchmark changed during the follow-up')
        if digest(Path(__file__).read_bytes()) != own_hash:
            raise AssertionError('benchmark driver changed while running')
        answer = {'schema': 'geometry-batched-benchmark-v1',
                  'baseline_commit': reference['baseline_commit'],
                  'created_utc': datetime.now(timezone.utc).isoformat(),
                  'python': sys.version, 'platform': platform.platform(),
                  'seed': SEED, 'measured_rounds': ROUNDS, 'excluded_warmup_rounds': 1,
                  'arms': list(ARMS), 'selection': [{'name': name, 'batch': batch}
                                                    for name, batch in SELECTION],
                  'reference_json_sha256': digest(input_bytes), 'driver_sha256': own_hash,
                  'source_sha256': before, 'source_hashes_unchanged': True,
                  'reference_sources_match': True, 'all_histograms_match': True,
                  'seconds': time.perf_counter() - all_start,
                  **totals, 'total_calls': serial_call, 'results': results,
                  'scope': 'Prespecified batched follow-up on four small workloads. '
                           'Each time covers a batch of fresh complete calls divided by '
                           'batch size. Every output is checked against the retained exact '
                           'reference histogram outside timing. sparse_verified includes '
                           'certificate production and verification inside each timed call. '
                           'dense_control is identical to dense. All rounds and regressions '
                           'are retained. No end-to-end knot recognition is timed.'}
        args.output.write_text(json.dumps(json_safe(answer), indent=2) + '\n')
        emit({'event': 'complete', **totals, 'total_calls': serial_call,
              'source_hashes_unchanged': True, 'all_histograms_match': True,
              'seconds': answer['seconds']})


if __name__ == '__main__':
    main()
