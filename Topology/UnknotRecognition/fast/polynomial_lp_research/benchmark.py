"""Paired complete transversal recognition: polynomial policy versus Bland.

Construction, preprocessing, discovery, internal replay and full JSON encoding
are timed. Independent replay of saved warmups is outside the timer.
"""
import argparse
from hashlib import sha256
import platform
from random import Random
from statistics import median
import sys
from time import perf_counter_ns

from fastunknot.normal_crushing_search import recognize_by_crushing
from .common import (ARMS, SEED, configs, diagrams, source_hashes, encode,
                     save, verify_result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    parser.add_argument('--pairs', type=int, default=3)
    parser.add_argument('--aa', type=int, default=1)
    parser.add_argument('--batch', type=int, default=1)
    args = parser.parse_args()
    if min(args.pairs, args.aa, args.batch) < 1:
        parser.error('pairs, aa and batch must be positive')
    configuration, rng = configs(), Random(SEED)
    output = dict(passed=False, source_sha256=source_hashes(), arms=list(ARMS),
        configs=configuration, seed=SEED, pairs=args.pairs, aa=args.aa, batch=args.batch,
        python=sys.version, platform=platform.platform(),
        comparison='current native solver: default polynomial policy versus explicit legacy Bland policy; all other configuration and source files identical',
        scope=__doc__, records=[])

    def query(diagram, arm):
        result = recognize_by_crushing(diagram, **configuration[arm])
        encoded = encode(result)
        return result, len(encoded), sha256(encoded).hexdigest()

    def sample(diagram, arm, expected):
        start = perf_counter_ns()
        for _ in range(args.batch):
            result, size, hashed = query(diagram, arm)
            assert hashed == expected, 'full timed output differs from replayed warmup'
        elapsed = perf_counter_ns()-start
        return dict(elapsed_ns=elapsed, ns=elapsed/args.batch, status=result['status'],
                    stats=result['stats'], result_bytes=size, output_sha256=hashed)

    for name, diagram in diagrams():
        record = dict(id=name, input_pd=[list(row) for row in diagram.pd],
                      warmup_results={}, warmup_sha256={}, samples=[], aa_samples=[])
        for arm in ARMS:
            result, _, hashed = query(diagram, arm)
            assert result['status'] == ('UNKNOT' if name == 'circle' else 'KNOTTED')
            verify_result(diagram, result)
            record['warmup_results'][arm], record['warmup_sha256'][arm] = result, hashed
        left, right = [record['warmup_results'][arm] for arm in ARMS]
        record['identical_full_results'] = record['warmup_sha256']['bland'] == record['warmup_sha256']['polynomial']
        record['different_top_level_fields'] = [key for key in sorted(set(left)|set(right))
                                                if left.get(key) != right.get(key)]
        if left['stats']['lp_fallbacks'] == right['stats']['lp_fallbacks'] == 0:
            assert record['identical_full_results'], 'policies changed a result without invoking fallback'
        for _ in range(args.pairs):
            order = list(ARMS)
            rng.shuffle(order)
            record['samples'].append(dict(order=order, results={arm:
                sample(diagram, arm, record['warmup_sha256'][arm]) for arm in order}))
        for _ in range(args.aa):
            order = ['A', 'B']
            rng.shuffle(order)
            record['aa_samples'].append(dict(order=order, results={label:
                sample(diagram, 'bland', record['warmup_sha256']['bland']) for label in order}))
        record['median_ns'] = {arm: median(s['results'][arm]['ns'] for s in record['samples']) for arm in ARMS}
        record['paired_bland_over_polynomial'] = median(
            s['results']['bland']['ns']/s['results']['polynomial']['ns'] for s in record['samples'])
        record['aa_ratio'] = median(s['results']['A']['ns']/s['results']['B']['ns'] for s in record['aa_samples'])
        output['records'].append(record)
        save(args.output, output)
        print(name, record['median_ns'], record['paired_bland_over_polynomial'], flush=True)
    assert output['source_sha256'] == source_hashes(), 'benchmarked source changed'
    output['passed'] = True
    save(args.output, output)


if __name__ == '__main__':
    main()
