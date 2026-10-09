"""Prepared canonical minimum rank/select benchmark with an analytic oracle.

All measured lookup arms use the same already prepared index.  Preparation is
reported separately and is excluded from every lookup timer.  The trace is a
deterministic, independently verified schedule for disjoint paired blocks.
"""

import argparse
import hashlib
import json
from pathlib import Path
import platform
import random
import statistics
import sys
import time

FAST_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(FAST_ROOT))
from fastunknot.interval_orbits import IntervalPairing
from fastunknot.integer_codec import json_safe
from fastunknot.orbit_index import OrbitIndex
from orbit_index_research.benchmark import source_manifest


def source_hashes():
    result = source_manifest()
    result['orbit_index_research/rank_select.py'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    return result


def paired_blocks(blocks, width):
    pairs = [IntervalPairing(2 * i * width, (2 * i + 1) * width - 1,
                             (2 * i + 1) * width, (2 * i + 2) * width - 1)
             for i in range(blocks)]
    events = []
    for i in reversed(range(blocks)):
        events.append(dict(op='truncate', index=i, new_size=(2 * i + 1) * width))
        events.append(dict(op='contract', gaps=[[2 * i * width, (2 * i + 1) * width - 1]]))
    proof = dict(version=2, size=2 * blocks * width,
                 pairings=[[p.a, p.b, p.c, p.d, 1] for p in pairs],
                 orbit_count=blocks * width, operations=events)
    return pairs, proof


def run(output, rounds, query_count):
    rng = random.Random(202610090836)
    manifest = source_hashes()
    result = dict(schema='compiled-minimum-rank-select-v1', seed=202610090836,
                  python=sys.version, platform=platform.platform(), rounds=rounds,
                  warmup_rounds=1, queries_per_call=query_count, batch=3,
                  source_manifest_before=manifest, cases=[])
    for blocks, bits in ((1, 128), (16, 128), (128, 4096), (512, 4096)):
        width = (1 << bits) + 3
        pairs, proof = paired_blocks(blocks, width)
        started = time.perf_counter_ns()
        index = OrbitIndex.from_certificate(2 * blocks * width, pairs, proof)
        preparation = (time.perf_counter_ns() - started) / 1e9
        expected_intervals = tuple((2 * i * width, (2 * i + 1) * width) for i in range(blocks))
        if index.minimum_intervals != expected_intervals:
            raise AssertionError('canonical minimum interval union differs from the analytic formula')
        ranks = [rng.randrange(blocks * width) for _ in range(query_count)]
        minima, ordinals = [], []
        for rank in ranks:
            block, offset = divmod(rank, width)
            minima.append(2 * block * width + offset)
            ordinals.append((blocks - 1 - block) * width + offset)
        arms = dict(
            emission_select=lambda: [index.select(i) for i in ordinals],
            canonical_select=lambda: [index.select_minimum(i) for i in ranks],
            select_control=lambda: [index.select_minimum(i) for i in ranks],
            canonical_rank=lambda: [index.minimum_rank(i) for i in minima],
            rank_control=lambda: [index.minimum_rank(i) for i in minima],
        )
        records = []
        for round_index in range(rounds + 1):
            order = list(arms)
            rng.shuffle(order)
            samples = {}
            for name in order:
                started = time.perf_counter_ns()
                answers = [arms[name]() for _ in range(3)]
                seconds = (time.perf_counter_ns() - started) / (1e9 * 3)
                expected = ranks if name in ('canonical_rank', 'rank_control') else minima
                if any(answer != expected for answer in answers):
                    raise AssertionError((blocks, bits, name, 'lookup disagrees with analytic answer'))
                samples[name] = seconds
            records.append(dict(round=round_index, warmup=round_index == 0,
                                order=order, seconds=samples))
        measured = [r['seconds'] for r in records if not r['warmup']]
        medians = {name: statistics.median(r[name] for r in measured) for name in arms}
        ratios = {key: statistics.median(r[left] / r[right] for r in measured)
                  for key, left, right in (
                      ('emission_over_canonical', 'emission_select', 'canonical_select'),
                      ('select_control', 'canonical_select', 'select_control'),
                      ('rank_control', 'canonical_rank', 'rank_control'))}
        case = dict(blocks=blocks, width=width, endpoint_bits=(2 * blocks * width).bit_length(),
                    queries=query_count, preparation_seconds=preparation,
                    index_statistics=index.statistics, ranks=ranks, emission_ordinals=ordinals,
                    minima=minima, median_seconds=medians, paired_ratios=ratios, records=records,
                    certificate_sha256=hashlib.sha256(json.dumps(json_safe(proof), sort_keys=True,
                        separators=(',', ':')).encode()).hexdigest())
        result['cases'].append(case)
        print(json.dumps(dict(blocks=blocks, endpoint_bits=case['endpoint_bits'],
                              preparation_seconds=preparation, median_seconds=medians,
                              paired_ratios=ratios)), flush=True)
    after = source_hashes()
    if manifest != after:
        raise AssertionError('a pinned source changed during the experiment')
    result['source_manifest_after'] = after
    output.write_text(json.dumps(json_safe(result), indent=2) + '\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path,
                        default=FAST_ROOT / 'results' / 'orbit_rank_select.json')
    parser.add_argument('--rounds', type=int, default=7)
    parser.add_argument('--queries', type=int, default=512)
    args = parser.parse_args()
    if args.rounds < 3 or args.queries < 1:
        parser.error('at least three rounds and one query are required')
    run(args.output, args.rounds, args.queries)
