"""Controlled A/A/B raw-elimination kernel comparison, not knot timings."""
import argparse
import hashlib
import json
import platform
import random
import statistics
import sys
from pathlib import Path
from time import perf_counter

from persistent_elimination import SignedCircuit, doubling_context_family


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--baseline-fast', required=True, type=Path)
    parser.add_argument('--output', default='persistent_elimination_results.json', type=Path)
    parser.add_argument('--sizes', nargs='+', type=int, default=[8, 16, 32, 64, 128])
    parser.add_argument('--rounds', type=int, default=5)
    args = parser.parse_args()
    sys.path.insert(0, str(args.baseline_fast.resolve()))
    from fastunknot.compressed_words import WordArena
    from fastunknot.elimination_batch import apply_batch

    def sample(k, arm):
        words, moves = doubling_context_family(k)
        t0 = perf_counter()
        if arm == 'persistent':
            arena = SignedCircuit(max_nodes=2_000_000, max_work=1_000_000_000)
            roots = [arena.from_word(word) for word in words]
            arena.expand = lambda *a, **kw: (_ for _ in ()).throw(
                AssertionError('unexpected literal expansion'))
            for slot, g in moves:
                arena.eliminate(roots, slot, g)
            elapsed = perf_counter()-t0
            work_elimination = arena.work
            info = arena.measurements(roots)
            info['work_elimination'] = work_elimination
            length = info['root_lengths'][-1]
            # Metadata measurements are excluded from elapsed in both arms.
            result = {key: value for key, value in info.items() if key != 'root_lengths'}
        else:
            arena = WordArena(max_nodes=2_000_000, max_work=1_000_000_000)
            roots = [arena.from_word(word) for word in words]
            alive = {abs(x) for word in words for x in word}
            arena.expand = lambda *a, **kw: (_ for _ in ()).throw(
                AssertionError('unexpected literal expansion'))
            for slot, g in moves:
                apply_batch(arena, roots, alive,
                            [dict(relation=slot, generator=g)])
            elapsed = perf_counter()-t0
            length = arena.lengths[roots[-1]]
            result = dict(nodes=len(arena.rules)-1, work_elimination=arena.stats['work'],
                          max_length_bits=max(x.bit_length() for x in arena.lengths))
        assert length == (1 << k)+2
        result.update(k=k, arm=arm, seconds=elapsed, output_length_bits=length.bit_length())
        return result

    results, orders = [], []
    rng = random.Random(20261009)
    for k in args.sizes:
        for arm in ['eager', 'eager_control', 'persistent']:
            sample(k, arm)
        for repeat in range(args.rounds):
            order = ['eager', 'eager_control', 'persistent']
            rng.shuffle(order)
            orders.append(dict(k=k, repeat=repeat, order=order))
            for arm in order:
                result = sample(k, arm)
                result['repeat'] = repeat
                results.append(result)
        summary = {arm: statistics.median(row['seconds'] for row in results
                                         if row['k'] == k and row['arm'] == arm)
                   for arm in ['eager', 'eager_control', 'persistent']}
        print(json.dumps(dict(k=k, median_seconds=summary)), flush=True)
    hashes = {}
    for filename in ['compressed_words.py', 'elimination_batch.py']:
        path = args.baseline_fast/'fastunknot'/filename
        hashes[filename] = hashlib.sha256(path.read_bytes()).hexdigest()
    report = dict(description='Artificial presentation kernel, identical serial donor sequence',
                  baseline_commit='9feb4346b4d050b305f825f0f7257f495960822a',
                  baseline_sha256=hashes, python=sys.version,
                  platform=platform.platform(), processor=platform.processor(),
                  measured_rounds=args.rounds, warmups_per_arm_size=1,
                  max_nodes=2_000_000, max_work=1_000_000_000,
                  orders=orders, samples=results)
    args.output.write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()
