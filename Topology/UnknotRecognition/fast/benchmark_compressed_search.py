"""Whole-query A/A/B audit of explicit versus compressed group discovery."""
import argparse
import json
import platform
import random
from statistics import median
import sys
from time import perf_counter

from benchmark_compressed_words import cases
from fastunknot import Diagram, recognize
from fastunknot.compressed_words import WordArena
from fastunknot.compressed_search import _search


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    rng, rows = random.Random(2688), []
    for name, diagram in cases():
        samples = []
        for repetition in range(6):
            order, measurements = ['explicit', 'control', 'compressed-search'], {}
            rng.shuffle(order)
            for arm in order:
                start = perf_counter()
                result = recognize(Diagram.from_pd(diagram.pd), use_group=True,
                    group_relators=True, group_compressed_search=arm == 'compressed-search',
                    group_seconds=10, group_max_work=10000000, seconds=12, max_objects=50000)
                evidence = result.evidence.get('group', {})
                measurements[arm] = dict(seconds=perf_counter()-start, status=result.status,
                    method=result.method, search_backend=evidence.get('search_backend'),
                    search_stats=evidence.get('search_stats'),
                    verification_backend=evidence.get('verification_backend'))
            if repetition:
                samples.append(dict(order=order, measurements=measurements))
        row = dict(name=name, pd=diagram.pd, samples=samples,
            median_seconds={arm: median(s['measurements'][arm]['seconds'] for s in samples)
                            for arm in measurements})
        print(name, row['median_seconds'], flush=True)
        rows.append(row)
    kernels = []
    for bits in (16, 64, 256, 1024):
        samples = []
        for repetition in range(6):
            start, arena, n = perf_counter(), WordArena(), 2**bits
            root = arena.power(arena.from_word([1, 2]), n)
            counts, graph = arena.summarize([root, root], whitehead=True)
            assert counts == {1: 2*n, 2: 2*n} and graph[1][-2] == 2*n
            assert arena.singletons([root]) == [[]]
            root = arena.concat(arena.letter(1), arena.power(arena.letter(2), n))
            moves = []
            assert _search(arena, [root], {1, 2}, moves, max_letters=4)
            if repetition:
                samples.append(dict(seconds=perf_counter()-start,
                    nodes=len(arena.rules)-1, work=arena.stats['work'], moves=moves))
        kernels.append(dict(exponent_bits=bits, samples=samples))
    with open(args.output, 'w') as out:
        json.dump(dict(python=sys.version, platform=platform.platform(), seed=2688,
            measured_rounds=5, excluded_warmups=1, group_seconds=10, global_seconds=12,
            max_work=10000000, max_letters=200000, max_nodes=100000,
            scope='Fresh PD validation and whole recognition, including independent certificate replay',
            censoring='Any INCONCLUSIVE record is a censored query, not a completed recognition time',
            kernel_scope='Synthetic compressed group presentations and summaries, not hard knot inputs',
            rows=rows, kernels=kernels), out, indent=2)
        out.write('\n')


if __name__ == '__main__':
    main()
