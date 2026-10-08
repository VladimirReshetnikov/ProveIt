"""Ablate certified-prefix bisection and bounded direct cancellation walks."""
import argparse
from functools import partial
import json
from pathlib import Path
import platform
import random
from statistics import median
import sys
from time import perf_counter
from unittest.mock import patch

from benchmark_compressed_words import cases
from benchmark_indexed_equality import baseline_arena, MODULE
from fastunknot import Diagram, recognize, compressed_search, compressed_group
from fastunknot.compressed_words import WordArena

BASELINE = '97587b36627c9b34b64ecd542e58ebbdd2bffef4'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    old = baseline_arena(BASELINE)
    factories = {'baseline': old, 'baseline-control': old,
                 'suffix-bisection': partial(WordArena, prefix_probe_steps=0),
                 'adaptive-prefix': WordArena, 'explicit': WordArena}
    rng, rows = random.Random(2692), []
    for name, diagram in cases():
        samples = []
        for repetition in range(6):
            order, measurements = list(factories), {}
            rng.shuffle(order)
            for arm in order:
                with patch.object(compressed_search, 'WordArena', factories[arm]), \
                     patch.object(compressed_group, 'WordArena', factories[arm]):
                    start = perf_counter()
                    result = recognize(Diagram.from_pd(diagram.pd), use_group=True,
                        group_relators=True, group_compressed_search=arm != 'explicit',
                        group_seconds=15, group_max_work=20000000, seconds=18, max_objects=50000)
                    group = result.evidence.get('group', {})
                    measurements[arm] = dict(seconds=perf_counter()-start,
                        status=result.status, method=result.method,
                        search_backend=group.get('search_backend'),
                        verification_backend=group.get('verification_backend'),
                        search_stats=group.get('search_stats'))
            if repetition:
                samples.append(dict(order=order, measurements=measurements))
        row = dict(name=name, pd=diagram.pd, samples=samples,
            median_seconds={arm: median(s['measurements'][arm]['seconds'] for s in samples)
                            for arm in factories})
        print(name, row['median_seconds'], flush=True)
        rows.append(row)
    kernels = []
    for kind in ('shared-prefix', 'noncanonical-cancellation'):
        for bits in (16, 64, 128):
            samples = []
            for repetition in range(6):
                order, measurements = [x for x in factories if x != 'explicit'], {}
                rng.shuffle(order)
                for arm in order:
                    start, arena, n = perf_counter(), factories[arm](), 2**bits
                    if kind == 'shared-prefix':
                        prefix = arena.power(arena.from_word([1, 2]), n)
                        a = arena.concat(prefix, arena.letter(3))
                        b = arena.concat(prefix, arena.letter(4))
                        assert arena.lcp(a, b) == 2*n
                    else:
                        a = arena.concat(arena.power(arena.from_word([1, 2]), n), arena.letter(1))
                        b = arena.concat(arena.letter(1), arena.power(arena.from_word([2, 1]), n))
                        assert arena.equal(a, b)
                        assert arena.reduce(arena.concat(a, arena.inverse(b))) == 0
                    measurements[arm] = dict(seconds=perf_counter()-start,
                        nodes=len(arena.rules)-1, stats=arena.stats.copy())
                if repetition:
                    samples.append(dict(order=order, measurements=measurements))
            kernels.append(dict(kind=kind, exponent_bits=bits, samples=samples))
            print(kind, bits, {arm: median(s['measurements'][arm]['seconds'] for s in samples)
                              for arm in order}, flush=True)
    args.output.write_text(json.dumps(dict(python=sys.version, platform=platform.platform(),
        baseline_commit=BASELINE, baseline_module=MODULE, seed=2692,
        measured_rounds=5, excluded_warmups=1, equality_probe_steps=64, prefix_probe_steps=64,
        group_seconds=15, global_seconds=18, max_work=20000000,
        max_letters=200000, max_nodes=100000, max_objects=50000,
        query_scope='Fresh PD validation and whole recognition including independently reconstructed replay',
        kernel_scope='Full grammar construction plus LCP or exact equality and cancellation; fresh state',
        censoring='INCONCLUSIVE is a censored observation, not completed recognition time',
        rows=rows, kernels=kernels), indent=2)+'\n')


if __name__ == '__main__':
    main()
