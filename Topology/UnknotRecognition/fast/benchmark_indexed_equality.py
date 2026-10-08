"""Controlled comparison of equality scheduling and bounded adaptive probes."""
import argparse
from functools import partial
import json
from pathlib import Path
import platform
import random
from statistics import median
import subprocess
import sys
from time import perf_counter
from types import ModuleType
from unittest.mock import patch

from benchmark_compressed_words import cases
from fastunknot import Diagram, recognize, compressed_search, compressed_group
from fastunknot.compressed_words import WordArena

BASELINE = 'e4f471c971359b74d30d5f85284850d462a74dfd'
MODULE = 'Topology/UnknotRecognition/fast/fastunknot/compressed_words.py'


def baseline_arena():
    """Load the recorded, trusted repository version without changing checkout."""
    source = subprocess.check_output(['git', 'show', f'{BASELINE}:{MODULE}'], text=True)
    module = ModuleType('recorded_compressed_words')
    exec(compile(source, f'{BASELINE}:{MODULE}', 'exec'), module.__dict__)
    return module.WordArena


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    old = baseline_arena()
    factories = {'baseline': old, 'baseline-control': old,
                 'indexed': partial(WordArena, equality_probe_steps=0),
                 'adaptive': WordArena, 'explicit': WordArena}
    rng, rows = random.Random(2690), []
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
    for bits in (8, 32, 100):
        samples = []
        for repetition in range(6):
            order, measurements = [x for x in factories if x != 'explicit'], {}
            rng.shuffle(order)
            for arm in order:
                start, arena = perf_counter(), factories[arm]()
                n = 2**bits
                a = arena.concat(arena.power(arena.from_word([1, 2]), n), arena.letter(1))
                b = arena.concat(arena.letter(1), arena.power(arena.from_word([2, 1]), n))
                assert arena.equal(a, b)
                assert arena.reduce(arena.concat(a, arena.inverse(b))) == 0
                measurements[arm] = dict(seconds=perf_counter()-start,
                    nodes=len(arena.rules)-1, stats=arena.stats.copy())
            if repetition:
                samples.append(dict(order=order, measurements=measurements))
        kernels.append(dict(exponent_bits=bits, samples=samples))
    args.output.write_text(json.dumps(dict(python=sys.version, platform=platform.platform(),
        baseline_commit=BASELINE, baseline_module=MODULE, seed=2690,
        measured_rounds=5, excluded_warmups=1, probe_steps=64,
        group_seconds=15, global_seconds=18, max_work=20000000,
        max_letters=200000, max_nodes=100000, max_objects=50000,
        query_scope='Fresh PD validation and whole recognition including independently reconstructed replay',
        kernel_scope='Full construction, equality and cancellation of noncanonical exponentially long parses',
        censoring='INCONCLUSIVE is a censored observation, not completed recognition time',
        rows=rows, kernels=kernels), indent=2)+'\n')


if __name__ == '__main__':
    main()
