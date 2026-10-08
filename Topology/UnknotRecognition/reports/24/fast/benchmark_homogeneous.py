"""Paired old-ranked/new-checked-homogeneous kernel and scanner timings.

Inputs and imports are prepared before timing. Each sample computes afresh;
kernel batches amortize timer overhead. Scanner timing includes order selection
and forces component contraction to exercise the changed code. This is raw
homology, not recognition; it is not a claim about the default sparse engine.
"""
import argparse
from contextlib import nullcontext
import json
from pathlib import Path
import platform
import random
import statistics
from time import perf_counter
from unittest.mock import patch

from fastunknot import Diagram, khovanov_rank
from fastunknot.frobenius.kernel import CompiledPlan
from fastunknot.frobenius.subset import pack, subset_product_fast, subset_product_ranked


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rounds', type=int, default=7)
    args = parser.parse_args()
    rng = random.Random(2026100803)
    inputs = []
    for m, a, b in ((8, 2, 3), (10, 3, 4), (12, 4, 5), (14, 5, 6),
                    (8, 4, 4), (10, 5, 5), (12, 6, 6), (14, 7, 7)):
        f, g = [pack((s for s in range(1 << m) if s.bit_count() == d and rng.randrange(2)), m)
                for d in (a, b)]
        inputs.append((f'homogeneous_{m}_{a}_{b}', m, f, g))
    inputs.append(('mixed_12', 12, rng.getrandbits(4096), rng.getrandbits(4096)))
    inputs.append(('sparse_12', 12, pack([1, 2], 12), pack([4, 8], 12)))
    rows = []
    for name, m, f, g in inputs:
        expected = subset_product_ranked(f, g, m)
        assert subset_product_fast(f, g, m) == expected
        cp = CompiledPlan.from_plan(tuple((1 << i, 1 << i, 1 << i, 0) for i in range(m)))
        for scope in ('product', 'full_component'):
            samples = []
            batch = max(1, min(16, 4096 // (1 << m)))
            for _ in range(args.rounds):
                arms = ['ranked', 'control', 'homogeneous']
                rng.shuffle(arms)
                sample = dict(order=arms, batch=batch)
                for arm in arms:
                    change = (patch('fastunknot.frobenius.subset.subset_product_fast', subset_product_ranked)
                              if arm != 'homogeneous' and scope == 'full_component' else nullcontext())
                    with change:
                        start = perf_counter()
                        for _ in range(batch):
                            if scope == 'full_component':
                                result = cp.apply(f, g, method='fast')
                            else:
                                fn = subset_product_fast if arm == 'homogeneous' else subset_product_ranked
                                result = fn(f, g, m)
                        sample[arm] = (perf_counter() - start) / batch
                    assert result == expected
                samples.append(sample)
            row = dict(name=name, scope=scope, variables=m, left=hex(f), right=hex(g),
                       result=hex(expected), samples=samples,
                       median_speedup=statistics.median(s['ranked']/s['homogeneous'] for s in samples),
                       median_aa=statistics.median(s['ranked']/s['control'] for s in samples))
            rows.append(row)
            print(name, scope, round(row['median_speedup'], 3), round(row['median_aa'], 3), flush=True)
    scans = []
    examples = Path(__file__).parent / 'examples'
    for name in ('trefoil', 'conway', 'kinoshita_terasaka', 'torus_3_5', 'hard_unknot_8'):
        diagram = Diagram.from_json(json.loads((examples / (name + '.json')).read_text()))
        expected = khovanov_rank(diagram.pd)['by_degree']
        samples, metrics = [], {}
        for _ in range(args.rounds):
            arms = ['ranked', 'control', 'homogeneous']
            rng.shuffle(arms)
            sample = dict(order=arms)
            for arm in arms:
                change = (patch('fastunknot.frobenius.subset.subset_product_fast', subset_product_ranked)
                          if arm != 'homogeneous' else nullcontext())
                with change:
                    start = perf_counter()
                    result = khovanov_rank(diagram.pd, composition='component-dense')
                    sample[arm] = perf_counter() - start
                assert result['by_degree'] == expected
                metrics[arm] = result
            samples.append(sample)
        row = dict(name=name, pd=diagram.pd, samples=samples, result=metrics['homogeneous'],
                   median_speedup=statistics.median(s['ranked']/s['homogeneous'] for s in samples),
                   median_aa=statistics.median(s['ranked']/s['control'] for s in samples))
        scans.append(row)
        print(name, 'scan', round(row['median_speedup'], 3), round(row['median_aa'], 3), flush=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(dict(python=platform.python_version(), seed=2026100803,
        rounds=args.rounds, scope=__doc__, kernels=rows, scans=scans), indent=2) + '\n')


if __name__ == '__main__':
    main()

