"""Paired whole-query costs of optional certified treewidth-two recognition."""
import argparse
import json
from pathlib import Path
import platform
import random
from statistics import median
import sys
from time import perf_counter

from fastunknot import Diagram, recognize
from separator_research.graphs import tree_medial

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT/'tests'))
from test_interlace import trefoil_sum


def cases():
    for name in ('trefoil', 'conway', 'kinoshita_terasaka', 'hard_unknot_8',
                 'grid_determinant_one_knot', 'unknot_braid40'):
        d = Diagram.from_json(json.loads((ROOT/'examples'/(name+'.json')).read_text()))
        yield name, d.pd
    for height in (6, 8, 10):
        yield f'tree-{height}', tree_medial(height).pd
    for size in (101, 501, 2001):
        yield f'mixed-two-braid-{size}', Diagram.from_braid(2, [1, -1]*(size//2)+[1]).pd
    yield 'trefoil-sum-40', trefoil_sum(40).pd
    # Mixed-sign connected sum with s=0: no false genus-zero inference.
    d = trefoil_sum(40)
    yield 'mixed-trefoil-sum-40', tuple(row[1:]+row[:1] if i >= 60 else row
                                     for i, row in enumerate(d.pd))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    rng, rows = random.Random(2643), []
    for name, pd in cases():
        samples = []
        for repetition in range(8):
            sequence = ['before', 'control', 'after']
            rng.shuffle(sequence)
            elapsed, results = {}, {}
            for arm in sequence:
                # Fresh validated PD strips source hints and discards caches.
                start = perf_counter()
                d = Diagram.from_pd(pd)
                result = recognize(d, use_treewidth_two=arm == 'after')
                elapsed[arm] = perf_counter()-start
                results[arm] = result
            assert results['before'].status == results['control'].status == results['after'].status
            assert results['after'].status != 'UNKNOWN'
            if repetition:
                samples.append(dict(order=sequence, seconds=elapsed))
        row = dict(name=name, crossings=len(pd), pd=pd, status=results['after'].status,
            methods={arm: result.method for arm, result in results.items()},
            treewidth_two=results['after'].evidence.get('treewidth_two'), samples=samples,
            median_seconds={arm: median(s['seconds'][arm] for s in samples) for arm in sequence},
            median_paired_speedup=median(s['seconds']['before']/s['seconds']['after'] for s in samples),
            median_aa_ratio=median(s['seconds']['before']/s['seconds']['control'] for s in samples))
        rows.append(row)
        print(name, {a: round(t*1000, 3) for a, t in row['median_seconds'].items()},
              'speedup', round(row['median_paired_speedup'], 3), flush=True)
    args.output.write_text(json.dumps(dict(scope='validation plus complete recognition; source-free PD',
        python=sys.version, platform=platform.platform(), seed=2643, rounds=7, excluded_warmups=1,
        before='recognize defaults; use_treewidth_two=False',
        after='recognize defaults; use_treewidth_two=True, treewidth_two_seconds=0.1',
        note='warm interpreter; imports, including the optional module, warmed before measured rounds',
        rows=rows), indent=2)+'\n')


if __name__ == '__main__':
    main()
