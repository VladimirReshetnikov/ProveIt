"""Paired full-Jones queries before/after skipping redundant identity decoding."""
import argparse
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import platform
import random
from statistics import median
import sys
from time import perf_counter

from fastunknot import Diagram
from fastunknot.faithful_jones import faithful_potts_exact
from separator_research.graphs import tree_medial

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT/'tests'))
from disk_grid import descending_grid


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    baseline_path = ROOT/'jones_research/before_identity_shortcut.py'
    spec = importlib.util.spec_from_file_location('fastunknot._before_identity_shortcut', baseline_path)
    before = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(before)
    arms = dict(before=before.faithful_potts_exact, control=before.faithful_potts_exact,
                after=faithful_potts_exact)
    cases = []
    for name in ('trefoil', 'conway', 'hard_unknot_8'):
        cases.append((name, Diagram.from_json(json.loads((ROOT/'examples'/(name+'.json')).read_text())).pd, None))
    cases.extend((f'tree-{power}', tree_medial(power).pd, None) for power in (6, 7))
    cases.append(('grid-10', descending_grid(10), None))
    shuffled = list(range(64))
    random.Random(2631).shuffle(shuffled)
    cases.append(('grid-8-random', descending_grid(8), shuffled))
    rng, rows = random.Random(2632), []
    for name, pd, order in cases:
        samples = []
        for repetition in range(8):
            sequence = list(arms)
            rng.shuffle(sequence)
            elapsed, results = {}, {}
            for arm in sequence:
                start = perf_counter()
                results[arm] = arms[arm](Diagram.from_pd(pd), order=order, include_polynomial=True)
                elapsed[arm] = perf_counter()-start
            assert results['before'] == results['control'] == results['after']
            if repetition:
                samples.append(dict(order=sequence, seconds=elapsed))
        result = results['after']
        row = dict(name=name, crossings=len(pd), pd=pd, supplied_order=order,
                   polynomial_identity=result['polynomial_identity'],
                   polynomial=result['jones_polynomial'], transitions=result['transitions'],
                   ordering_policy=result['ordering_policy'], samples=samples,
                   median_seconds={arm: median(s['seconds'][arm] for s in samples) for arm in arms},
                   median_paired_speedup=median(s['seconds']['before']/s['seconds']['after'] for s in samples),
                   median_aa_ratio=median(s['seconds']['before']/s['seconds']['control'] for s in samples))
        rows.append(row)
        print(name, {k: round(v*1000, 3) for k, v in row['median_seconds'].items()},
              'paired speedup', round(row['median_paired_speedup'], 3), flush=True)
    args.output.write_text(json.dumps(dict(scope='full polynomial queries, identical complete results',
        python=sys.version, platform=platform.platform(), seed=2632, rounds=7, excluded_warmups=1,
        baseline_commit='58006240adfeccea75c991249914611d6d96448c',
        baseline_sha256=sha256(baseline_path.read_bytes()).hexdigest(),
        baseline_file='jones_research/before_identity_shortcut.py', rows=rows), indent=2)+'\n')


if __name__ == '__main__':
    main()
