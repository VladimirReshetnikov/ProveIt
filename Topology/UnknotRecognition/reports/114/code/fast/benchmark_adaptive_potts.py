"""Adaptive vs ordinary/eager scalar queries, with separate full recognition.

Every timed arm includes Diagram construction and all order preparation.
Supplied random orders stress the scalar API; full recognition chooses its own
order. Limits are censored, never used as completed-query speedup ratios.
"""
import argparse
import importlib.util
from hashlib import sha256
import json
from pathlib import Path
import platform
import random
from statistics import median
import sys
from time import perf_counter

from fastunknot import Diagram, recognize
from fastunknot.adaptive_potts import adaptive_potts_exact
from fastunknot.filters import FilterLimit
from fastunknot.geometry import ScanLimit
from fastunknot.potts_exact import multiply, potts_exact
from fastunknot.separator_potts import separator_potts_exact
from separator_research.graphs import tree_medial

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT/'tests'))
from disk_grid import descending_grid


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    rng = random.Random(2623)
    cases = []
    for name in ('trefoil', 'conway', 'kinoshita_terasaka', 'hard_unknot_8', 'stress_braid5_36'):
        d = Diagram.from_json(json.loads((ROOT/'examples'/f'{name}.json').read_text()))
        cases.append((name, d.pd, None))
    cases.append(('tree-7', tree_medial(7).pd, None))
    order_rng = random.Random(2621)
    for m in (4, 6, 8, 10):
        pd = descending_grid(m)
        order = list(range(len(pd)))
        order_rng.shuffle(order)
        cases.extend([(f'grid-{m}', pd, None), (f'grid-{m}-random-order', pd, order)])
    cases.append(('grid-12', descending_grid(12), None))
    spec = importlib.util.spec_from_file_location('fastunknot._initial_adaptive_potts',
                                                ROOT/'adaptive_potts_research/initial_policy.py')
    initial = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(initial)
    evaluators = dict(ordinary=potts_exact, control=potts_exact,
                      eager=separator_potts_exact, adaptive=adaptive_potts_exact,
                      initial=initial.adaptive_potts_exact)
    rows = []
    for name, pd, supplied in cases:
        for scope in ('scalar', 'recognition'):
            if scope == 'recognition' and supplied is not None:
                continue
            samples = []
            for round_index in range(8):
                arms = [arm for arm in evaluators if scope == 'scalar' or arm != 'initial']
                rng.shuffle(arms)
                elapsed, results = {}, {}
                for arm in arms:
                    start = perf_counter()
                    def check():
                        if perf_counter()-start > 2:
                            raise ScanLimit('two-second scalar allowance')
                    if scope == 'recognition':
                        backend = {'ordinary': 'potts-exact', 'control': 'potts-exact',
                                   'eager': 'potts-separator', 'adaptive': 'potts-adaptive'}[arm]
                        result = recognize(Diagram.from_pd(pd), jones_backend=backend, seconds=2).to_json()
                    else:
                        statistics = {}
                        try:
                            result = evaluators[arm](Diagram.from_pd(pd), order=supplied, check=check,
                                                     statistics=statistics)
                            result['status'] = 'KNOTTED' if result['differs'] else 'INCONCLUSIVE'
                        except (FilterLimit, ScanLimit) as error:
                            result = dict(status='LIMIT', reason=str(error), statistics=statistics)
                    elapsed[arm] = perf_counter()-start
                    results[arm] = result
                complete = [r for r in results.values() if r['status'] not in ('LIMIT', 'UNKNOWN')]
                assert len({r['status'] for r in complete}) <= 1
                if scope == 'scalar' and complete:
                    ref = complete[0]
                    for result in complete[1:]:
                        # Shading/order can change Z and its normalizing factor.
                        assert multiply(ref['partition_function'], result['unknot_partition']) == \
                               multiply(result['partition_function'], ref['unknot_partition'])
                if round_index:
                    samples.append(dict(arm_order=arms, seconds=elapsed, results=results))
            complete_arms = [arm for arm in arms
                             if all(s['results'][arm]['status'] not in ('LIMIT', 'UNKNOWN') for s in samples)]
            ratios = {arm: median(s['seconds']['ordinary']/s['seconds'][arm] for s in samples)
                      for arm in complete_arms if arm != 'ordinary'} if 'ordinary' in complete_arms else {}
            row = dict(name=name, scope=scope, pd=pd, supplied_order=supplied, samples=samples,
                       median_seconds={arm: median(s['seconds'][arm] for s in samples) for arm in arms},
                       completed_arms=complete_arms, median_ordinary_over=ratios)
            rows.append(row)
            print(name, scope, ratios, complete_arms, flush=True)
    paths = ['benchmark_adaptive_potts.py', 'fastunknot/adaptive_potts.py',
             'fastunknot/potts_exact.py', 'fastunknot/separator_potts.py',
             'fastunknot/separator_order.py', 'fastunknot/recognize.py',
             'adaptive_potts_research/initial_policy.py']
    output = dict(seed=2623, order_seed=2621, rounds=7, warmups=1, python=platform.python_version(),
                  scope=__doc__, rows=rows,
                  source_sha256={p: sha256((ROOT/p).read_bytes()).hexdigest() for p in paths})
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2)+'\n')


if __name__ == '__main__':
    main()
