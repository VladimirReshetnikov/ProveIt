"""Cost of collision-free identity and full recovery versus fixed q=6.

Seven shuffled paired rounds follow one excluded warmup. Each arm constructs
a fresh Diagram and includes order preparation. These are invariant queries,
not full recognition benchmarks; the arms deliberately compute different data.
"""
import argparse
import json
from pathlib import Path
import platform
import random
from statistics import median
import sys
from time import perf_counter

from fastunknot import Diagram
from fastunknot.adaptive_potts import adaptive_potts_exact
from fastunknot.faithful_jones import faithful_potts_exact
from fastunknot.filters import FilterLimit
from fastunknot.geometry import ScanLimit
from check_potts_independent import evaluate, laurent_jones, times
from separator_research.graphs import tree_medial

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT/'tests'))
from disk_grid import descending_grid


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    cases = []
    for name in ('trefoil', 'conway', 'kinoshita_terasaka', 'hard_unknot_8', 'stress_braid5_36'):
        cases.append((name, Diagram.from_json(json.loads((ROOT/'examples'/(name+'.json')).read_text())).pd, None))
    cases.append(('weaving-10', Diagram.from_braid(3, [1, -2]*5).pd, None))
    cases.append(('tree-7', tree_medial(7).pd, None))
    rng = random.Random(2630)
    for m in (6, 8, 10):
        pd = descending_grid(m)
        order = list(range(len(pd)))
        rng.shuffle(order)
        cases.extend([(f'grid-{m}', pd, None), (f'grid-{m}-random', pd, order)])
    rows = []
    for name, pd, order in cases:
        oracle = laurent_jones(Diagram.from_pd(pd)) if len(pd) <= 12 else None
        samples = []
        for repetition in range(8):
            arms = ['fixed6', 'control6', 'identity', 'polynomial']
            rng.shuffle(arms)
            elapsed, summary, results = {}, {}, {}
            for arm in arms:
                start = perf_counter()

                def check():
                    if perf_counter()-start > 2:
                        raise ScanLimit('two-second query allowance')

                stats = {}
                try:
                    options = dict(order=order, check=check, statistics=stats)
                    if arm in ('fixed6', 'control6'):
                        result = adaptive_potts_exact(Diagram.from_pd(pd), **options)
                    else:
                        result = faithful_potts_exact(Diagram.from_pd(pd),
                                                      include_polynomial=arm == 'polynomial', **options)
                except (FilterLimit, ScanLimit) as exc:
                    elapsed[arm] = perf_counter()-start
                    summary[arm] = dict(status='CAPPED', reason=str(exc), policy=stats.get('ordering_policy'))
                    continue
                elapsed[arm] = perf_counter()-start
                results[arm] = result
                summary[arm] = dict(status='COMPLETE', differs=result['differs'],
                                    transitions=result['transitions'], peak_states=result['peak_states'],
                                    coefficient_bits=result['max_coefficient_bits'],
                                    policy=result['ordering_policy'])
                if oracle is not None:
                    assert tuple(result['partition_function']) == times(
                        evaluate(oracle, result['q']), result['unknot_partition'], result['q'])
            if 'fixed6' in results and 'control6' in results:
                assert results['fixed6'] == results['control6']
            if 'polynomial' in results:
                full = results['polynomial']
                poly = {-k: int(v, 16) for k, v in full['jones_polynomial']['coefficients_hex']}
                if oracle is not None:
                    assert poly == oracle
                if 'fixed6' in results:
                    fixed = results['fixed6']
                    assert tuple(fixed['partition_function']) == times(
                        evaluate(poly, 6), fixed['unknot_partition'], 6)
                if 'identity' in results:
                    assert full['partition_function'] == results['identity']['partition_function']
                summary['polynomial']['polynomial'] = full['jones_polynomial']
            if repetition:
                samples.append(dict(order=arms, seconds=elapsed, result=summary))
        medians = {arm: median(s['seconds'][arm] for s in samples)
                   for arm in ('fixed6', 'control6', 'identity', 'polynomial')}
        rows.append(dict(name=name, crossings=len(pd), pd=pd, supplied_order=order,
                         independent_cube_checked=oracle is not None,
                         median_seconds=medians, samples=samples))
        print(name, {arm: round(1000*v, 3) for arm, v in medians.items()}, flush=True)
    args.output.write_text(json.dumps(dict(python=sys.version, platform=platform.platform(),
        seed=2630, rounds=7, excluded_warmups=1, max_states=4096, max_transitions=200000,
        seconds_per_query=2, scope='invariant queries with different output guarantees', rows=rows), indent=2)+'\n')


if __name__ == '__main__':
    main()
