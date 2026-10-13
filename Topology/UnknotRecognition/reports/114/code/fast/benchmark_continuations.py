"""Paired raw-backend comparisons, with explicit exact and capped contracts.

Includes order selection; excludes imports and Diagram construction. Graded and
ungraded Fitting use identical bounded searches. Earlier recognition filters
are bypassed. Independent full ranks validate every completed result.
"""
import argparse
import json
from pathlib import Path
import platform
import random
import statistics
from time import perf_counter

from fastunknot import Diagram, khovanov_rank, recognize
from fastunknot.barcode_scan import BarcodeScan, barcode_khovanov_rank, barcode_khovanov_decide
from fastunknot.component_scan import ComponentScan
from fastunknot.recovered_grading import recover_shifts
from fastunknot.scalar_split import fitting_khovanov_rank, fitting_khovanov_decide


def synthetic_counts():
    # Graded pure complexes; these are not presented as knot-derived scans.
    results = {}
    copies, layers = 31, 7
    for name, cls, options in [('literal', ComponentScan, {}), ('exact', BarcodeScan, {}),
                               ('decision', BarcodeScan, dict(rank_cap=3, length_cap=2))]:
        scan = cls(**options)
        matching = scan.algebra.intern(((0, 1), (2, 3)))
        scan.points = frozenset(range(4))
        scan.mid = [matching] * (copies * layers)
        scan.deg = [h for h in range(layers) for _ in range(copies)]
        scan.out = [{} for _ in scan.mid]
        for h in range(layers-1):
            for i in range(copies):
                scan.out[h*copies+i][(h+1)*copies+i] = 2
                if i+1 < copies:
                    scan.out[h*copies+i][(h+1)*copies+i+1] = 2
        scan.inc = [set() for _ in scan.mid]
        for v, row in enumerate(scan.out):
            for w in row:
                scan.inc[w].add(v)
        scan.live = len(scan.mid)
        scan.weights, scan.owner = [{0: 1}], [0]*scan.live
        recover_shifts(scan, list(range(scan.live)))
        scan.check_d_squared()
        scan._compress([0]*scan.live)
        scan.check_d_squared()
        results[name] = dict(objects=scan.live, weights=scan.weights, stats=scan.stats)
    assert [results[k]['objects'] for k in ('literal', 'exact', 'decision')] == [217, 7, 2]
    return dict(copies=copies, layers=layers, kind='synthetic graded pure component', results=results)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rounds', type=int, default=7)
    args = parser.parse_args()
    rng = random.Random(2026100807)
    examples = Path(__file__).parent/'examples'
    names = ('conway', 'kinoshita_terasaka', 'hard_unknot_8', 'stress_braid5_36', 'torus_3_5')
    cases = [(name, Diagram.from_json(json.loads((examples/(name+'.json')).read_text()))) for name in names]
    rows = []
    for name, d in cases:
        reference = khovanov_rank(d.pd)
        arms = dict(full=lambda: khovanov_rank(d.pd), control=lambda: khovanov_rank(d.pd),
                    barcode_exact=lambda: barcode_khovanov_rank(d.pd),
                    fitting_exact=lambda: fitting_khovanov_rank(d.pd),
                    fitting_ungraded=lambda: fitting_khovanov_rank(d.pd, preserve_grading=False),
                    barcode_decision=lambda: barcode_khovanov_decide(d.pd),
                    fitting_decision=lambda: fitting_khovanov_decide(d.pd))
        samples, results = [], {}
        for _ in range(args.rounds):
            order = list(arms)
            rng.shuffle(order)
            times = {}
            for arm in order:
                start = perf_counter()
                result = arms[arm]()
                times[arm] = perf_counter()-start
                if arm.endswith('decision'):
                    assert result['rank_capped'] == min(3, reference['rank'])
                else:
                    assert result['by_degree'] == reference['by_degree']
                results[arm] = {k: v for k, v in result.items() if k not in ('stages', 'witnesses')}
            samples.append(dict(order=order, seconds=times))
        ratios = {arm: statistics.median(r['seconds']['full']/r['seconds'][arm] for r in samples)
                  for arm in arms if arm != 'full'}
        grading_ratio = statistics.median(r['seconds']['fitting_ungraded']/r['seconds']['fitting_exact']
                                          for r in samples)
        # Collect witnesses separately so recording is not charged to one timing arm.
        witnessed = fitting_khovanov_rank(d.pd, record_witnesses=True, check_d_squared=True)
        rows.append(dict(name=name, pd=d.pd, default_method=recognize(d).method,
                         results=results, samples=samples, median_full_over=ratios,
                         median_ungraded_over_graded=grading_ratio, witnesses=witnessed['witnesses']))
        print(name, {k: round(v, 3) for k,v in ratios.items()},
              'grading', round(grading_ratio,3), 'splits', results['fitting_exact']['stats']['fitting_splits'],
              'intervals', results['fitting_exact']['stats']['barcode_components'], flush=True)
    output = dict(python=platform.python_version(), seed=2026100807, rounds=args.rounds,
                  scope=__doc__, cases=rows, synthetic=synthetic_counts())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2)+'\n')


if __name__ == '__main__':
    main()
