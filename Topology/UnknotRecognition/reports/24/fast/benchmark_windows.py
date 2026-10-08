"""Exact windows versus full homology, and bounded probes versus full decisions.

Preparation/imports are excluded. Order and mirror selection are included.
Raw window and full rank have different output contracts; both are checked
against full homology. The decision arms disable earlier filters explicitly
to measure fallback behavior, while recording the actual default method.
Every comparison has a shuffled identical baseline/control arm.
"""
import argparse
import json
from pathlib import Path
import platform
import random
import statistics
from time import perf_counter

from fastunknot import Diagram, recognize, khovanov_rank
from fastunknot.window_bounds import khovanov_window_auto

NO_FILTERS = dict(use_braid=False, use_seifert=False, use_reduction=False,
                  use_descending=False, use_alexander=False, use_jones=False, use_factorization=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rounds', type=int, default=7)
    args = parser.parse_args()
    rng = random.Random(2026100806)
    examples = Path(__file__).parent / 'examples'
    cases = [(name, Diagram.from_json(json.loads((examples/(name+'.json')).read_text())))
             for name in ('conway', 'kinoshita_terasaka', 'hard_unknot_8', 'stress_braid5_36')]
    cases += [('torus_4_7', Diagram.from_braid(4, [-1, -2, -3]*7)),
              ('two_strand_201', Diagram.from_braid(2, [1]*201))]
    rows = []
    for name, diagram in cases:
        shift = diagram.signs().count(-1)
        expected = khovanov_rank(diagram.pd, seconds=30)
        expected_window = {h: count for h, count in expected['by_degree'].items() if h == shift}
        status = 'UNKNOT' if expected['rank'] == 2 else 'KNOTTED'
        samples, metrics = [], {}
        arms = ['full', 'control', 'window', 'probe_zero', 'probe_widen']
        for _ in range(args.rounds):
            rng.shuffle(arms)
            sample = dict(order=list(arms))
            for arm in arms:
                start = perf_counter()
                if arm == 'window':
                    result = khovanov_window_auto(diagram, shift, shift, seconds=30)
                    elapsed = perf_counter() - start
                    assert result['by_degree'] == expected_window
                elif arm.startswith('probe'):
                    verdict = recognize(diagram, window_radius=0 if arm == 'probe_zero' else 4,
                                        window_seconds=2, seconds=30, **NO_FILTERS)
                    elapsed = perf_counter() - start
                    assert verdict.status == status
                    result = verdict.to_json()
                    for attempt in result['evidence']['khovanov_windows']['attempts']:
                        if 'unreduced_rank_by_normalized_degree' in attempt:
                            radius = attempt['radius']
                            selected = {h-shift: count for h, count in expected['by_degree'].items()
                                        if shift-radius <= h <= shift+radius}
                            assert attempt['unreduced_rank_by_normalized_degree'] == selected
                else:
                    verdict = recognize(diagram, seconds=30, **NO_FILTERS)
                    elapsed = perf_counter() - start
                    assert verdict.status == status
                    result = verdict.to_json()
                if arm != 'window' and 'khovanov' in result['evidence']:
                    assert result['evidence']['khovanov']['unreduced_rank_by_cube_degree'] == expected['by_degree']
                sample[arm] = elapsed
                metrics[arm] = result
            samples.append(sample)
        default = recognize(diagram)
        row = dict(name=name, pd=diagram.pd, default_method=default.method, expected=expected,
                   samples=samples, results=metrics,
                   median_full_over_window=statistics.median(s['full']/s['window'] for s in samples),
                   median_zero_speedup=statistics.median(s['full']/s['probe_zero'] for s in samples),
                   median_widen_speedup=statistics.median(s['full']/s['probe_widen'] for s in samples),
                   median_aa=statistics.median(s['full']/s['control'] for s in samples))
        rows.append(row)
        print(name, round(row['median_full_over_window'], 3), round(row['median_zero_speedup'], 3),
              round(row['median_widen_speedup'], 3), round(row['median_aa'], 3),
              metrics['probe_zero']['method'], metrics['probe_widen']['method'], flush=True)
    diagram = dict(cases)['stress_braid5_36']
    budget = 10000
    baseline = recognize(diagram, max_objects=budget, seconds=30, **NO_FILTERS)
    probed = recognize(diagram, max_objects=budget, window_radius=0, window_seconds=2,
                       seconds=30, **NO_FILTERS)
    assert baseline.status == 'UNKNOWN' and probed.status == 'KNOTTED'
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(dict(python=platform.python_version(), seed=2026100806,
        rounds=args.rounds, scope=__doc__, cases=rows,
        resource_comparison=dict(max_objects=budget, baseline=baseline.to_json(), window=probed.to_json())),
        indent=2) + '\n')


if __name__ == '__main__':
    main()

