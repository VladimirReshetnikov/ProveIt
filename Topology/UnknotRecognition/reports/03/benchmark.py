#!/usr/bin/env python3
"""Reproduce small exact computations; timings are NOT a complexity proof.

Run from the extracted package: python benchmark.py
No external libraries or network access are required.
"""
from __future__ import annotations

import json
import platform
from pathlib import Path
import sys
from time import perf_counter

from unknot_lab.diagrams import PlanarDiagram
from unknot_lab.khovanov import fox_determinant, recognize
from unknot_lab.patterns import BallPattern, decide_ball_pattern, verify_violation

ROOT = Path(__file__).resolve().parent


def main() -> None:
    out = ROOT / 'results'
    out.mkdir(exist_ok=True)
    examples = []
    for name in ('unknot', 'curl', 'trefoil', 'figure_eight', 'torus_3_5',
                 'unknot_8_crossings'):
        pd = PlanarDiagram.from_json(json.loads((ROOT / 'examples' / (name + '.json'))
                                               .read_text()))
        start = perf_counter()
        r = recognize(pd, check_d2=True, determinant_filter=False)
        elapsed = perf_counter() - start
        row = {'name': name, 'seconds': elapsed, 'determinant': fox_determinant(pd), **r}
        examples.append(row)
        (out / (name + '.json')).write_text(json.dumps(row, indent=2) + '\n')
    growth = []
    for n in range(1, 9):
        pd = PlanarDiagram.from_braid(n + 1, range(1, n + 1))
        start = perf_counter()
        r = recognize(pd, check_d2=True, determinant_filter=False)
        assert r['is_unknot'] and r['resolutions'] == 2 ** n
        assert r['chain_generators'] == 3 ** n
        growth.append({'n': n, 'seconds': perf_counter() - start,
                       'resolutions': r['resolutions'],
                       'chain_generators': r['chain_generators'],
                       'logical_matrix_bits': r['logical_matrix_bits']})
    patterns = []
    for path in sorted((ROOT / 'examples').glob('pattern_*.json')):
        pattern = BallPattern.from_json(json.loads(path.read_text()))
        start = perf_counter()
        r = decide_ball_pattern(pattern)
        if not r['essential']:
            assert verify_violation(pattern, r['certificate'])
        patterns.append({'name': path.stem, 'seconds': perf_counter() - start, **r})
        (out / path.name).write_text(json.dumps(r, indent=2) + '\n')
    report = {'python': sys.version, 'platform': platform.platform(),
              'statement': 'Small-instance observations; no quasi-polynomial guarantee',
              'independent_full_khovanov_oracle_used': False,
              'knots': examples, 'stabilized_unknot_growth': growth, 'patterns': patterns}
    (out / 'validation.json').write_text(json.dumps(report, indent=2) + '\n')
    print('Wrote results/validation.json and individual example results.')
    for r in examples:
        print(f"{r['name']:24} n={r['crossings']:2} determinant={r['determinant']:2} "
              f"rank_F2={r['reduced_rank_f2']:2} {r['status']:10} {r['seconds']:.4f}s")


if __name__ == '__main__':
    main()
