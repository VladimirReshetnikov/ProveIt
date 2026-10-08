"""Paired exact benchmarks: real diagram scans and explicit algebraic stress tests."""
from __future__ import annotations
import argparse
import copy
import json
import platform
from pathlib import Path
import random
import statistics
import sys
from time import perf_counter

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'fast'))
from fastunknot.diagram import Diagram
from fastunknot.ordering import best_scan_order
from fastunknot.perturbation import khovanov_perturbation, minimal_model
from fastunknot.scan import khovanov_rank
from fastunknot.scan_fast import FastScan


def nilpotent_stress(size):
    """Two-term complex d=I+xR over F2[x]/x²; provably contractible.

    This is an algebraic stress test, not a claim that it is a knot diagram.
    Its inverse is I+xR and its scalar shadow is exactly the identity.
    """
    rng = random.Random(481 + size)
    scan = FastScan(shape_cache=False)
    matching = scan.algebra.intern(((0, 1),))
    scan.points = frozenset((0, 1))
    scan.mid = [matching] * (2 * size)
    scan.deg = [0] * size + [1] * size
    scan.out = [{} for _ in scan.mid]
    scan.inc = [set() for _ in scan.mid]
    for a in range(size):
        for j in range(size):
            value = (1 if a == j else 0) ^ (2 if rng.getrandbits(1) else 0)
            if value:
                scan.out[a][size + j] = value
                scan.inc[size + j].add(a)
    scan.live = 2 * size
    return scan


def paired(functions, repeats):
    timings = [[], []]
    results = [None, None]
    for function in functions:
        function()
    for repeat in range(repeats):
        for index in ([0, 1] if repeat % 2 == 0 else [1, 0]):
            start = perf_counter()
            result = functions[index]()
            timings[index].append(perf_counter() - start)
            results[index] = result
    return {'seconds': timings, 'median_seconds': list(map(statistics.median, timings))}, results


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--repeats', type=int, default=5)
    parser.add_argument('--output', type=Path, default=ROOT / 'results' / 'perturbation_benchmarks.json')
    args = parser.parse_args()
    rows = []
    cases = []
    for filename in ('hard_unknot_8.json', 'conway.json', 'kinoshita_terasaka.json'):
        diagram = Diagram.from_json(json.loads((ROOT / 'fast/examples' / filename).read_text()))
        cases.append((filename.removesuffix('.json'), diagram))
    cases += [('torus_3_7', Diagram.from_braid(3, [1, 2] * 7)),
              ('torus_4_7', Diagram.from_braid(4, [1, 2, 3] * 7))]
    for name, diagram in cases:
        order = best_scan_order(diagram.pd, tries=min(diagram.crossings, 12))
        functions = [lambda: khovanov_rank(diagram.pd, order=order, shape_cache=False),
                     lambda: khovanov_perturbation(diagram.pd, order=order)]
        timing, results = paired(functions, args.repeats)
        assert results[0]['by_degree'] == results[1]['by_degree']
        rows.append(dict(case=name, kind='knot_scan', crossings=diagram.crossings,
                         by_degree=results[0]['by_degree'],
                         scalar_stats=results[0]['stats'], perturbation_stats=results[1]['stats'],
                         **timing))
    for size in (16, 32, 64, 128, 256):
        def scalar():
            scan = nilpotent_stress(size)
            scan.eliminate()
            assert scan.live == 0
            return dict(scan.stats)

        def perturb():
            model = minimal_model(nilpotent_stress(size))
            assert len(model['space']) == 0
            return model['stats']

        timing, results = paired([scalar, perturb], args.repeats)
        rows.append(dict(case='I_plus_xR_' + str(size), kind='algebraic_stress',
                         matrix_order=size, input_objects=2 * size,
                         scalar_stats=results[0], perturbation_stats=results[1], **timing))
    # Explicit deformation-retraction checks, including the actual radical term.
    certified = 0
    for size in range(1, 9):
        assert minimal_model(nilpotent_stress(size), certificate=True)['certified']
        certified += 1
    output = {'python': sys.version, 'platform': platform.platform(),
              'repeats': args.repeats, 'timing_scope': 'paired warmed kernel calls; fixed scan orders',
              'synthetic_warning': 'I+xR inputs are algebraic complexes, not knot diagrams',
              'certified_stress_sizes': certified, 'rows': rows}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2) + '\n')
    for row in rows:
        old, new = row['median_seconds']
        print(f"{row['case']:24s} {old:.6f} {new:.6f} speedup={old/new:.3f}")


if __name__ == '__main__':
    main()
