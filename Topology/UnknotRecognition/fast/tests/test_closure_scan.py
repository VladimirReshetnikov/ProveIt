"""Classical closure hypotheses, independent cube checks, and exact fallback."""
import copy
import json
from pathlib import Path
import random
import subprocess
import sys
from types import SimpleNamespace
import unittest

from fastunknot import Diagram, recognize
from fastunknot.closure_scan import (ClosureBudget, Work, certify_block,
                                    complete_matching, closure_khovanov_decide)
from fastunknot.geometry import ScanLimit
from fastunknot.scan_fast import FastScan

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'reports/28/src'))
from closure_reset.binary import rank, apply
from closure_reset.cube import Cube, interval_rank
from closure_reset.diagram import component_count, splice
from closure_reset.jet import certify_jet


def block():
    return SimpleNamespace(mid=[0]*6, deg=[0, 0, 1, 1, 2, 2],
                           out=[{2: 2, 3: 2}, {2: 2, 3: 2}, {4: 2, 5: 2},
                                {4: 2, 5: 2}, {}, {}],
                           inc=[set(), set(), {0, 1}, {0, 1}, {2, 3}, {2, 3}],
                           algebra=SimpleNamespace(pairs=[((0, 1), (2, 3), (4, 5))]))


class ClosureTests(unittest.TestCase):
    def test_mixed_matrix_formula_against_completed_cube(self):
        rng = random.Random(2802)
        cube = Cube(Diagram.from_braid(2, [1]*3).pd)
        for _ in range(40):
            scan = block()
            for row in scan.out:
                for v in row:
                    row[v] = rng.choice([2, 8, 32, 128, 10, 34, 130, 42, 170])
            before = copy.deepcopy(scan.__dict__)
            data = certify_block(scan, range(6))
            self.assertEqual(data['kappa'], certify_jet(scan, range(6)).kappa)
            self.assertEqual(scan.__dict__, before)
            maps = {f: cube.polynomial(f, cube.labels[:3]) for row in scan.out for f in row.values()}
            size, columns = cube.dimension, []
            for v, row in enumerate(scan.out):
                for x in range(size):
                    column = cube.d[x] << (size*v)
                    for w, f in row.items():
                        column ^= maps[f][x] << (size*w)
                    columns.append(column)
            self.assertFalse(any(apply(columns, c) for c in columns))
            self.assertEqual(len(columns)-2*rank(columns), data['kappa']*cube.homology_rank())

    def test_pure_even_bound_and_link_counterexample(self):
        scan = block()
        for row in scan.out:
            for w in row:
                row[w] = 6  # x_1+x_2
        data = certify_block(scan, range(6))
        self.assertEqual(data['closure_uniform_lower_bound'], 4)
        one = Diagram.from_braid(2, [1]).pd
        cube = Cube(list(one)+[tuple(x+2 for x in row) for row in one])
        theta = cube.polynomial(6, [0, 2])
        self.assertEqual(interval_rank(cube, theta, 3), 4)
        self.assertNotEqual(interval_rank(cube, theta, 3), 3*cube.homology_rank())

    def test_whole_block_domains(self):
        scan = block()
        with self.assertRaises(ValueError):
            certify_block(scan, [0, 2])
        with self.assertRaises(ValueError):
            certify_block(scan, [0, 0])
        scan.out[0][2] = 1
        self.assertIsNone(certify_block(scan, range(6)))
        scan.out[0][2] = 1 << 8
        with self.assertRaises(ValueError):
            certify_block(scan, range(6))
        scan.out[0][2] = 2
        scan.deg[2] = 4
        with self.assertRaises(ValueError):
            certify_block(scan, range(6))

    def test_splices_and_decisions_against_independent_cube(self):
        rng = random.Random(2803)
        accepted = resets = completions = 0
        while accepted < 60:
            strands = rng.randrange(2, 5)
            word = [rng.choice((-1, 1))*rng.randrange(1, strands)
                    for _ in range(rng.randrange(1, 9))]
            try:
                diagram = Diagram.from_braid(strands, word)
            except ValueError:
                continue
            accepted += 1
            order = list(range(diagram.crossings))
            rng.shuffle(order)
            expected = 'UNKNOT' if Cube(diagram.pd).homology_rank() == 2 else 'KNOTTED'
            for limit, reset in [(None, True), (None, False), (0, True)]:
                out = closure_khovanov_decide(diagram.pd, order=order, reset=reset,
                                              closure_max_work=limit, check_d_squared=True)
                self.assertEqual(out['status'], expected)
                self.assertLessEqual(out['closure_stats']['scanned'], diagram.crossings)
                resets += out['closure_stats']['resets']
                for e in out['events']:
                    if e['type'] == 'reset':
                        self.assertEqual('UNKNOT' if Cube(e['residual']).homology_rank() == 2 else 'KNOTTED', expected)
            scan = FastScan()
            for stage, i in enumerate(order[:-1], 1):
                scan.add_crossing(diagram.pd[i])
                suffix = [diagram.pd[j] for j in order[stage:]]
                for m in set(scan.mid)-{None}:
                    pairs = scan.algebra.pairs[m]
                    actual, count = complete_matching(suffix, pairs)
                    reference = splice(suffix, pairs)
                    self.assertEqual(count, component_count(reference))
                    self.assertEqual(Cube(actual).homology_rank(), Cube(reference).homology_rank())
                    completions += 1
        self.assertGreater(resets, 0)
        self.assertGreater(completions, 100)

    def test_single_survivor_resets_and_budget_exhaustion(self):
        diagram = Diagram.from_braid(8, list(range(1, 8)))
        order = list(range(7))
        full = closure_khovanov_decide(diagram.pd, order=order)
        self.assertEqual(full['status'], 'UNKNOT')
        self.assertEqual(full['closure_stats']['resets'], 6)
        self.assertEqual(full['closure_stats']['max_gap'], 1)
        limited = closure_khovanov_decide(diagram.pd, order=order,
                                        closure_max_work=full['closure_stats']['work_units']//2)
        self.assertEqual(limited['status'], 'UNKNOT')
        self.assertTrue(limited['closure_stats']['exhausted'])
        self.assertGreater(limited['closure_stats']['resets'], 0)
        self.assertLess(limited['closure_stats']['resets'], 6)
        self.assertEqual(limited['closure_stats']['scanned'], 7)

    def test_global_limits_and_validation(self):
        diagram = Diagram.from_braid(2, [1]*3)
        with self.assertRaises(ScanLimit):
            closure_khovanov_decide(diagram.pd, seconds=0, closure_max_work=0)
        with self.assertRaises(ScanLimit):
            Work(0, 0)()
        with self.assertRaises(ClosureBudget):
            Work(0, None)()
        for limit in (-1, True, 1.5):
            with self.assertRaises(ValueError):
                closure_khovanov_decide([], closure_max_work=limit)
            with self.assertRaises(ValueError):
                recognize(Diagram.from_pd([]), closure_max_work=limit)
        with self.assertRaises(ValueError):
            complete_matching([], ())
        with self.assertRaises(ValueError):
            complete_matching([(0, 1, 2, 3)], [(0, 1)])
        with self.assertRaises(ValueError):
            complete_matching([(0, 1, 0, 1)], ())
        with self.assertRaises(ValueError):
            closure_khovanov_decide(diagram.pd, order=[0, 0, 1])
        self.assertEqual(recognize(diagram, backend='closure', seconds=0).status, 'UNKNOWN')

    def test_cli_dispatch_and_invalid_budget(self):
        command = [sys.executable, '-B', '-m', 'fastunknot', 'recognize',
                   'examples/trefoil.json', '--backend', 'closure', '--no-reduction',
                   '--no-descending', '--no-seifert', '--no-braid', '--no-rational',
                   '--no-factor', '--no-modular', '--no-jones', '--no-alexander', '--no-r3']
        out = subprocess.run(command, text=True, capture_output=True)
        self.assertEqual(out.returncode, 0, out.stderr)
        result = json.loads(out.stdout)
        self.assertEqual(result['status'], 'KNOTTED')
        self.assertIn('closure', result['method'])
        out = subprocess.run(command+['--closure-max-work', '-1'], text=True, capture_output=True)
        self.assertEqual(out.returncode, 2)
        self.assertNotIn('Traceback', out.stderr)


if __name__ == '__main__':
    unittest.main()
