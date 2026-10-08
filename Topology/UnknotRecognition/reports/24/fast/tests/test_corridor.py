"""Independent correctness and asymptotic-regression checks for corridor transfer."""
import importlib.util
import contextlib
import io
import json
from pathlib import Path
import random
import unittest

from fastunknot import Diagram
from fastunknot.corridor import AdaptiveCorridorScan, CorridorScan, corridor_transfer
from fastunknot.diagram import DiagramError
from fastunknot.geometry import ScanLimit
from fastunknot.graded import GradedScan
from fastunknot.ordering import best_scan_order
from fastunknot.scan import khovanov_rank


ROOT = Path(__file__).resolve().parents[1]
REFERENCE = ROOT.parent / 'reference' / 'graded_transfer_v1.py'


def prior_module():
    spec = importlib.util.spec_from_file_location('corridor_frozen_prior', REFERENCE)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def shared_suffix(sources=5, width=7, dead=0):
    """The exact graded R_3 family from the proof, with optional dead leaves."""
    scan = GradedScan(shape_cache=False)
    matching = scan.algebra.intern(((0, 1), (2, 3), (4, 5)))
    scan.points = frozenset(range(6))
    mid, deg, quantum, out = [], [], [], []

    def add(h, q):
        ident = len(mid)
        mid.append(matching)
        deg.append(h)
        quantum.append(q)
        out.append({})
        return ident

    ss = [add(0, 0) for _ in range(sources)]
    target = add(1, 6)
    l0, b0 = add(0, 2), add(1, 2)
    out[l0][b0] = 1
    for s in ss:
        out[s][b0] = 2
    for _ in range(width):
        li, bi = add(0, 4), add(1, 4)
        out[li][bi] = 1
        out[l0][bi] = 4
        out[li][target] = 16
    for _ in range(dead):
        li, bi = add(0, 4), add(1, 4)
        out[li][bi] = 1
        out[l0][bi] = 4
    scan.mid, scan.deg, scan.qshift, scan.out = mid, deg, quantum, out
    scan.inc = [set() for _ in mid]
    for a, row in enumerate(out):
        for b in row:
            scan.inc[b].add(a)
    scan.live = len(mid)
    return scan


class CorridorTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.prior = prior_module()

    def assert_same_transfer(self, scan, certificates=False):
        expected = self.prior.transfer(scan, certificates=certificates)
        for mode in ('forward', 'reverse', 'auto'):
            for prune in (False, True):
                with self.subTest(mode=mode, prune=prune):
                    actual = corridor_transfer(scan, mode=mode, prune=prune)
                    for key in ('mid', 'deg', 'q', 'out'):
                        self.assertEqual(actual[key], expected[key])
                    self.assertLessEqual(actual['stats']['propagations'],
                                         actual['stats']['chosen_bound'])
                    if certificates:
                        check = dict(expected, out=actual['out'])
                        self.assertEqual(len(self.prior.check_certificate(scan, check)), 8)

    def test_complete_contraction_certificates(self):
        for sources, width in ((1, 1), (2, 2), (3, 5)):
            scan = shared_suffix(sources, width, dead=2)
            scan.check_grading()
            scan.check_d_squared()
            self.assert_same_transfer(scan, certificates=True)

    def test_parity_cancellation_is_not_boolean_reachability(self):
        odd = corridor_transfer(shared_suffix(3, 5))
        even = corridor_transfer(shared_suffix(3, 4))
        self.assertEqual(sum(map(len, odd['out'])), 3)
        self.assertTrue(all(value == 128 for row in odd['out'] for value in row.values()))
        self.assertFalse(any(even['out']))
        self.assertGreater(even['stats']['retained_edges'], 0)

    def test_directional_linear_work_family(self):
        for size in (3, 9, 27):
            scan = shared_suffix(size, size)
            forward = corridor_transfer(scan, mode='forward')
            reverse = corridor_transfer(scan, mode='reverse')
            self.assertEqual(forward['out'], reverse['out'])
            self.assertEqual(forward['stats']['geometric_propagations'], size * (1 + 2 * size))
            self.assertEqual(reverse['stats']['geometric_propagations'], size + 2 * size)
            self.assertLess(reverse['stats']['propagations'], forward['stats']['propagations'])

    def test_dead_branches_are_exactly_removed(self):
        live = corridor_transfer(shared_suffix(1, 1, dead=40), mode='forward', prune=True)
        full = corridor_transfer(shared_suffix(1, 1, dead=40), mode='forward', prune=False)
        self.assertEqual(live['out'], full['out'])
        self.assertEqual(live['stats']['geometric_propagations'], 3)
        self.assertEqual(full['stats']['geometric_propagations'], 43)
        self.assertLess(live['stats']['retained_vertices'], full['stats']['retained_vertices'])

    def test_real_prefixes_and_typed_composition(self):
        for name in ('trefoil', 'figure_eight', 'hard_unknot_8', 'conway'):
            diagram = Diagram.from_json(json.loads((ROOT / 'examples' / f'{name}.json').read_text()))
            scan = GradedScan(shape_cache=False)
            for index in best_scan_order(diagram.pd):
                scan.add_crossing(diagram.pd[index], reduce_now=False)
                self.assert_same_transfer(scan, certificates=diagram.crossings <= 4)
                scan.eliminate()

    def test_random_orders_against_independent_set_engine(self):
        rng = random.Random(842026)
        checked = 0
        while checked < 40:
            strands = rng.randrange(2, 5)
            word = [rng.choice((-1, 1)) * rng.randrange(1, strands)
                    for _ in range(rng.randrange(1, 10))]
            try:
                diagram = Diagram.from_braid(strands, word)
            except DiagramError:
                continue
            order = list(range(diagram.crossings))
            rng.shuffle(order)
            expected = khovanov_rank(diagram.pd, order=order, algebra='sets', pivot='lifo')
            for reduction in ('corridor', 'corridor-adaptive'):
                result = khovanov_rank(diagram.pd, order=order, reduction=reduction,
                                       check_d_squared=True)
                self.assertEqual(result['by_degree'], expected['by_degree'])
            checked += 1

    def test_partially_cancelled_input_and_atomic_deadline(self):
        scan = shared_suffix(9, 9)
        GradedScan.eliminate(scan, update_budget=0)
        self.assert_same_transfer(scan)
        state = (scan.mid[:], scan.deg[:], scan.qshift[:], [dict(r) if r is not None else None for r in scan.out])
        scan.deadline = 0
        with self.assertRaises(ScanLimit):
            corridor_transfer(scan)
        self.assertEqual(state, (scan.mid, scan.deg, scan.qshift, scan.out))

    def test_tail_component_engine_and_invalid_options(self):
        diagram = Diagram.from_braid(3, [1, 1, -2, 1, -2, 1])
        expected = khovanov_rank(diagram.pd)
        for reduction in ('corridor', 'corridor-adaptive'):
            for tail in (0, 2):
                actual = khovanov_rank(diagram.pd, reduction=reduction, tail=tail,
                                       composition='component-dense')
                self.assertEqual(actual['by_degree'], expected['by_degree'])
        for options in ({'race': 2}, {'algebra': 'sets'}, {'pivot': 'lifo'}):
            with self.assertRaises(ValueError):
                khovanov_rank(diagram.pd, reduction='corridor', **options)
        with self.assertRaises(ValueError):
            CorridorScan(mode='guessed')

    def test_sparse_scalar_and_boolean_direction_policies(self):
        scan = shared_suffix(9, 9, dead=11)
        expected = self.prior.transfer(scan, certificates=True)
        for mode in ('auto', 'forward', 'reverse'):
            result = corridor_transfer(scan, mode=mode, direction_policy='ports',
                                       scalar_engine='components')
            for key in ('mid', 'deg', 'q', 'out'):
                self.assertEqual(result[key], expected[key])
            self.assertEqual(len(self.prior.check_certificate(
                scan, dict(expected, out=result['out']))), 8)
        for options in ({'direction_policy': 'guessed'}, {'scalar_engine': 'guessed'}):
            with self.assertRaises(ValueError):
                CorridorScan(**options)

    def test_cli_window_incompatibility_is_cleanly_rejected(self):
        from fastunknot.__main__ import main
        for reduction in ('corridor', 'corridor-adaptive'):
            errors = io.StringIO()
            with contextlib.redirect_stderr(errors):
                code = main(['recognize', str(ROOT / 'examples' / 'trefoil.json'),
                             '--reduction', reduction, '--window-radius', '1'])
            self.assertEqual(code, 2)
            self.assertIn('cannot be combined', errors.getvalue())


if __name__ == '__main__':
    unittest.main()
