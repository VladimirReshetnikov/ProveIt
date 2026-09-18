from __future__ import annotations

from copy import deepcopy
from itertools import product
import json
from pathlib import Path
import random
import subprocess
import sys
import unittest

from unknot import Complex, Diagram, DiagramError, Limits, from_braid, recognize, verify_report
from unknot.khovanov import resolve
from unknot.linear import rank_f2
from tests.reference import dense_rank, differential, smoothing

ROOT = Path(__file__).resolve().parents[1]


def example(name):
    return Diagram.from_json(json.loads((ROOT / 'examples' / (name + '.json')).read_text()))


def dimension(diagram):
    report = recognize(diagram, check_d_squared=True)
    assert report['status'] != 'unknown'
    return report['reduced_homology_dimension']


class InputTests(unittest.TestCase):
    def test_empty_pd_means_one_circle(self):
        self.assertEqual(dimension(Diagram.from_pd([])), 1)

    def test_invalid_labels(self):
        for pd in ([[1, 2, 3, 4]], [[True, 1, 2, 2]], [[-1, -1, 0, 0]], [[1, 1, 1, 1]],
                   [[1, 1, 2]], [17], None):
            with self.subTest(pd=pd), self.assertRaises(DiagramError):
                Diagram.from_pd(pd)

    def test_invalid_braids(self):
        for strands, word in [(0, []), (True, []), (2, [0]), (2, [2]), (2, [True]),
                              (2, [1.0]), (3, []), (2, None), (2, [1, -1])]:
            with self.subTest(strands=strands, word=word), self.assertRaises(DiagramError):
                from_braid(strands, word)

    def test_multicomponent_pd_rejected(self):
        with self.assertRaisesRegex(DiagramError, 'component'):
            Diagram.from_pd([[0, 1, 0, 1]])

    def test_nonclassical_one_component_rejected(self):
        # Repeated edge incidence is legal, but this rotation system has genus 1.
        with self.assertRaisesRegex(DiagramError, 'spherical'):
            Diagram.from_pd([[0, 1, 2, 3], [0, 1, 3, 2]])

    def test_ambiguous_input_rejected(self):
        for obj in ({}, {'pd': [], 'braid': {}}, {'pd': [], 'components': 2},
                    {'pd': [], 'basepoint': 0}, {'pd': [], 'name': 3},
                    {'braid': {'strands': 1, 'word': []}, 'basepoint': 1}):
            with self.subTest(obj=obj), self.assertRaises(DiagramError):
                Diagram.from_json(obj)

    def test_direct_construction_cannot_bypass_validation(self):
        with self.assertRaises(DiagramError):
            recognize(Diagram(((0, 1, 0, 1),)))

    def test_basepoint_validation(self):
        with self.assertRaises(DiagramError):
            Diagram.from_pd(example('trefoil').pd, basepoint=999)


class HomologyTests(unittest.TestCase):
    def test_named_examples(self):
        # Rank 33 on the 11-crossing examples is a regression value from this
        # implementation. Knot Atlas independently identifies both as knots.
        for name, expected in [('unknot', 1), ('trefoil', 3), ('figure-eight', 5),
                               ('cinquefoil', 5), ('kt11n42', 33), ('conway11n34', 33),
                               ('unknot-braid12', 1)]:
            with self.subTest(name=name):
                self.assertEqual(dimension(example(name)), expected)

    def test_torus_family(self):
        for k in (1, 3, 5, 7, 9):
            for sign in (-1, 1):
                with self.subTest(k=k, sign=sign):
                    self.assertEqual(dimension(from_braid(2, [sign] * k)), k)

    def test_reidemeister_one(self):
        for pd in ([[0, 0, 1, 1]], [[0, 1, 1, 0]]):
            self.assertEqual(dimension(Diagram.from_pd(pd)), 1)

    def test_crossing_change_is_not_ignored(self):
        pd = [list(c) for c in example('trefoil').pd]
        pd[0] = pd[0][1:] + pd[0][:1]
        self.assertEqual(dimension(Diagram.from_pd(pd)), 1)

    def test_mirrors(self):
        for name in ('trefoil', 'figure-eight', 'kt11n42'):
            diagram = example(name)
            mirror = Diagram.from_pd([c[1:] + c[:1] for c in diagram.pd])
            self.assertEqual(dimension(diagram), dimension(mirror))

    def test_reidemeister_two_braid_cancellation(self):
        base = [1, -2, 1, -2]
        for position in range(len(base) + 1):
            for i in (1, -1, 2, -2):
                word = base[:position] + [i, -i] + base[position:]
                self.assertEqual(dimension(from_braid(3, word)), 5)

    def test_reidemeister_three_braid_relation(self):
        checked = 0
        for tail in ([1, 1, 2], [2, 2, 1], [-1, 1, -2]):
            for sign in (-1, 1):
                left = [sign, 2 * sign, sign] + list(tail)
                right = [2 * sign, sign, 2 * sign] + list(tail)
                # These closures are knots because the complete word's
                # permutation has a single cycle.
                try:
                    a, b = from_braid(3, left), from_braid(3, right)
                except DiagramError:
                    continue
                self.assertEqual(dimension(a), dimension(b))
                checked += 1
        self.assertEqual(checked, 6)

    def test_markov_stabilization(self):
        for strands, word in [(1, []), (2, [1, 1, 1]), (3, [1, -2, 1, -2])]:
            expected = dimension(from_braid(strands, word))
            for sign in (-1, 1):
                self.assertEqual(dimension(from_braid(strands + 1, word + [sign * strands])),
                                 expected)

    def test_braid_conjugation(self):
        for prefix in ([1], [-2], [1, -2]):
            inverse = [-i for i in reversed(prefix)]
            word = list(prefix) + [1, -2, 1, -2] + inverse
            self.assertEqual(dimension(from_braid(3, word)), 5)

    def test_relabel_crossing_order_and_basepoint(self):
        rng = random.Random(5301)
        diagram = example('figure-eight')
        for _ in range(20):
            labels = rng.sample(range(100, 500), 2 * diagram.crossings)
            pd = [[labels[x] for x in c] for c in diagram.pd]
            rng.shuffle(pd)
            self.assertEqual(dimension(Diagram.from_pd(pd, basepoint=rng.choice(labels))), 5)

    def test_every_trefoil_basepoint(self):
        for edge in range(6):
            self.assertEqual(dimension(Diagram.from_pd(example('trefoil').pd, basepoint=edge)), 3)

    def test_d_squared_short_three_braids(self):
        checked = 0
        for word in product((-2, -1, 1, 2), repeat=4):
            try:
                diagram = from_braid(3, word)
            except DiagramError:
                continue
            self.assertTrue(Complex(diagram).check_d_squared())
            self.assertGreaterEqual(dimension(diagram), 1)
            checked += 1
        self.assertEqual(checked, 160)

    def test_reference_complex_and_ranks(self):
        # Reference basis order differs (tuple lexicographic vs integer bitsets),
        # so compare ranks, smoothing partitions and total homology dimensions.
        samples = [from_braid(1, []), from_braid(2, [1]), from_braid(2, [-1]),
                   example('trefoil'), example('figure-eight'),
                   from_braid(3, [1, 2, 1, -1]), from_braid(2, [1] * 5)]
        for diagram in samples:
            c = Complex(diagram)
            for state in range(1 << diagram.crossings):
                actual = [frozenset(x) for x in resolve(diagram, state).circles]
                self.assertEqual(actual, smoothing(diagram.pd, state))
            for h in range(diagram.crossings + 1):
                self.assertEqual(rank_f2(c.columns(h)), dense_rank(differential(diagram.pd, h)))

    def test_chain_euler_characteristic_is_preserved(self):
        for name in ('unknot', 'trefoil', 'figure-eight', 'kt11n42'):
            result = recognize(example(name))
            alternating = lambda data: sum((-1)**i * v for i, v in enumerate(data))
            self.assertEqual(alternating(result['chain_dimensions']),
                             alternating(result['betti_by_height']))


class LinearTests(unittest.TestCase):
    def test_random_matrices_against_dense_reference(self):
        rng = random.Random(42)
        for rows in range(12):
            for columns in range(12):
                matrix = [[rng.randrange(2) for _ in range(rows)] for _ in range(columns)]
                bitsets = [sum(v << i for i, v in enumerate(c)) for c in matrix]
                self.assertEqual(rank_f2(bitsets), dense_rank(matrix))

    def test_large_bit_indices_not_truncated(self):
        self.assertEqual(rank_f2([1 << 10000, 1 << 25000, (1 << 10000) | (1 << 25000)]), 2)

    def test_invalid_columns(self):
        for value in (-1, 1.5, True):
            with self.assertRaises(ValueError):
                rank_f2([value])


class BudgetAndReportTests(unittest.TestCase):
    def test_state_limit_never_returns_knotted(self):
        result = recognize(example('trefoil'), limits=Limits(max_states=4))
        self.assertEqual(result['status'], 'unknown')
        self.assertNotIn('reduced_homology_dimension', result)

    def test_generator_limit_never_returns_knotted(self):
        self.assertEqual(recognize(example('figure-eight'), limits=Limits(max_generators=3))
                         ['status'], 'unknown')

    def test_time_limit_never_returns_knotted(self):
        self.assertEqual(recognize(example('kt11n42'), limits=Limits(seconds=1e-12))
                         ['status'], 'unknown')

    def test_invalid_limits(self):
        for kwargs in ({'max_states': 0}, {'max_generators': -1}, {'seconds': 0},
                       {'seconds': float('nan')}, {'seconds': True}, {'max_states': True}):
            with self.subTest(kwargs=kwargs), self.assertRaises(ValueError):
                Limits(**kwargs)

    def test_recompute_report(self):
        result = recognize(example('trefoil'))
        self.assertTrue(verify_report(result))
        for key, value in [('status', 'unknot'), ('reduced_homology_dimension', 1),
                           ('differential_ranks', [0, 0, 0, 0]), ('worst_case', 'polynomial')]:
            modified = deepcopy(result)
            modified[key] = value
            self.assertFalse(verify_report(modified))
        self.assertFalse(verify_report({'schema': 'unknot-result-v1', 'status': 'unknown'}))
        modified = recognize(example('unknot'))
        modified['reduced_homology_dimension'] = True
        self.assertFalse(verify_report(modified))

    def test_report_reverification_budget(self):
        self.assertFalse(verify_report(recognize(example('trefoil')), limits=Limits(max_states=2)))

    def test_cli_success_unknown_and_invalid(self):
        base = [sys.executable, '-m', 'unknot', 'recognize', str(ROOT/'examples/trefoil.json')]
        answer = subprocess.run(base, cwd=ROOT, text=True, capture_output=True)
        self.assertEqual(answer.returncode, 0, answer.stderr)
        self.assertEqual(json.loads(answer.stdout)['status'], 'knotted')
        answer = subprocess.run(base + ['--max-states', '2'], cwd=ROOT, text=True,
                                capture_output=True)
        self.assertEqual(answer.returncode, 3)
        self.assertEqual(json.loads(answer.stdout)['status'], 'unknown')
        answer = subprocess.run([sys.executable, '-m', 'unknot', 'recognize', '-'],
                                input='{"pd":[[0,1,0,1]]}', cwd=ROOT, text=True,
                                capture_output=True)
        self.assertEqual(answer.returncode, 2)
        self.assertEqual(json.loads(answer.stderr)['status'], 'error')


if __name__ == '__main__':
    unittest.main()
