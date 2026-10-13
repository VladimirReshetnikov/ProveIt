"""Certified projection class, independent knot arithmetic, and safe fallback."""
import copy
import itertools
import json
from pathlib import Path
import random
import subprocess
import sys
import unittest
from unittest.mock import patch

from fastunknot import Diagram, DiagramError, recognize
from fastunknot.alexander import alexander_polynomial, evaluate
from fastunknot.scan import ScanLimit
from fastunknot.treewidth_two import (_eliminate, exact_determinant, projection_order,
    treewidth_two_certificate, verify_treewidth_two_certificate)
from separator_research.graphs import tree_medial
from test_fastunknot import reference_reduced_rank
from test_interlace import trefoil_sum

ROOT = Path(__file__).resolve().parents[1]


def load(name):
    return Diagram.from_json(json.loads((ROOT/'examples'/(name+'.json')).read_text()))


def has_k4_minor(n, edges):
    """Independent exhaustive connected branch-set definition; tiny graphs only."""
    for assignment in itertools.product(range(5), repeat=n):
        groups = [{v for v, label in enumerate(assignment) if label == i} for i in range(4)]
        if any(not group for group in groups):
            continue
        connected = True
        for group in groups:
            reached = {min(group)}
            while True:
                more = {v for u, v in edges | {(b, a) for a, b in edges}
                        if u in reached and v in group} - reached
                if not more:
                    break
                reached |= more
            if reached != group:
                connected = False
                break
        if connected and all(any((min(u, v), max(u, v)) in edges
                                 for u in groups[a] for v in groups[b])
                             for a, b in itertools.combinations(range(4), 2)):
            return True
    return False


class TreewidthTwoTests(unittest.TestCase):
    def test_graph_gate_against_branch_set_definition(self):
        # Every graph on four vertices, plus graph families on five and six.
        cases = []
        pairs = list(itertools.combinations(range(4), 2))
        cases.extend((4, {e for i, e in enumerate(pairs) if (mask >> i) & 1})
                     for mask in range(1 << len(pairs)))
        rng = random.Random(2640)
        for n in (5, 6):
            cases.extend((n, {e for e in itertools.combinations(range(n), 2)
                              if rng.randrange(2)}) for _ in range(12))
        # K4 with one subdivided edge: degree-two deletion without fill
        # would incorrectly accept it.
        cases.append((5, {(0, 4), (1, 4), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)}))
        for n, edges in cases:
            adjacency = [set() for _ in range(n)]
            for u, v in edges:
                adjacency[u].add(v)
                adjacency[v].add(u)
            self.assertEqual(_eliminate(adjacency, lambda: None) is None,
                             has_k4_minor(n, edges), (n, edges))

    def test_small_knots_against_full_cube_and_independent_verifier(self):
        # All 2-strand crossing assignments up to seven crossings, without
        # source provenance. Their det is abs(exponent sum), not crossing count.
        for n in (1, 3, 5, 7):
            for word in itertools.product((-1, 1), repeat=n):
                diagram = Diagram.from_pd(Diagram.from_braid(2, word).pd)
                c = treewidth_two_certificate(diagram)
                self.assertEqual(int(c['determinant_hex'], 16), abs(sum(word)))
                self.assertEqual(c['status'] == 'UNKNOT', reference_reduced_rank(diagram) == 1)
                self.assertTrue(verify_treewidth_two_certificate(diagram, c))

    def test_general_signed_tait_determinants_and_scope(self):
        diagrams = [load(name) for name in ('trefoil', 'figure_eight', 'conway',
                    'kinoshita_terasaka', 'hard_unknot_8', 'grid_determinant_one_knot')]
        rng = random.Random(2641)
        for _ in range(90):
            strands = rng.randrange(2, 6)
            word = [rng.choice((-1, 1))*rng.randrange(1, strands) for _ in range(rng.randrange(1, 10))]
            try:
                diagrams.append(Diagram.from_braid(strands, word))
            except DiagramError:
                pass
        accepted = 0
        for original in diagrams:
            for d in (original, original.mirror()):
                expected = abs(evaluate(alexander_polynomial(d), -1))
                self.assertEqual(exact_determinant(d), expected)
                c = treewidth_two_certificate(d)
                if c is not None:
                    accepted += 1
                    self.assertTrue(verify_treewidth_two_certificate(d, c))
        self.assertGreater(accepted, 10)
        for name in ('conway', 'kinoshita_terasaka', 'grid_determinant_one_knot'):
            d = load(name)
            self.assertEqual(exact_determinant(d), 1)
            self.assertIsNone(treewidth_two_certificate(d))
            result = recognize(d, use_treewidth_two=True)
            self.assertEqual(result.status, 'KNOTTED')
            self.assertEqual(result.evidence['treewidth_two']['status'], 'outside-class')

    def test_large_graphs_composites_and_relabelings(self):
        for d, expected in ((tree_medial(10), 1), (trefoil_sum(9), 3**9)):
            c = treewidth_two_certificate(d)
            self.assertEqual(int(c['determinant_hex'], 16), expected)
            self.assertEqual(len(c['order']), d.crossings)
        rng = random.Random(2642)
        d = trefoil_sum(5)
        for _ in range(10):
            rows = list(d.pd)
            rng.shuffle(rows)
            rows = [row[2:]+row[:2] if rng.randrange(2) else row for row in rows]
            labels = list(range(2*d.crossings))
            rng.shuffle(labels)
            changed = Diagram.from_pd([[1000-7*labels[e] for e in row] for row in rows])
            c = treewidth_two_certificate(changed)
            self.assertEqual(c['status'], 'KNOTTED')
            self.assertEqual(int(c['determinant_hex'], 16), 3**5)
            self.assertTrue(verify_treewidth_two_certificate(changed, c))

    def test_large_determinant_is_json_safe(self):
        c = treewidth_two_certificate(trefoil_sum(10000))
        self.assertEqual(int(c['determinant_hex'], 16), 3**10000)
        self.assertEqual(json.loads(json.dumps(c)), c)

    def test_verifier_rejects_forged_or_incomplete_evidence(self):
        d = load('trefoil')
        original = treewidth_two_certificate(d)
        for key, value in (('version', True), ('crossings', True), ('status', 'UNKNOT'),
                           ('determinant_hex', '0x1'), ('method', 'determinant'),
                           ('order', [0, 1]), ('order', [0, 0, 2]), ('order', [False, 1, 2])):
            changed = copy.deepcopy(original)
            changed[key] = value
            self.assertFalse(verify_treewidth_two_certificate(d, changed), (key, value))
        forged = dict(original, order=list(range(11)), crossings=11, determinant_hex='0x1', status='UNKNOT')
        self.assertFalse(verify_treewidth_two_certificate(load('conway'), forged))
        with (patch('fastunknot.treewidth_two.projection_order', side_effect=AssertionError('producer gate')),
              patch('fastunknot.treewidth_two.exact_determinant', side_effect=AssertionError('producer arithmetic'))):
            self.assertTrue(verify_treewidth_two_certificate(d, original))

    def test_cancellation_and_adaptive_fallback(self):
        d = Diagram.from_pd(Diagram.from_braid(2, [1, -1, 1]).pd)
        def stop():
            raise ScanLimit('injected cancellation')
        for call in (lambda: treewidth_two_certificate(d, check=stop),
                     lambda: exact_determinant(d, check=stop),
                     lambda: verify_treewidth_two_certificate(d, {}, check=stop)):
            with self.assertRaises(ScanLimit):
                call()
        r = recognize(d, use_treewidth_two=True, treewidth_two_seconds=0)
        self.assertEqual(r.status, 'UNKNOT')
        self.assertEqual(r.evidence['treewidth_two']['status'], 'skipped')
        self.assertNotEqual(r.method, 'treewidth-two-determinant')
        r = recognize(d, use_treewidth_two=True, seconds=0)
        self.assertEqual(r.status, 'UNKNOWN')
        with patch('fastunknot.treewidth_two.exact_determinant', side_effect=ScanLimit('mid determinant')):
            r = recognize(d, use_treewidth_two=True)
        self.assertEqual(r.status, 'UNKNOT')
        self.assertEqual(r.evidence['treewidth_two']['status'], 'skipped')
        finished = []
        def compute(*args, **kwargs):
            value = exact_determinant(*args, **kwargs)
            finished.append(value)
            return value
        def late_stop():
            if finished:
                raise ScanLimit('cancel after determinant, before publishing')
        with patch('fastunknot.treewidth_two.exact_determinant', side_effect=compute):
            with self.assertRaises(ScanLimit):
                treewidth_two_certificate(d, check=late_stop)
        self.assertEqual(finished, [1])
        for options in ({'use_treewidth_two': 1}, {'treewidth_two_seconds': -1},
                        {'treewidth_two_seconds': True}, {'treewidth_two_seconds': float('nan')},
                        {'treewidth_two_seconds': float('inf')}):
            with self.assertRaises(ValueError):
                recognize(d, **options)
        r = recognize(d, use_treewidth_two=True, treewidth_two_seconds=None)
        self.assertEqual(r.method, 'treewidth-two-determinant')
        self.assertTrue(verify_treewidth_two_certificate(d, r.evidence['treewidth_two']))

    def test_cli_and_crossing_free_input(self):
        c = treewidth_two_certificate(Diagram.from_pd([]))
        self.assertTrue(verify_treewidth_two_certificate(Diagram.from_pd([]), c))
        run = subprocess.run([sys.executable, '-B', '-m', 'fastunknot', 'recognize',
            str(ROOT/'examples/trefoil.json'), '--treewidth-two', '--no-braid'],
            capture_output=True, text=True, check=True)
        result = json.loads(run.stdout)
        self.assertEqual(result['method'], 'treewidth-two-determinant')
        self.assertEqual(result['status'], 'KNOTTED')
        self.assertFalse(result['quasipolynomial_guarantee'])


if __name__ == '__main__':
    unittest.main()
