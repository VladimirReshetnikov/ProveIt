"""Group soundness, independent replay, Whitehead conventions and budgets."""
import copy
import itertools
import json
from pathlib import Path
import random
import subprocess
import sys
import unittest
from unittest.mock import patch

from fastunknot import Diagram, recognize
from fastunknot.group_certificate import (_Budget, _presentation, _whitehead_graph,
    _whitehead_move, group_certificate, verify_group_certificate, group_decide, GroupLimit)
from fastunknot.scan import ScanLimit
from fastunknot.simplify import simplify
from hard_unknots import SURVIVORS
from test_fastunknot import one_component, reference_reduced_rank

ROOT = Path(__file__).resolve().parents[1]


def load(name):
    return Diagram.from_json(json.loads((ROOT/'examples'/(name+'.json')).read_text()))


def budget():
    return _Budget(lambda: None, 200000, 20000000)


def literal(word, a, subset):
    """Direct four-case definition, with slow cancellation for tiny tests."""
    out = []
    for x in word:
        if x in (a, -a) or (x not in subset and -x not in subset):
            out.append(x)
        elif x in subset and -x not in subset:
            out.extend([x, a])
        elif x not in subset and -x in subset:
            out.extend([-a, x])
        else:
            out.extend([-a, x, a])
    changed = True
    while changed:
        changed = False
        for i in range(len(out)-1):
            if out[i]+out[i+1] == 0:
                del out[i:i+2]
                changed = True
                break
    while len(out) > 1 and out[0]+out[-1] == 0:
        out = out[1:-1]
    return out


class GroupCertificateTests(unittest.TestCase):
    def test_whitehead_formula_all_short_cyclic_words_and_cuts(self):
        # Includes every characteristic pair in rank three, signed multipliers,
        # repeated letters, one-letter relators, inverse words and wraparound.
        alphabet = (-3, -2, -1, 1, 2, 3)
        cases = 0
        for length in (1, 2, 3):
            for word in itertools.product(alphabet, repeat=length):
                if any(word[i] == -word[(i+1) % length] for i in range(length)):
                    continue
                graph = _whitehead_graph([word], budget())
                best = 0
                for a in alphabet:
                    others = [x for x in alphabet if abs(x) != abs(a)]
                    for bits in itertools.product((0, 1), repeat=4):
                        subset = {a} | {x for x, bit in zip(others, bits) if bit}
                        predicted = sum(w for u in subset for v, w in graph.get(u, {}).items()
                                        if v not in subset)-sum(graph.get(a, {}).values())
                        actual = len(literal(word, a, subset))-len(word)
                        self.assertEqual(predicted, actual, (word, a, subset))
                        best = min(best, actual)
                        cases += 1
                self.assertEqual(_whitehead_move([word], budget())[0], best)
        self.assertEqual(cases, 15552)
        # The min-cut graph for a list is the sum of the cyclic-word graphs.
        words = [[1, 2, 3], [1, -2, 3, 3], [-1, -3]]
        graph = _whitehead_graph(words, budget())
        change, a, subset = _whitehead_move(words, budget())
        if a is not None:
            self.assertEqual(sum(len(literal(w, a, subset))-len(w) for w in words), change)

    def test_preprint_convention_counterexample(self):
        # arXiv:2607.21499v1 equations (10)--(12), read literally together.
        word, a, subset = [1, 2, 3], 1, {1, -2}
        self.assertEqual(literal(word, a, subset), [2, 3])
        printed_edges = [(-word[i], word[(i+1) % 3]) for i in range(3)]
        printed_change = sum((x in subset) != (y in subset) for x, y in printed_edges)
        printed_change -= sum(a in edge for edge in printed_edges)
        self.assertEqual(printed_change, 1)  # actual change is -1
        correct_edges = [(word[i], -word[(i+1) % 3]) for i in range(3)]
        self.assertEqual(sum((x in subset) != (y in subset) for x, y in correct_edges)-1, -1)

    def test_survivors_mirrors_and_independent_replay(self):
        whitehead = 0
        for _, strands, word in SURVIVORS:
            d, _ = simplify(Diagram.from_braid(strands, word), r3=True)
            for mirrored, diagram in enumerate((Diagram.from_pd(d.pd), d.mirror())):
                c = group_certificate(diagram)
                if not mirrored:
                    self.assertIsNotNone(c)
                if c is None:
                    continue  # Greedy elimination need not succeed on a mirror.
                self.assertTrue(verify_group_certificate(diagram, json.loads(json.dumps(c))))
                whitehead += sum(m['kind'] == 'whitehead' for m in c['moves'])
                # Make sure verifier uses neither producer reconstruction nor
                # its reduction, substitution, graph or flow implementation.
                with patch('fastunknot.group_certificate._presentation', side_effect=AssertionError), \
                     patch('fastunknot.group_certificate._reduce', side_effect=AssertionError), \
                     patch('fastunknot.group_certificate._image', side_effect=AssertionError), \
                     patch('fastunknot.group_certificate._whitehead_move', side_effect=AssertionError):
                    self.assertTrue(verify_group_certificate(diagram, c))
        self.assertGreater(whitehead, 0)
        for name in ('unknot', 'hard_unknot_8', 'grid_scrambled_unknot'):
            d = load(name)
            c = group_certificate(d)
            if c is not None:
                self.assertTrue(verify_group_certificate(d, c))

    def test_small_random_knots_against_full_cube(self):
        rng = random.Random(2661)
        checked = positive = negative = 0
        while checked < 70:
            strands, length = rng.choice((2, 3, 4)), rng.randrange(1, 8)
            word = [rng.choice((-1, 1))*rng.randrange(1, strands) for _ in range(length)]
            if not one_component(strands, word):
                continue
            d = Diagram.from_pd(Diagram.from_braid(strands, word).pd)
            c = group_certificate(d)
            unknot = reference_reduced_rank(d) == 1
            if c is not None:
                self.assertTrue(unknot, word)
                self.assertTrue(verify_group_certificate(d, c))
                positive += 1
            elif not unknot:
                negative += 1
            checked += 1
        self.assertGreater(positive, 10)
        self.assertGreater(negative, 3)
        for name in ('trefoil', 'figure_eight', 'conway', 'kinoshita_terasaka',
                     'grid_determinant_one_knot'):
            self.assertEqual(group_decide(load(name), seconds=None)['status'], 'INCONCLUSIVE')

    def test_forged_traces_rejected(self):
        _, strands, word = SURVIVORS[0]
        d, _ = simplify(Diagram.from_braid(strands, word), r3=True)
        c = group_certificate(d)
        corruptions = []
        for key, value in [('version', True), ('method', 'abelianization'), ('status', 'KNOTTED'),
                           ('moves', []), ('remaining_generator', 0), ('input_pd', [])]:
            bad = copy.deepcopy(c)
            bad[key] = value
            corruptions.append(bad)
        pivot = next(i for i, m in enumerate(c['moves']) if m['kind'] == 'eliminate')
        whitehead = next(i for i, m in enumerate(c['moves']) if m['kind'] == 'whitehead')
        for index, field, value in [(pivot, 'generator', True), (pivot, 'relation', -1),
                                   (pivot, 'generator', 9999), (whitehead, 'multiplier', 0),
                                   (whitehead, 'subset', []), (whitehead, 'subset', [9999])]:
            bad = copy.deepcopy(c)
            bad['moves'][index][field] = value
            corruptions.append(bad)
        bad = copy.deepcopy(c)
        bad['moves'].append(copy.deepcopy(c['moves'][pivot]))
        corruptions.append(bad)
        for bad in corruptions:
            self.assertFalse(verify_group_certificate(d, bad), bad)
        self.assertFalse(verify_group_certificate(load('trefoil'), c))
        # Binding alone is not the proof: replacing the input with a knot still
        # fails replay rather than accepting the final UNKNOT status blindly.
        knot = load('trefoil')
        bad = copy.deepcopy(c)
        bad['input_pd'] = [list(row) for row in knot.pd]
        self.assertFalse(verify_group_certificate(knot, bad))

    def test_local_budgets_and_global_cancellation(self):
        d = load('hard_unknot_8')
        for options in ({'seconds': 0}, {'max_letters': 0}, {'max_work': 0}):
            self.assertEqual(group_decide(d, **options)['status'], 'INCONCLUSIVE')
        def cancel(*args, **kwargs):
            raise ScanLimit('global cancellation')
        for operation in (lambda: group_decide(d, check=cancel),
                          lambda: group_certificate(d, check=cancel),
                          lambda: verify_group_certificate(d, {}, check=cancel)):
            with self.assertRaisesRegex(ScanLimit, 'global cancellation'):
                operation()
        c = group_certificate(d)
        with self.assertRaises(GroupLimit):
            verify_group_certificate(d, c, max_work=0)
        # Cancellation after search, during replay, cannot become a verdict.
        with patch('fastunknot.group_certificate.verify_group_certificate', side_effect=cancel):
            with self.assertRaises(ScanLimit):
                group_decide(d, seconds=None)
        with patch('fastunknot.group_certificate.verify_group_certificate', return_value=False):
            with self.assertRaises(ArithmeticError):
                group_decide(d, seconds=None)

    def test_pipeline_success_fallback_and_cli(self):
        _, strands, word = SURVIVORS[0]
        d, _ = simplify(Diagram.from_braid(strands, word), r3=True)
        result = recognize(Diagram.from_pd(d.pd), use_group=True, group_seconds=None)
        self.assertEqual((result.status, result.method), ('UNKNOT', 'wirtinger-cyclic-group'))
        c = result.evidence['group']['certificate']
        self.assertTrue(verify_group_certificate(Diagram.from_pd(c['input_pd']), c))
        self.assertFalse(result.to_json()['quasipolynomial_guarantee'])
        fallback = recognize(Diagram.from_pd(d.pd), use_group=True, group_seconds=0)
        self.assertEqual(fallback.status, 'UNKNOT')
        self.assertEqual(fallback.evidence['group']['status'], 'INCONCLUSIVE')
        self.assertNotEqual(fallback.method, 'wirtinger-cyclic-group')
        with patch('fastunknot.group_certificate.group_decide', side_effect=ScanLimit('global')):
            self.assertEqual(recognize(Diagram.from_pd(d.pd), use_group=True).status, 'UNKNOWN')
        output = subprocess.run([sys.executable, '-B', '-m', 'fastunknot', 'recognize', '-', '--group'],
            input=json.dumps({'pd': d.pd}), capture_output=True, text=True, cwd=ROOT)
        self.assertEqual(output.returncode, 0, output.stderr)
        self.assertEqual(json.loads(output.stdout)['method'], 'wirtinger-cyclic-group')
        for options in ({'use_group': 1}, {'group_seconds': True}, {'group_seconds': -1},
                        {'group_seconds': float('inf')}, {'group_seconds': float('nan')}):
            with self.assertRaises(ValueError):
                recognize(d, **options)


if __name__ == '__main__':
    unittest.main()
