"""Cyclic overlap search and presentation-preserving replay audits."""
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
from fastunknot.group_certificate import (_Budget, _reduce, GroupLimit,
    group_certificate, verify_group_certificate, group_decide)
from fastunknot.relator_overlap import overlap_move, apply_overlap
from fastunknot.scan import ScanLimit
from fastunknot.simplify import simplify
from hard_unknots import SURVIVORS
from test_fastunknot import one_component, reference_reduced_rank

ROOT = Path(__file__).resolve().parents[1]


def budget():
    return _Budget(lambda: None, 200000, 10000000)


def brute_gain(words):
    best = 0
    for i, left in enumerate(words):
        for j, right in enumerate(words):
            if i == j:
                continue
            for source in (right, [-x for x in reversed(right)]):
                for a in range(len(left)):
                    for b in range(len(source)):
                        overlap = 0
                        while (overlap < min(len(left), len(source)) and
                               left[(a+overlap) % len(left)] == source[(b+overlap) % len(source)]):
                            overlap += 1
                        best = max(best, 2*overlap-len(source))
    return best


def mirror(index):
    _, strands, word = SURVIVORS[index]
    d, _ = simplify(Diagram.from_braid(strands, word), r3=True)
    return d.mirror()


class RelatorOverlapTests(unittest.TestCase):
    def test_exhaustive_short_words_against_all_rotations(self):
        words = [list(w) for size in (1, 2, 3) for w in itertools.product((-2, -1, 1, 2), repeat=size)
                 if all(w[i] != -w[(i+1) % size] for i in range(size))]
        cases = [[a, b] for a in words for b in words]
        rng = random.Random(2671)
        cases.extend([[rng.choices((-3, -2, -1, 1, 2, 3), k=rng.randrange(0, 12))
                       for _ in range(rng.randrange(1, 5))] for _ in range(200)])
        cases.extend([[[1]*30, [1]*7], [[1, 2]*20, [2, 1]*5],
                      [[1, 2, 3], [-3, -2, -1]], [[1, 2, 3]], [[], []]])
        for relators in cases:
            move = overlap_move(relators, budget())
            gain = 0 if move is None else 2*move['overlap']-len(relators[move['donor']])
            self.assertEqual(gain, brute_gain(relators), relators)
            if move is not None:
                changed = copy.deepcopy(relators)
                apply_overlap(changed, move, budget(), _reduce)
                self.assertLessEqual(sum(map(len, changed)), sum(map(len, relators))-gain)
                self.assertEqual(changed[move['donor']], relators[move['donor']])
        self.assertEqual(len(cases), 2141)

    def test_native_gordian_certificate(self):
        d = Diagram.from_json(json.loads((ROOT/'normal_research/gordian.json').read_text()))
        c = group_certificate(d, relator_moves=True, max_work=10000000)
        self.assertIsNotNone(c)
        self.assertEqual(c['version'], 2)
        self.assertEqual(sum(m['kind'] == 'eliminate' for m in c['moves']), 140)
        self.assertEqual(sum(m['kind'] == 'relator' for m in c['moves']), 1)
        self.assertTrue(verify_group_certificate(d, json.loads(json.dumps(c)), max_work=10000000))
        with patch('fastunknot.relator_overlap.overlap_move', side_effect=AssertionError), \
             patch('fastunknot.relator_overlap.apply_overlap', side_effect=AssertionError):
            self.assertTrue(verify_group_certificate(d, c, max_work=10000000))

    def test_stalled_mirrors_and_small_knots(self):
        # Existing successful small-rank paths keep their exact old traces;
        # overlap matching is deferred until Whitehead search actually stalls.
        for _, strands, word in SURVIVORS:
            d, _ = simplify(Diagram.from_braid(strands, word), r3=True)
            with patch('fastunknot.relator_overlap.overlap_move', side_effect=AssertionError):
                c = group_certificate(d, relator_moves=True)
            self.assertEqual(c, group_certificate(d))
        for i in (3, 8):
            d = mirror(i)
            self.assertIsNone(group_certificate(d))
            c = group_certificate(d, relator_moves=True)
            self.assertIsNotNone(c)
            self.assertTrue(verify_group_certificate(d, c))
        rng, checked, certified = random.Random(2672), 0, 0
        while checked < 80:
            strands, length = rng.choice((2, 3, 4)), rng.randrange(1, 8)
            word = [rng.choice((-1, 1))*rng.randrange(1, strands) for _ in range(length)]
            if not one_component(strands, word):
                continue
            d = Diagram.from_pd(Diagram.from_braid(strands, word).pd)
            c = group_certificate(d, relator_moves=True)
            if c is not None:
                self.assertEqual(reference_reduced_rank(d), 1, word)
                self.assertTrue(verify_group_certificate(d, c))
                certified += 1
            checked += 1
        self.assertGreater(certified, 20)
        for name in ('trefoil', 'conway', 'kinoshita_terasaka', 'grid_determinant_one_knot'):
            d = Diagram.from_json(json.loads((ROOT/'examples'/(name+'.json')).read_text()))
            self.assertEqual(group_decide(d, seconds=None, relator_moves=True)['status'], 'INCONCLUSIVE')

    def test_forged_overlap_steps_and_version_boundaries(self):
        d = mirror(3)
        c = group_certificate(d, relator_moves=True)
        index = next(i for i, m in enumerate(c['moves']) if m['kind'] == 'relator')
        original = c['moves'][index]
        for key, value in [('donor', original['target']), ('donor', -1), ('target', True),
                           ('target_rotation', -1), ('donor_rotation', 1000000),
                           ('inverse', 1), ('overlap', 0), ('overlap', 1000000)]:
            bad = copy.deepcopy(c)
            bad['moves'][index][key] = value
            self.assertFalse(verify_group_certificate(d, bad), (key, value))
        bad = copy.deepcopy(c)
        bad['version'] = 1
        self.assertFalse(verify_group_certificate(d, bad))
        bad = copy.deepcopy(c)
        bad['moves'][index]['inverse'] = not original['inverse']
        self.assertFalse(verify_group_certificate(d, bad))
        bad = copy.deepcopy(c)
        bad['moves'][index]['donor_rotation'] += 1
        self.assertFalse(verify_group_certificate(d, bad))

    def test_budget_cancellation_and_cli(self):
        def cancel():
            raise ScanLimit('global cancellation')
        with self.assertRaises(ScanLimit):
            overlap_move([[1, 2, 3], [2, 3]], _Budget(cancel, 100, 100))
        with self.assertRaises(GroupLimit):
            overlap_move([[1, 2, 3], [2, 3]], _Budget(lambda: None, 100, 0))
        d = mirror(8)
        self.assertEqual(group_decide(d, relator_moves=True, max_work=0)['status'], 'INCONCLUSIVE')
        result = recognize(Diagram.from_pd(d.pd), use_group=True, group_relators=True, group_seconds=None)
        self.assertEqual((result.status, result.method), ('UNKNOT', 'wirtinger-cyclic-group'))
        run = subprocess.run([sys.executable, '-B', '-m', 'fastunknot', 'recognize', '-',
                              '--group-relators', '--group-seconds', '2', '--group-max-work', '10000000'],
                             input=json.dumps({'pd': d.pd}), text=True, capture_output=True, cwd=ROOT)
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(json.loads(run.stdout)['method'], 'wirtinger-cyclic-group')
        for options in ({'group_relators': 1}, {'group_max_work': True}, {'group_max_work': -1}):
            with self.assertRaises(ValueError):
                recognize(d, **options)
        with patch('fastunknot.group_certificate.verify_group_certificate', side_effect=GroupLimit('replay cap')):
            self.assertEqual(group_decide(d, seconds=None, relator_moves=True)['status'], 'INCONCLUSIVE')


if __name__ == '__main__':
    unittest.main()
