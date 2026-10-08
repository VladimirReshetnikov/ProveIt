"""Report-46 all-rotation audits plus maintained-prelude and resource regressions."""
import copy
import itertools
import json
from pathlib import Path
import random
import unittest
from unittest.mock import patch

from fastunknot import Diagram
from fastunknot.cyclic_overlap_index import bounded_overlap_move, joint_overlap_move
from fastunknot.group_certificate import (
    _Budget, _reduce, GroupLimit, group_certificate, verify_group_certificate)
from fastunknot.relator_overlap import overlap_move, pairwise_overlap_move, apply_overlap
from fastunknot.scan import ScanLimit
from test_relator_overlap import brute_gain

ROOT = Path(__file__).resolve().parents[1]


def budget(work=20_000_000):
    return _Budget(lambda: None, 200_000, work)


def gain(words, move):
    return 0 if move is None else 2*move['overlap']-len(words[move['donor']])


class CyclicOverlapIndexTests(unittest.TestCase):
    def check_words(self, words, expected=None):
        expected = brute_gain(words) if expected is None else expected
        for backend in ('adaptive', 'joint', 'pairwise'):
            move = overlap_move(words, budget(), backend=backend)
            self.assertEqual(gain(words, move), expected, (words, backend, move))
            if move is not None:
                self.assertNotEqual(move['target'], move['donor'])
                changed = copy.deepcopy(words)
                apply_overlap(changed, move, budget(), _reduce)
                self.assertEqual(changed[move['donor']], words[move['donor']])
                self.assertLessEqual(sum(map(len, changed)), sum(map(len, words))-expected)

    def test_exhaustive_unreduced_rank_two_pairs(self):
        # Include cancellations: the substring primitive does not assume them
        # away, even though its production caller supplies reduced relators.
        words = [list(w) for size in (1, 2, 3)
                 for w in itertools.product((-2, -1, 1, 2), repeat=size)]
        for left in words:
            for right in words:
                self.check_words([left, right])
        self.assertEqual(len(words)**2, 7056)

    def test_independent_brute_force_random_multi_slot(self):
        rng = random.Random(261008901)
        for _ in range(350):
            words = [rng.choices((-3, -2, -1, 1, 2, 3), k=rng.randrange(0, 9))
                     for _ in range(rng.randrange(0, 7))]
            self.check_words(words)

    def test_periodic_clipped_windows_inverse_and_distinct_slots(self):
        cases = [[], [[]], [[], []], [[1]], [[1, 2, -1, -2]],
                 [[1, 2, 3], [1, 2, 3]], [[1, 2, 3], [-3, -2, -1]],
                 [[1]*60, [1]*7], [[1, 2]*20, [2, 1]*5],
                 [[1, 2, 3, 4]*6, [4, 1, 2, 3]*3],
                 [[1, 1, 2, 3, 1], [-1, -3, -2, -1]],
                 [[1, 2, 3], [4, 5, 6]],
                 [[], [1, 2]*5, [], [2, 1]*5, []],
                 [[1], [2, 1, 3], [1, 2, 3, 1, 2, 3]],
                 [[1, 2, 3, 4, 5], [3, 4, 5, 1], [-4, -3, -2, -1]]]
        for words in cases:
            self.check_words(words)

    def test_joint_against_incumbent_many_slots_and_large_alphabet(self):
        rng = random.Random(261008902)
        for _ in range(600):
            alphabet = rng.choice(([-4, -3, -2, -1, 1, 2, 3, 4],
                [1, 2**70+3, -(2**80+7), -1]))
            words = [rng.choices(alphabet, k=rng.randrange(0, 35))
                     for _ in range(rng.randrange(0, 12))]
            old = pairwise_overlap_move(words, budget())
            expected = gain(words, old)
            for query in (joint_overlap_move, bounded_overlap_move):
                move = query(words, budget())
                self.assertEqual(gain(words, move), expected, (words, query.__name__))
                if move is not None:
                    apply_overlap(copy.deepcopy(words), move, budget(), _reduce)

    def test_bounded_handoff_and_shared_limits(self):
        words = [[1, 2, 3, 4], [-4, -3, -2, -1], [8, 9, 10]]
        for coefficient in (0, 1, 2):
            stats, shared = {}, budget()
            move = bounded_overlap_move(words, shared, coefficient=coefficient, small_slots=0, stats=stats)
            self.assertEqual(gain(words, move), brute_gain(words))
            self.assertGreater(stats['prelude_work'], 0)
            if coefficient == 0:
                self.assertEqual(stats['backend'], 'joint-index')
                self.assertGreater(20_000_000-shared.left, stats['prelude_work'])
        with self.assertRaises(GroupLimit):
            bounded_overlap_move(words, budget(0), coefficient=0, small_slots=0)
        with self.assertRaises(GroupLimit):
            bounded_overlap_move(words, budget(20), coefficient=0, small_slots=0)
        def cancel():
            raise ScanLimit('global cancellation')
        with self.assertRaises(ScanLimit):
            bounded_overlap_move(words, _Budget(cancel, 100, 100), coefficient=0, small_slots=0)
        for coefficient in (-1, True, 1.5):
            with self.assertRaises(ValueError):
                bounded_overlap_move(words, budget(), coefficient=coefficient)
        for options in ({'backend':'bad'}, {'stats':1}):
            with self.assertRaises(ValueError):
                overlap_move(words, budget(), **options)

    def test_fixed_slot_base_case_preserves_incumbent(self):
        words = [[1,2,3,4]*8, [3,4,1,2]*4, [-4,-3,-2,-1]*5]
        stats = {}
        with patch('fastunknot.cyclic_overlap_index.joint_overlap_move',
                   side_effect=AssertionError('fixed-slot query must not build joint index')):
            move = bounded_overlap_move(words, budget(), stats=stats)
        self.assertEqual(move, pairwise_overlap_move(words, budget()))
        self.assertEqual(stats['backend'], 'fixed-slot-pairwise')
        for value in (-1, True, 1.5):
            with self.assertRaises(ValueError):
                bounded_overlap_move(words, budget(), small_slots=value)

    def test_completed_prelude_preserves_every_incumbent_witness(self):
        rng = random.Random(261008612)
        for _ in range(2000):
            words = [rng.choices((-3,-2,-1,1,2,3),k=rng.randrange(18))
                     for _ in range(rng.randrange(11))]
            stats = {}
            move = bounded_overlap_move(words,budget(),coefficient=100000,
                                        small_slots=0,stats=stats)
            self.assertEqual(move,pairwise_overlap_move(words,budget()))
            self.assertEqual(stats['backend'],'prelude')

    def test_full_donor_match_preserves_the_maintained_early_cutoffs(self):
        words = [list(range(1,129)) for _ in range(128)]
        stats = {}
        with patch('fastunknot.cyclic_overlap_index.joint_overlap_move',side_effect=AssertionError):
            move = bounded_overlap_move(words,budget(),stats=stats)
        self.assertEqual(move,pairwise_overlap_move(words,budget()))
        self.assertEqual(stats['backend'],'prelude')
        self.assertEqual(stats['donor_automata'],1)
        self.assertEqual(stats['pair_scans'],1)

    def test_global_exhaustion_and_external_errors_do_not_trigger_continuation(self):
        words = [list(range(1,20)) for _ in range(8)]
        with patch('fastunknot.cyclic_overlap_index.joint_overlap_move',side_effect=AssertionError):
            with self.assertRaises(GroupLimit):
                bounded_overlap_move(words,budget(len(words)+1),coefficient=0,small_slots=0)
            steps = 0
            def cancel():
                nonlocal steps
                steps += 1
                if steps == 20:
                    raise ValueError('external overlap cancellation')
            with self.assertRaisesRegex(ValueError,'external overlap cancellation'):
                bounded_overlap_move(words,_Budget(cancel,10000,100000))
        for query in (bounded_overlap_move,joint_overlap_move):
            with self.assertRaises(ValueError):query(words,budget(),stats=1)
        # Handoff may require more than the old allowance. It must not expose
        # a partial incumbent as a finished exact query or reset that allowance.
        shared=budget();stats={}
        result=bounded_overlap_move(words,shared,coefficient=0,small_slots=0,stats=stats)
        used=20_000_000-shared.left
        self.assertEqual(bounded_overlap_move(words,budget(used),coefficient=0,small_slots=0),result)
        with self.assertRaises(GroupLimit):
            bounded_overlap_move(words,budget(used-1),coefficient=0,small_slots=0)

    def test_full_gordian_trace_and_independent_replay(self):
        diagram = Diagram.from_json(json.loads((ROOT/'normal_research/gordian.json').read_text()))
        with patch('fastunknot.relator_overlap.overlap_move', pairwise_overlap_move):
            old = group_certificate(diagram, relator_moves=True, max_work=20_000_000)
        new = group_certificate(diagram, relator_moves=True, max_work=20_000_000)
        self.assertEqual(new, old)
        with patch('fastunknot.cyclic_overlap_index.joint_overlap_move', side_effect=AssertionError), \
             patch('fastunknot.cyclic_overlap_index.bounded_overlap_move', side_effect=AssertionError), \
             patch('fastunknot.relator_overlap.overlap_move', side_effect=AssertionError), \
             patch('fastunknot.relator_overlap.apply_overlap', side_effect=AssertionError):
            self.assertTrue(verify_group_certificate(diagram, new, max_work=20_000_000))
            self.assertTrue(verify_group_certificate(diagram, new, compressed=True,
                                                     max_work=20_000_000))
        index = next(i for i, move in enumerate(new['moves']) if move['kind'] == 'relator')
        for key, value in (('overlap', new['moves'][index]['overlap']+1),
                           ('target_rotation', -1), ('donor', new['moves'][index]['target'])):
            bad = copy.deepcopy(new)
            bad['moves'][index][key] = value
            self.assertFalse(verify_group_certificate(diagram, bad, max_work=20_000_000))


if __name__ == '__main__':
    unittest.main()
