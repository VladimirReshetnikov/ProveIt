"""Raw singleton DAGs: noncommutative images, source families and rejection."""
from collections import Counter
from copy import deepcopy
import random
import unittest
from unittest.mock import patch

from fastunknot import Diagram
from fastunknot.compressed_words import WordArena, CompressedLimit
from fastunknot.group_certificate import _Budget, _presentation, GroupLimit
from fastunknot.primitive_forest import plan_forest
from fastunknot.primitive_projection_verify import verify_compressed_rank_one
from fastunknot.singleton_dag import plan_singleton_dag, apply_singleton_dag
from fastunknot.singleton_dag_verify import (
    replay_compressed_singleton_dag, replay_literal_singleton_dag)


def inverse(word):
    return [-letter for letter in reversed(word)]


def substitute(word, images):
    result = []
    for letter in word:
        image = images.get(abs(letter), [abs(letter)])
        result.extend(image if letter > 0 else inverse(image))
    return result


def conjugation_chain(rank):
    """Abstract Z presentation whose unreduced image length grows as 2^rank."""
    words = [[1, -2]]
    words.extend([child, -(child - 1), -1, child - 1]
                 for child in range(3, rank + 1))
    words.append([rank, -1])
    return words


class SingletonDagTests(unittest.TestCase):
    def test_cached_maximum_count_selection_and_current_slots(self):
        rng = random.Random(261009101)
        for _ in range(80):
            labels = rng.sample(range(1, 100000), 7)
            words = [[rng.choice(labels) * rng.choice((-1, 1))
                      for _ in range(rng.randrange(20))] for _ in range(12)]
            words.extend([words[0], words[-1], [], [labels[0]], [labels[0], -labels[0]]])
            arena = WordArena()
            roots = [arena.from_word(word) for word in words]
            cache, expected, used = {}, [], set()
            for slot, word in enumerate(words):
                counts = Counter(map(abs, word))
                if counts:
                    child = max(counts)
                    if counts[child] == 1 and child not in used:
                        expected.append(dict(relation=slot, generator=child))
                        used.add(child)
            expected.sort(key=lambda pivot: pivot['generator'])
            self.assertEqual(plan_singleton_dag(arena, roots, set(labels), cache), expected)
            count = arena.stats['singleton_dag_metadata_nodes']
            self.assertEqual(plan_singleton_dag(arena, roots, set(labels), cache), expected)
            self.assertEqual(arena.stats['singleton_dag_metadata_nodes'], count)
            if expected:
                # Cached root content cannot cache an obsolete live set.
                alive = set(labels) - {expected[0]['generator']}
                after = plan_singleton_dag(arena, roots, alive, cache)
                self.assertTrue(all(p['generator'] in alive for p in after))
            # Reordering roots must reconstruct every original donor slot.
            reordered = list(reversed(roots))
            for pivot in plan_singleton_dag(arena, reordered, set(labels), cache):
                child = pivot['generator']
                word = words[len(words) - 1 - pivot['relation']]
                self.assertEqual(sum(abs(x) == child for x in word), 1)
                self.assertEqual(max(map(abs, word)), child)

    def test_random_signed_nonnumeric_dags_and_every_retained_relator(self):
        rng = random.Random(261009102)
        general = False
        for _ in range(100):
            labels = rng.sample(range(1, 500), 7)
            ordered_donors = []
            images = {g: [g] for g in labels[:2]}
            for index, child in enumerate(labels[2:], 2):
                body = [rng.choice(labels[:index]) * rng.choice((-1, 1))
                        for _ in range(rng.randrange(1, 7))]
                position = rng.randrange(len(body) + 1)
                signed = child * rng.choice((-1, 1))
                word = body[:position] + [signed] + body[position:]
                rest = word[position + 1:] + word[:position]
                definition = inverse(rest) if signed > 0 else rest
                images[child] = substitute(definition, images)
                ordered_donors.append((word, child))
            donors = ordered_donors[:]
            rng.shuffle(donors)
            words = [word for word, _ in donors]
            words += [[rng.choice(labels) * rng.choice((-1, 1)) for _ in range(11)]
                      for _ in range(4)]
            pivots = [dict(relation=slot, generator=child)
                      for slot, (_, child) in enumerate(donors)]
            rng.shuffle(pivots)
            expected = [[] for _ in donors] + [substitute(word, images) for word in words[len(donors):]]
            ordered_pivots = sorted(pivots, key=lambda pivot: labels.index(pivot['generator']))
            move = dict(kind='singleton_dag', pivots=ordered_pivots)
            arena, other = WordArena(), WordArena()
            roots = [arena.from_word(word) for word in words]
            replayed = [other.from_word(word) for word in words]
            alive, other_alive, literal_alive = set(labels), set(labels), set(labels)
            literal = deepcopy(words)
            apply_singleton_dag(arena, roots, alive, pivots)
            self.assertTrue(replay_compressed_singleton_dag(other, replayed, other_alive, move))
            self.assertTrue(replay_literal_singleton_dag(
                literal, literal_alive, move, _Budget(lambda: None, 1000000, 10000000)))
            self.assertEqual([list(arena.expand(root)) for root in roots], expected)
            self.assertEqual([list(other.expand(root)) for root in replayed], expected)
            self.assertEqual(literal, expected)
            self.assertEqual(alive, set(labels[:2]))
            self.assertEqual(alive, other_alive)
            self.assertEqual(alive, literal_alive)
            general |= bool(arena.stats.get('singleton_dag_general_mask_nodes'))
        self.assertTrue(general)

    def test_actual_stabilized_circles_contract_in_one_raw_batch(self):
        for crossings in (4, 8, 32, 128):
            diagram = Diagram.from_braid(crossings + 1, list(range(1, crossings + 1)))
            alive, words = _presentation(diagram, _Budget(lambda: None, 100000, 1000000))
            arena = WordArena()
            roots = [arena.from_word(word) for word in words]
            self.assertEqual(len(plan_forest(arena, roots, alive)), 2)
            pivots = plan_singleton_dag(arena, roots, alive)
            self.assertEqual(len(pivots), crossings - 1)
            move = dict(kind='singleton_dag', pivots=pivots)
            other = WordArena()
            replayed = [other.from_word(word) for word in words]
            other_alive = set(alive)
            with patch.object(arena, 'reduce', side_effect=AssertionError), \
                    patch.object(arena, 'cyclic_reduce', side_effect=AssertionError), \
                    patch.object(arena, 'expand', side_effect=AssertionError), \
                    patch.object(arena, 'equal', side_effect=AssertionError), \
                    patch.object(arena, 'inverse', side_effect=AssertionError):
                apply_singleton_dag(arena, roots, alive, pivots)
                self.assertTrue(verify_compressed_rank_one(arena, roots, alive,
                    dict(kind='rank_one_exponent_zero', generator=1)))
            with patch.object(other, 'reduce', side_effect=AssertionError), \
                    patch.object(other, 'cyclic_reduce', side_effect=AssertionError), \
                    patch.object(other, 'expand', side_effect=AssertionError), \
                    patch.object(other, 'equal', side_effect=AssertionError):
                self.assertTrue(replay_compressed_singleton_dag(other, replayed, other_alive, move))
                self.assertTrue(verify_compressed_rank_one(other, replayed, other_alive,
                    dict(kind='rank_one_exponent_zero', generator=1)))
            self.assertEqual(alive, {1})
            self.assertEqual(len(roots), len(words))
            self.assertEqual(arena.stats['singleton_dag_rounds'], 1)
            self.assertEqual(arena.stats['singleton_dag_pivots'], crossings - 1)
            self.assertNotIn('singleton_dag_general_mask_nodes', arena.stats)

    def test_exponential_raw_nonnormalized_output_stays_small(self):
        rank = 512
        words = conjugation_chain(rank)
        arena = WordArena(max_nodes=20000, max_work=1000000)
        roots = [arena.from_word(word) for word in words]
        alive = set(range(1, rank + 1))
        initial = len(arena.rules)
        pivots = plan_singleton_dag(arena, roots, alive)
        self.assertEqual(len(pivots), rank - 1)
        with patch.object(arena, 'reduce', side_effect=AssertionError), \
                patch.object(arena, 'cyclic_reduce', side_effect=AssertionError), \
                patch.object(arena, 'expand', side_effect=AssertionError), \
                patch.object(arena, 'equal', side_effect=AssertionError), \
                patch.object(arena, 'inverse', side_effect=AssertionError):
            apply_singleton_dag(arena, roots, alive, pivots)
            self.assertEqual(arena.lengths[roots[-1]], 1 << (rank - 1))
            self.assertTrue(verify_compressed_rank_one(arena, roots, alive,
                dict(kind='rank_one_exponent_zero', generator=1)))
        self.assertEqual(alive, {1})
        self.assertLess(len(arena.rules), 4 * initial)
        self.assertLess(arena.stats['work'], 200 * rank)
        self.assertEqual(len(roots), rank)

    def test_singletons_hidden_in_large_shared_powers(self):
        arena = WordArena(max_nodes=10000)
        # A repeated subgrammar must count occurrences by multiplicity, not
        # merely by the number of distinct terminal nodes in the grammar.
        huge = arena.power(arena.from_word([7, -3, 7]), 1 << 256)
        duplicate = arena.concat(huge, arena.letter(-7))
        donor = arena.concat(huge, arena.letter(-11))
        roots = [duplicate, donor, arena.from_word([11, -7])]
        alive = {3, 7, 11}
        selected = plan_singleton_dag(arena, roots, alive)
        self.assertEqual(selected, [dict(relation=1, generator=11)])
        with patch.object(arena, 'expand', side_effect=AssertionError), \
                patch.object(arena, 'reduce', side_effect=AssertionError), \
                patch.object(arena, 'equal', side_effect=AssertionError):
            apply_singleton_dag(arena, roots, alive, selected)
        self.assertEqual(alive, {3, 7})
        self.assertEqual(roots[1], 0)
        self.assertEqual(arena.lengths[roots[2]], 3 * (1 << 256) + 1)

    def test_internal_preconditions_cycles_unary_definitions_and_atomic_roots(self):
        cases = [
            ([[1, -2], [2, -1]], [dict(relation=0, generator=1), dict(relation=1, generator=2)]),
            ([[1, -2], [1, 3]], [dict(relation=0, generator=1), dict(relation=1, generator=1)]),
            ([[1, -2]], [dict(relation=0, generator=1), dict(relation=0, generator=2)]),
            ([[1, -2, 1]], [dict(relation=0, generator=1)]),
            ([[1, -2]], [dict(relation=0, generator=3)]),
        ]
        for words, pivots in cases:
            arena = WordArena()
            roots = [arena.from_word(word) for word in words]
            alive = {1, 2, 3}
            before = roots[:]
            with self.assertRaises(ValueError):
                apply_singleton_dag(arena, roots, alive, pivots)
            self.assertEqual(roots, before)
            self.assertEqual(alive, {1, 2, 3})
        arena = WordArena()
        roots = [arena.from_word(word) for word in ([1], [-2], [3], [1, -2, 3])]
        alive = {1, 2, 3}
        selected = plan_singleton_dag(arena, roots, alive)
        apply_singleton_dag(arena, roots, alive, selected)
        self.assertEqual(alive, set())
        self.assertEqual(roots, [0, 0, 0, 0])

    def test_resource_caps_cancellation_and_independent_checker(self):
        words = conjugation_chain(8)
        arena = WordArena()
        roots = [arena.from_word(word) for word in words]
        alive = set(range(1, 9))
        pivots = plan_singleton_dag(arena, roots, alive)
        move = dict(kind='singleton_dag', pivots=pivots)
        with patch('fastunknot.singleton_dag.plan_singleton_dag', side_effect=AssertionError), \
                patch('fastunknot.singleton_dag.apply_singleton_dag', side_effect=AssertionError):
            self.assertTrue(replay_compressed_singleton_dag(arena, roots, alive, move))
            self.assertTrue(replay_literal_singleton_dag(deepcopy(words), set(range(1, 9)), move,
                _Budget(lambda: None, 100000, 1000000)))
        with self.assertRaises(GroupLimit):
            replay_literal_singleton_dag(deepcopy(words), set(range(1, 9)), move,
                _Budget(lambda: None, 100, 1000000))
        arena = WordArena()
        roots = [arena.from_word(word) for word in words]
        alive = set(range(1, 9))
        before = roots[:]
        arena.left = 0
        with self.assertRaises(CompressedLimit):
            apply_singleton_dag(arena, roots, alive, pivots)
        self.assertEqual(roots, before)
        self.assertEqual(alive, set(range(1, 9)))
        with self.assertRaises(CompressedLimit):
            plan_singleton_dag(arena, roots, alive)

        def cancel():
            raise RuntimeError('external cancellation')

        arena.check = cancel
        with self.assertRaisesRegex(RuntimeError, 'external cancellation'):
            apply_singleton_dag(arena, roots, alive, pivots)


if __name__ == '__main__':
    unittest.main()
