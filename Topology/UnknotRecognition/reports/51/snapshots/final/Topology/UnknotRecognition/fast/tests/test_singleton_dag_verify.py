"""Independent evidence, residual preservation, and source-bound v8 coverage."""
from copy import deepcopy
import unittest
from unittest.mock import patch

from fastunknot.compressed_search import compressed_certificate, _search
from fastunknot.compressed_words import WordArena, CompressedLimit
from fastunknot.diagram import Diagram
from fastunknot.group_certificate import (
    _Budget, GroupLimit, group_decide, verify_group_certificate,
)
from fastunknot.primitive_projection_verify import verify_compressed_rank_one
from fastunknot.singleton_dag_verify import (
    replay_compressed_singleton_dag, replay_literal_singleton_dag,
)


def move(*pivots):
    return dict(kind='singleton_dag', pivots=[
        dict(relation=slot, generator=child) for slot, child in pivots])


def compressed_state(words):
    arena = WordArena(max_work=5_000_000)
    roots = [arena.from_word(word) for word in words]
    alive = {abs(letter) for word in words for letter in word}
    return arena, roots, alive


class SingletonDAGVerifierTests(unittest.TestCase):
    def check_both(self, words, evidence, expected=True):
        arena, roots, alive = compressed_state(words)
        original_roots, original_alive = roots[:], alive.copy()
        literal, live = deepcopy(words), alive.copy()
        self.assertEqual(replay_compressed_singleton_dag(
            arena, roots, alive, evidence), expected)
        self.assertEqual(replay_literal_singleton_dag(
            literal, live, evidence, _Budget(lambda: None, 1_000_000, 5_000_000)),
            expected)
        if expected:
            self.assertEqual([list(arena.expand(root)) for root in roots], literal)
            self.assertEqual(alive, live)
        else:
            self.assertEqual(roots, original_roots)
            self.assertEqual(alive, original_alive)
            self.assertEqual(literal, words)
            self.assertEqual(live, original_alive)
        return arena, roots, alive

    def test_arbitrary_labels_signs_and_noncommuting_dependencies(self):
        words = [[9, -5, 8], [5, 9, 5, -2, -8], [2, 8, -2, -9],
                 [2, 5, -9, -5, -2, 8]]
        evidence = move((0, 5), (1, 2))
        arena, roots, alive = self.check_both(words, evidence)
        self.assertEqual(alive, {8, 9})
        self.assertEqual(roots[:2], [0, 0])
        self.assertTrue(roots[2])
        # List order is a checked topological certificate, independent of labels.
        self.check_both(words, move((1, 2), (0, 5)), expected=False)

    def test_all_nondonor_relations_survive_and_can_obstruct_endpoint(self):
        words = [[1, -2], [2, -3], [1, 1], [3, -3]]
        arena, roots, alive = self.check_both(words, move((0, 2), (1, 3)))
        self.assertEqual(len(roots), len(words))
        self.assertFalse(verify_compressed_rank_one(
            arena, roots, alive, dict(kind='rank_one_exponent_zero', generator=1)))
        self.assertEqual(list(arena.expand(roots[2])), [1, 1])

    def test_rejects_cycles_even_without_surviving_relators(self):
        self.check_both([[1, -2], [2, -1]], move((0, 1), (1, 2)), False)
        self.check_both([[1, 2], [2, 1]], move((0, 1), (1, 2)), False)
        self.check_both([[3, -1], [1, -2], [2, -3]],
                        move((0, 1), (1, 2), (2, 3)), False)

    def test_rejects_schema_and_literal_singleton_forgeries(self):
        words = [[1, -2], [2, -3], [2, 2, -2, 1], [1, 1]]
        valid = move((0, 2), (1, 3))
        bad = [move(), move((0, 2), (0, 1)), move((0, 2), (1, 2)),
               move((2, 2)), move((4, 2)), move((0, 8)), move((True, 2)),
               move((0, True)), dict(kind='singleton_dag', pivots='wrong')]
        for field, value in [('extra', 1), ('kind', 'primitive_forest')]:
            altered = deepcopy(valid)
            altered[field] = value
            bad.append(altered)
        altered = deepcopy(valid)
        altered['pivots'][0]['image'] = [1]
        bad.append(altered)
        for evidence in bad:
            with self.subTest(evidence=evidence):
                self.check_both(words, evidence, False)

    def test_compressed_replay_uses_no_producer_or_normalization(self):
        arena, roots, alive = compressed_state([[1, -2], [1, 2, -1, -3], [3, -1]])
        with (patch('fastunknot.singleton_dag.plan_singleton_dag', side_effect=AssertionError),
              patch('fastunknot.singleton_dag.apply_singleton_dag', side_effect=AssertionError),
              patch.object(arena, 'reduce', side_effect=AssertionError),
              patch.object(arena, 'cyclic_reduce', side_effect=AssertionError),
              patch.object(arena, 'inverse', side_effect=AssertionError),
              patch.object(arena, 'equal', side_effect=AssertionError),
              patch.object(arena, 'expand', side_effect=AssertionError)):
            self.assertTrue(replay_compressed_singleton_dag(
                arena, roots, alive, move((0, 2), (1, 3))))
            self.assertTrue(verify_compressed_rank_one(
                arena, roots, alive, dict(kind='rank_one_exponent_zero', generator=1)))

    def test_version_eight_is_source_bound_and_default_is_unchanged(self):
        for strands in [5, 9, 17]:
            diagram = Diagram.from_braid(strands, list(range(1, strands)))
            old = compressed_certificate(diagram, primitive_forest=True)
            self.assertEqual(old, compressed_certificate(
                diagram, primitive_forest=True, singleton_dag=False))
            certificate = compressed_certificate(diagram, singleton_dag=True)
            self.assertEqual(certificate['version'], 8)
            self.assertEqual(len(certificate['moves']), 1)
            self.assertEqual(len(certificate['moves'][0]['pivots']), strands - 2)
            for compressed in [False, True]:
                self.assertTrue(verify_group_certificate(diagram, certificate,
                                                        compressed=compressed))
                self.assertTrue(verify_group_certificate(diagram, old, compressed=compressed))
                for version in range(5, 8):
                    altered = deepcopy(certificate)
                    altered['version'] = version
                    self.assertFalse(verify_group_certificate(diagram, altered,
                                                             compressed=compressed))
            other = Diagram.from_braid(2, [1, 1, 1])
            altered = deepcopy(certificate)
            altered['input_pd'] = [list(row) for row in other.pd]
            self.assertFalse(verify_group_certificate(other, altered, compressed=True))

    def test_resource_limits_and_caller_cancellation_propagate(self):
        words = [[1] * 20 + [-2], [2] * 20 + [-3], [3, -3]]
        evidence = move((0, 2), (1, 3))
        with self.assertRaises(GroupLimit):
            replay_literal_singleton_dag(deepcopy(words), {1, 2, 3}, evidence,
                                         _Budget(lambda: None, 100, 5_000_000))
        arena, roots, alive = compressed_state(words)
        arena.left = 2
        with self.assertRaises(CompressedLimit):
            replay_compressed_singleton_dag(arena, roots, alive, evidence)
        arena, roots, alive = compressed_state(words)
        def cancel():
            raise RuntimeError('caller cancellation')
        arena.check = cancel
        with self.assertRaisesRegex(RuntimeError, 'caller cancellation'):
            replay_compressed_singleton_dag(arena, roots, alive, evidence)

    def test_opt_in_public_group_api_and_argument_validation(self):
        diagram = Diagram.from_braid(9, list(range(1, 9)))
        result = group_decide(diagram, singleton_dag=True, seconds=None)
        self.assertEqual(result['status'], 'UNKNOT')
        self.assertEqual(result['certificate']['version'], 8)
        self.assertEqual(result['verification_backend'], 'compressed-slp')
        for function in [compressed_certificate, group_decide]:
            with self.assertRaises(ValueError):
                function(diagram, singleton_dag=1)

    def test_terminal_guard_preserves_partial_state_and_legacy_moves(self):
        words = [[1, -2], [1, 2, -1, -3], [4, 5, -4, 5]]
        outputs = []
        for enabled in [False, True]:
            arena, roots, alive = compressed_state(words)
            moves, terminal = [], {}
            with patch('fastunknot.singleton_dag.apply_singleton_dag',
                       side_effect=AssertionError('partial batch must be skipped')):
                decision = _search(arena, roots, alive, moves,
                                   primitive_terminal=terminal, singleton_dag=enabled)
            outputs.append((decision, moves, terminal, alive,
                            [list(arena.expand(root)) for root in roots]))
            if enabled:
                self.assertGreater(arena.stats['singleton_dag_partial_skips'], 0)
        self.assertEqual(outputs[0], outputs[1])


if __name__ == '__main__':
    unittest.main()
