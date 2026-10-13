"""Directed signed transition bounds and safe whole-donor impossibility filters."""
import random
import unittest
from unittest.mock import patch
from fastunknot.compressed_lcs import CommonSubstring, adjacent_pairs
from fastunknot.compressed_words import WordArena, CompressedLimit
from fastunknot.compressed_overlap import whole_donor_move, cyclic_overlap_move, apply_cyclic_overlap
from test_compressed_lcs import parsed, literal_lcs


class LCSTransitionTests(unittest.TestCase):
    def test_adjacencies_and_transition_runs_against_literal_words(self):
        rng = random.Random(3001)
        alphabet = (-2, -1, 1, 2)
        for _ in range(400):
            arena = WordArena()
            root = parsed(arena, [rng.choice(alphabet) for _ in range(rng.randrange(1, 70))], rng)
            nodes = arena._reachable([root])
            word = arena.expand(root)
            self.assertEqual(adjacent_pairs(arena, nodes), set(zip(word, word[1:])))
            allowed = {x for x in alphabet if rng.randrange(2)}
            transitions = {(x, y) for x in alphabet for y in alphabet if rng.randrange(2)}
            bound = CommonSubstring(arena).transition_runs(nodes, {arena.letter(x) for x in allowed}, transitions)
            for node in nodes:
                maximum = run = 0
                previous = None
                for letter in arena.expand(node):
                    if letter not in allowed:
                        run = 0
                    elif run and (previous, letter) in transitions:
                        run += 1
                    else:
                        run = 1
                    maximum = max(maximum, run)
                    previous = letter
                self.assertEqual(bound[node], maximum)
        arena.left = 0
        with self.assertRaises(CompressedLimit):
            adjacent_pairs(arena, nodes)
        with self.assertRaises(CompressedLimit):
            CommonSubstring(arena).transition_runs(nodes, set(), set())

    def test_same_alphabet_exponential_queries_without_tables(self):
        for h in (8, 32, 100, 500):
            arena, n = WordArena(max_work=100000), 2**h
            run = arena.power(arena.from_word([1, 2]), n)
            x, y = arena.concat(run, arena.from_word([1, 3])), arena.concat(run, arena.from_word([3, 1]))
            with patch('fastunknot.compressed_lcs.MatchTable', side_effect=AssertionError('bound must finish')):
                self.assertEqual(CommonSubstring(arena).longest(x, y), (2*n, 0, 0))
            self.assertEqual(arena.stats['lcs_transition_stops'], 1)
            self.assertNotIn('lcs_cut_pairs', arena.stats)
        arena = WordArena(max_work=100000)
        half = arena.power(arena.from_word([1, 2]), 2**499)
        x = arena.concat(arena.concat(arena.letter(3), half), arena.concat(half, arena.letter(2)))
        y = arena.concat(arena.concat(arena.letter(2), half), arena.concat(half, arena.letter(3)))
        matcher = CommonSubstring(arena)
        with patch.object(matcher, 'overlaps', side_effect=AssertionError('first extension attains bound')):
            self.assertEqual(matcher.longest(x, y), (2**501, 1, 1))
        self.assertEqual(arena.stats['lcs_extensions'], 1)
        # Equal alphabets and equal bigram sets do not imply equal strings.
        tail = [1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 2, 3]
        x, y = [1, 2]*32+[3]+tail, [1, 2]*32+[1]+tail
        arena = WordArena()
        u, v = arena.from_word(x), arena.from_word(y)
        self.assertEqual(adjacent_pairs(arena, arena._reachable([u])), adjacent_pairs(arena, arena._reachable([v])))
        length, i, j = CommonSubstring(arena).longest(u, v)
        self.assertEqual(length, literal_lcs(x, y))
        self.assertEqual(x[i:i+length], y[j:j+length])
        self.assertGreater(arena.stats.get('lcs_cut_pairs', 0), 0)
        self.assertEqual(arena.stats.get('lcs_transition_bound_nodes', 0), 0)

    def test_whole_donor_filter_retains_cyclic_seams_and_inverse_order(self):
        for target in ([2, 1], [-2, -1]):
            arena = WordArena()
            roots = [arena.from_word([1, 2]), arena.from_word(target)]
            move = whole_donor_move(arena, roots)
            self.assertIsNotNone(move)
            self.assertEqual(move['overlap'], 2)
            self.assertEqual(move['inverse'], target[0] < 0)
        arena = WordArena()
        roots = [arena.from_word([1, 2, 3]), arena.from_word([1, 3, 2])]
        with patch('fastunknot.compressed_overlap.first_occurrence', side_effect=AssertionError('pair filter must reject')), \
             patch.object(arena, 'inverse', side_effect=AssertionError('do not allocate an ineligible inverse')):
            self.assertIsNone(whole_donor_move(arena, roots))
        self.assertEqual(arena.stats['overlap_adjacency_skips'], 4)
        arena.max_nodes = 1  # Existing rules retained; test the independent new cache cap.
        with self.assertRaisesRegex(CompressedLimit, 'adjacency cache'):
            whole_donor_move(arena, roots)

    def test_uniform_whole_donor_pairs_need_no_grammar_traversal(self):
        arena, n = WordArena(max_work=100000), 2**500
        roots = [arena.power(arena.letter(1), n), arena.power(arena.letter(1), n*n+1)]
        with patch('fastunknot.compressed_overlap.adjacent_pairs',
                   side_effect=AssertionError('uniform metadata already determines every pair')):
            move = whole_donor_move(arena, roots)
        self.assertEqual(move['kind'], 'relator_power')
        self.assertEqual(move['copies'], n)
        # Single-letter donors have no internal pairs, including inverse-only matches.
        for letter in (1, -1):
            arena = WordArena()
            roots = [arena.letter(1), arena.power(arena.letter(letter), 3)]
            with patch('fastunknot.compressed_overlap.adjacent_pairs', side_effect=AssertionError):
                move = whole_donor_move(arena, roots)
            self.assertEqual(move['inverse'], letter < 0)
            self.assertEqual(move['copies'], 3)

    def test_same_alphabet_partial_move_reaches_the_new_fallback(self):
        arena, n = WordArena(max_work=100000), 2**500
        run = arena.power(arena.from_word([1, 2]), n)
        roots = [arena.concat(run, arena.from_word([1, 3])), arena.concat(run, arena.from_word([3, 1]))]
        with patch.object(arena, 'expand', side_effect=AssertionError('must not expand')), \
             patch('fastunknot.compressed_lcs.MatchTable', side_effect=AssertionError('bounds should finish')), \
             patch('fastunknot.compressed_overlap.first_occurrence', side_effect=AssertionError('whole filter should reject')):
            self.assertIsNone(whole_donor_move(arena, roots))
            move = cyclic_overlap_move(arena, roots)
            self.assertEqual(move['overlap'], 2*n)
            apply_cyclic_overlap(arena, roots, move)
        self.assertEqual(sum(arena.lengths[root] for root in roots), 2*n+6)
        self.assertEqual(arena.expand(roots[move['target']]), [-3, -1, 3, 1])


if __name__ == '__main__':
    unittest.main()
