"""Exact alphabet barriers and incremental witness stopping for compressed LCS."""
import random
import unittest
from unittest.mock import patch
from fastunknot.compressed_words import WordArena, CompressedLimit
from fastunknot.compressed_lcs import CommonSubstring
from fastunknot.compressed_overlap import whole_donor_move, cyclic_overlap_move, apply_cyclic_overlap
from test_compressed_lcs import parsed, literal_lcs


class LCSBoundTests(unittest.TestCase):
    def test_shared_signed_alphabet_run_summaries(self):
        rng = random.Random(2902)
        for _ in range(400):
            arena = WordArena()
            word = [rng.choice((-3, -2, -1, 1, 2, 3)) for _ in range(rng.randrange(1, 65))]
            root = parsed(arena, word, rng)
            allowed = {x for x in (-3, -2, -1, 1, 2, 3) if rng.randrange(2)}
            terminals = {arena.letter(x) for x in allowed}
            nodes = arena._reachable([root])
            bounds = CommonSubstring(arena).shared_runs(nodes, terminals)
            for node in nodes:
                maximum = run = 0
                for letter in arena.expand(node):
                    run = run+1 if letter in allowed else 0
                    maximum = max(maximum, run)
                self.assertEqual(bounds[node], maximum)
        arena.left = 0
        with self.assertRaises(CompressedLimit):
            CommonSubstring(arena).shared_runs(nodes, terminals)

    def test_exponential_uncapped_answers_stop_without_occurrence_tables(self):
        for h in (8, 32, 100, 500):
            arena, n = WordArena(max_work=100000), 2**h
            run = arena.power(arena.letter(1), n)
            x = arena.concat(run, arena.from_word([2, 2]))
            y = arena.concat(run, arena.from_word([3, 3]))
            x, y = arena.concat(x, x), arena.concat(y, y)
            with patch('fastunknot.compressed_lcs.MatchTable', side_effect=AssertionError('bound should finish')):
                self.assertEqual(CommonSubstring(arena).longest(x, y), (n, 0, 0))
            self.assertEqual(arena.stats['lcs_bound_stops'], 1)
            self.assertNotIn('match_cells', arena.stats)
            self.assertNotIn('lcs_cut_pairs', arena.stats)
        # No common prefix: the first cut extension reaches the new global
        # bound. The overlap generator must stop before requesting any table.
        arena = WordArena(max_work=100000)
        half = arena.power(arena.letter(1), 2**499)
        x = arena.concat(arena.concat(arena.letter(2), half), arena.concat(half, arena.letter(2)))
        y = arena.concat(arena.concat(arena.letter(3), half), arena.concat(half, arena.letter(3)))
        matcher = CommonSubstring(arena)
        with patch.object(matcher, 'overlaps', side_effect=AssertionError('witness already attains bound')):
            self.assertEqual(matcher.longest(x, y), (2**500, 1, 1))
        self.assertEqual(arena.stats['lcs_extensions'], 1)

    def test_local_bound_stops_preserve_global_maximum(self):
        x = [1,3,2,1,1,2,3,1,3,3,2,2,1,1,3,2,3,3,1,1,1,2,1,2,2]
        y = [4,1,4,2,2,1,1,1,4,2,2,1,2,4,2,4,1,1,2,2,4,4,4,2,4]
        arena = WordArena()
        length, i, j = CommonSubstring(arena).longest(arena.from_word(x), arena.from_word(y))
        self.assertEqual(length, literal_lcs(x, y))
        self.assertEqual(x[i:i+length], y[j:j+length])
        self.assertGreater(arena.stats.get('lcs_pair_stops', 0), 0)
        # Same alphabet must still use the exact fallback; an alphabet bound
        # says nothing about ordering or about different generator signs.
        x, y = [1,2]*11+[-1], [2,1,1,2]*5+[-1]
        arena = WordArena()
        length, i, j = CommonSubstring(arena).longest(arena.from_word(x), arena.from_word(y))
        self.assertEqual(length, literal_lcs(x, y))
        self.assertEqual(x[i:i+length], y[j:j+length])
        self.assertEqual(arena.stats.get('lcs_bound_nodes', 0), 0)

    def test_partial_cyclic_move_with_loose_total_count_bound(self):
        arena, n = WordArena(max_work=100000), 2**500
        long_run = arena.power(arena.letter(1), n)
        short_run = arena.power(arena.letter(1), n//4)
        roots = []
        for g in (2, 3):
            gap = arena.from_word([g, g])
            roots.append(arena.concat(arena.concat(long_run, gap), arena.concat(short_run, gap)))
        with patch.object(arena, 'expand', side_effect=AssertionError('must not expand')), \
             patch('fastunknot.compressed_lcs.MatchTable', side_effect=AssertionError('run bound should finish')):
            self.assertIsNone(whole_donor_move(arena, roots))
            move = cyclic_overlap_move(arena, roots)
            self.assertEqual(move['overlap'], n)
            apply_cyclic_overlap(arena, roots, move)
        self.assertEqual(sum(arena.lengths[r] for r in roots), n+3*(n//4)+12)
        self.assertGreater(arena.stats['lcs_bound_nodes'], 0)


if __name__ == '__main__':
    unittest.main()
