"""Exact literal and compressed oracles for short-period phase certificates."""
import random
import unittest
from unittest.mock import patch

from fastunknot.compressed_lcs import CommonSubstring
from fastunknot.compressed_words import WordArena, CompressedLimit
from test_compressed_lcs import lcp, parsed


class PeriodicOverlapTests(unittest.TestCase):
    def test_rotations_truncations_and_short_exceptional_overlaps(self):
        rng = random.Random(3013)
        blocks = [[1, 1, 2, 1, 1, 3], [-2, 1, -2, 1], [1]]
        blocks += [[rng.choice((-3, -2, -1, 1, 2, 3))
                    for _ in range(rng.randrange(1, 33))] for _ in range(150)]
        for block in blocks:
            shift = rng.randrange(len(block))
            rotated = block[shift:]+block[:shift]
            x = (rotated*300)[:rng.randrange(128, 300)]
            y = (block*300)[:rng.randrange(128, 300)]
            arena = WordArena(max_work=1000000)
            matcher = CommonSubstring(arena)
            u, v = parsed(arena, x, rng), parsed(arena, y, rng)
            with patch('fastunknot.compressed_lcs.MatchTable',
                       side_effect=AssertionError('certified period needs no table')):
                aps = matcher.overlaps(u, v)
            values = [p+i*d for p, d, n in aps for i in range(n)]
            expected = {k for k in range(1, min(len(x), len(y))+1) if x[-k:] == y[:k]}
            self.assertEqual(set(values), expected, (block, shift, len(x), len(y), aps))
            self.assertEqual(len(values), len(expected))

    def test_sample_is_only_a_proposal_and_long_period_falls_back(self):
        cases = []
        periodic = [1, 2]*90
        for position in (64, 100, 179):
            corrupted = periodic.copy()
            corrupted[position] = 3
            cases.extend(((periodic, corrupted), (corrupted, periodic)))
        long_period = (list(range(1, 34))*6)[:180]
        cases.append((long_period, long_period))
        for x, y in cases:
            arena = WordArena(max_work=10000000)
            u, v = arena.from_word(x), arena.from_word(y)
            matcher = CommonSubstring(arena)
            self.assertIsNone(matcher.periodic_overlaps(u, v))
            # Keep exercising the general table path after phase rejection;
            # sparse endpoint certificates have their own literal oracles.
            with patch.object(matcher, 'sparse_overlaps', return_value=None), \
                 patch.object(matcher, 'progression_overlaps', return_value=None), \
                 patch.object(matcher, 'anchor_overlaps', return_value=None):
                aps = matcher.overlaps(u, v)
            self.assertEqual({p+i*d for p, d, n in aps for i in range(n)},
                             {k for k in range(1, 181) if x[-k:] == y[:k]})
            self.assertGreater(arena.stats.get('match_cells', 0), 0)

    def test_exponential_phase_shifted_words_and_work_limit(self):
        arena, n = WordArena(max_work=20000), 2**500
        block = list(range(1, 33))
        x = arena.power(arena.from_word(block[7:]+block[:7]), n)
        y = arena.power(arena.from_word(block), n)
        matcher = CommonSubstring(arena)
        with patch.object(arena, 'expand', side_effect=AssertionError('must not expand')), \
             patch('fastunknot.compressed_lcs.MatchTable',
                   side_effect=AssertionError('must not build table')):
            self.assertEqual(matcher.overlaps(x, y), [(7, 32, n)])
        self.assertEqual(arena.stats['lcs_periodic_hits'], 1)
        arena.left = 0
        with self.assertRaises(CompressedLimit):
            CommonSubstring(arena).overlaps(x, y)

    def test_phase_progressions_feed_exact_critical_extensions(self):
        rng = random.Random(3014)
        for _ in range(30):
            block = [1, 2]+[rng.choice((1, 2, 3)) for _ in range(rng.randrange(5))]
            left, other_right = block*70, block*80
            right = block*rng.randrange(4)+[3, 2]
            other_left = [2, 3]+block*rng.randrange(4)
            arena = WordArena(max_work=2000000)
            x = arena.concat(arena.from_word(left), arena.from_word(right))
            y = arena.concat(arena.from_word(other_left), arena.from_word(other_right))
            matcher = CommonSubstring(arena)
            aps = matcher.overlaps(arena.rules[x][1], arena.rules[y][2])
            self.assertEqual(arena.stats['lcs_periodic_hits'], 1)
            for p, d, n in aps:
                candidates = matcher.critical(x, y, (p, d, n))
                expected = max(k+lcp(left[:-k][::-1], other_left[::-1])+
                               lcp(right, other_right[k:]) for k in (p+i*d for i in range(n)))
                self.assertEqual(max(matcher.extension(x, y, k)[0] for k in candidates), expected)


if __name__ == '__main__':
    unittest.main()
