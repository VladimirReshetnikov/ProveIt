"""Boundary and resource regressions for localized overlap queries."""
import random
import unittest
from unittest.mock import patch

from fastunknot.compressed_lcs import CommonSubstring
from fastunknot.compressed_words import WordArena
from test_compressed_lcs import parsed


class LCSWindowTests(unittest.TestCase):
    def test_asymmetric_periodic_windows_and_original_cache_keys(self):
        rng = random.Random(3012)
        for _ in range(200):
            block = [rng.choice((-2, -1, 1, 2)) for _ in range(rng.randrange(1, 6))]
            core = block*rng.randrange(2, 12)
            prefix = [3]*rng.randrange(0, 100)
            suffix = [-3]*rng.randrange(0, 100)
            arena = WordArena(max_work=2000000)
            matcher = CommonSubstring(arena)
            for x, y in ((prefix+core, core), (core, core+suffix),
                         (prefix+core, core+suffix), ([], core), (core, [])):
                u, v = parsed(arena, x, rng), parsed(arena, y, rng)
                aps = matcher.overlaps(u, v)
                values = [p+i*d for p, d, n in aps for i in range(n)]
                expected = {k for k in range(1, min(len(x), len(y))+1)
                            if x[-k:] == y[:k]}
                self.assertEqual(set(values), expected, (x, y, aps))
                self.assertEqual(len(values), len(expected))
                # Repeated caller roots must hit the cache even when cropped.
                with patch('fastunknot.compressed_lcs.MatchTable',
                           side_effect=AssertionError('cached query rebuilt')):
                    self.assertIs(matcher.overlaps(u, v), aps)

    def test_exponential_outside_context_does_not_obscure_uniform_overlap(self):
        arena, n = WordArena(max_work=20000), 2**500
        outside = arena.power(arena.from_word([2, -3]), n)
        run = arena.power(arena.letter(1), 63)
        matcher = CommonSubstring(arena)
        with patch.object(arena, 'expand', side_effect=AssertionError('must not expand')):
            self.assertEqual(matcher.overlaps(arena.concat(outside, run), run), [(1, 1, 63)])
            self.assertEqual(matcher.overlaps(run, arena.concat(run, outside)), [(1, 1, 63)])

    def test_equal_bigrams_exact_lcs_with_exponential_prefix(self):
        arena, n = WordArena(max_work=20000), 2**500
        run = arena.power(arena.from_word([1, 2]), n)
        tail = arena.from_word([1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 2, 3])
        x = arena.concat(run, arena.concat(arena.letter(3), tail))
        y = arena.concat(run, arena.concat(arena.letter(1), tail))
        with patch.object(arena, 'expand', side_effect=AssertionError('must not expand')):
            self.assertEqual(CommonSubstring(arena).longest(x, y), (2*n, 0, 0))
        self.assertGreater(arena.stats.get('lcs_window_queries', 0), 0)


if __name__ == '__main__':
    unittest.main()
