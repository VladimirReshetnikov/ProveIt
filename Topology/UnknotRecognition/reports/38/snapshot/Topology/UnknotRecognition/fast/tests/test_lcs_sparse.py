"""Sparse endpoint candidates must be complete and individually exact."""
import random
import unittest
from unittest.mock import patch

from fastunknot.compressed_lcs import CommonSubstring
from fastunknot.compressed_words import WordArena, CompressedLimit
from test_compressed_lcs import parsed


class SparseOverlapTests(unittest.TestCase):
    def test_both_endpoint_directions_signed_random_parses(self):
        rng = random.Random(3014)
        for trial in range(160):
            core = [rng.choice((-2, -1, 1, 2)) for _ in range(rng.randrange(1, 60))]
            left = [rng.choice((-2, -1, 1, 2)) for _ in range(150)]
            right = [rng.choice((-2, -1, 1, 2)) for _ in range(150)]
            if trial % 2:
                # The first letter of y is rare in x; the opposite sign
                # elsewhere must not count as the same endpoint.
                left[25] = left[75] = -3
                core = [-3]+core
                x, y = left+[3]+core, core+[3]+right
            else:
                right[25] = right[75] = 3
                core += [3]
                x, y = left+[-3]+core, core+[-3]+right
            arena = WordArena(max_work=2000000)
            u, v = parsed(arena, x, rng), parsed(arena, y, rng)
            matcher = CommonSubstring(arena)
            with patch('fastunknot.compressed_lcs.MatchTable',
                       side_effect=AssertionError('sparse endpoints need no table')):
                aps = matcher.overlaps(u, v)
            values = [p+i*d for p, d, n in aps for i in range(n)]
            expected = {k for k in range(1, min(len(x), len(y))+1) if x[-k:] == y[:k]}
            self.assertEqual(set(values), expected)
            self.assertEqual(len(values), len(expected))
            self.assertGreaterEqual(len(values), 1)
            self.assertEqual(arena.stats['lcs_sparse_hits'], 1)

    def test_exponential_blocks_reused_64_times_and_saturation(self):
        for copies in (1, 17, 64):
            arena, n = WordArena(max_work=30000), 2**500
            block = arena.concat(arena.power(arena.from_word([1, 2]), n), arena.letter(3))
            root = arena.power(block, copies)
            with patch.object(arena, 'expand', side_effect=AssertionError('must not expand')), \
                 patch('fastunknot.compressed_lcs.MatchTable',
                       side_effect=AssertionError('must not build table')):
                aps = CommonSubstring(arena).overlaps(root, root)
            self.assertEqual(sorted(p for p, d, count in aps),
                             [(2*n+1)*j for j in range(1, copies+1)])
            self.assertTrue(all(d == 0 and count == 1 for p, d, count in aps))
            self.assertEqual(arena.stats['lcs_sparse_candidates'], copies)
        arena = WordArena()
        block = arena.from_word([1, 2, 3])
        root = arena.power(block, 65)
        self.assertIsNone(CommonSubstring(arena).sparse_overlaps(root, root))

    def test_dense_fallback_absent_endpoint_and_resource_limits(self):
        rng = random.Random(3015)
        word = [1]*80+[2]*80
        rng.shuffle(word)
        arena = WordArena(max_work=10000000)
        root = parsed(arena, word, rng)
        matcher = CommonSubstring(arena)
        self.assertIsNone(matcher.sparse_overlaps(root, root))
        aps = matcher.overlaps(root, root)
        self.assertEqual({p+i*d for p, d, n in aps for i in range(n)},
                         {k for k in range(1, len(word)+1) if word[-k:] == word[:k]})
        self.assertGreater(arena.stats.get('match_cells', 0), 0)
        x = arena.concat(arena.power(arena.letter(1), 200), arena.letter(-3))
        y = arena.concat(arena.power(arena.letter(1), 200), arena.letter(3))
        with patch.object(arena, 'equal', side_effect=AssertionError('no candidate')):
            self.assertEqual(CommonSubstring(arena).sparse_overlaps(x, y), [])
        arena.left = 0
        with self.assertRaises(CompressedLimit):
            CommonSubstring(arena).sparse_overlaps(x, y)


if __name__ == '__main__':
    unittest.main()
