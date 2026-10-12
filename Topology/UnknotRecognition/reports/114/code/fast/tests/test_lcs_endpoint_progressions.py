"""Exact occurrence-grid and two-largest-overlap certificates."""
import itertools
import random
import unittest
from unittest.mock import patch

from fastunknot.compressed_lcs import CommonSubstring, letter_progression
from fastunknot.compressed_words import WordArena, CompressedLimit
from test_compressed_lcs import parsed, lcp


class EndpointProgressionTests(unittest.TestCase):
    def test_occurrence_grid_against_literal_positions(self):
        rng = random.Random(3016)
        words = [list(w) for n in range(8) for w in itertools.product((-1, 1), repeat=n)]
        words += [[rng.choice((-2, -1, 1, 2)) for _ in range(rng.randrange(1, 160))]
                  for _ in range(300)]
        for word in words:
            arena = WordArena()
            root = parsed(arena, word, rng)
            for letter in (-2, -1, 1, 2, 3):
                positions = [i for i, value in enumerate(word) if value == letter]
                if not positions:
                    expected = ()
                elif len(positions) == 1:
                    expected = positions[0], 0, 1
                else:
                    step = positions[1]-positions[0]
                    expected = ((positions[0], step, len(positions))
                                if all(y-x == step for x, y in zip(positions, positions[1:]))
                                else None)
                self.assertEqual(letter_progression(arena, root, letter), expected)

    def test_rotated_long_blocks_and_critical_extensions(self):
        rng = random.Random(3017)
        for _ in range(40):
            block = [rng.choice((-2, -1, 1, 2)) for _ in range(rng.randrange(2, 10))]+[3]
            shift = rng.randrange(len(block))
            left, other_right = block*70, (block[shift:]+block[:shift])*70
            arena = WordArena(max_work=5000000)
            a, d = parsed(arena, left, rng), parsed(arena, other_right, rng)
            matcher = CommonSubstring(arena)
            aps = matcher.progression_overlaps(a, d)
            self.assertIsNotNone(aps)
            values = [p+i*s for p, s, n in aps for i in range(n)]
            self.assertEqual(set(values), {k for k in range(1, len(left)+1)
                                          if left[-k:] == other_right[:k]})
            self.assertEqual(len(values), len(set(values)))
            right, other_left = block[:3]+[4], [4]+block[-3:]
            x = arena.concat(a, arena.from_word(right))
            y = arena.concat(arena.from_word(other_left), d)
            for ap in aps:
                expected = max(k+lcp(left[:-k][::-1], other_left[::-1])+
                               lcp(right, other_right[k:]) for k in
                               (ap[0]+i*ap[1] for i in range(ap[2])))
                self.assertEqual(max(matcher.extension(x, y, k)[0]
                                     for k in matcher.critical(x, y, ap)), expected)

    def test_disjoint_endpoint_grids_and_failed_large_checks(self):
        arena = WordArena(max_work=10000000)
        x = arena.power(arena.from_word([1, 2]), 100)
        y = arena.concat(arena.letter(1), x)
        with patch.object(arena, 'equal', side_effect=AssertionError('disjoint grids')):
            self.assertEqual(CommonSubstring(arena).progression_overlaps(x, y), [])
        original = [1, 2, 3]*65
        changed = original.copy()
        changed[97] = 4  # Preserve both endpoint grids while breaking period 3.
        for left, right in ((original, changed), (changed, changed)):
            arena = WordArena(max_work=10000000)
            x, y = arena.from_word(left), arena.from_word(right)
            matcher = CommonSubstring(arena)
            self.assertIsNone(matcher.progression_overlaps(x, y))
            aps = matcher.overlaps(x, y)
            self.assertEqual({p+i*d for p, d, n in aps for i in range(n)},
                             {k for k in range(1, len(left)+1) if left[-k:] == right[:k]})
            # The new continuation can clip against the unchanged periodic
            # operand; the doubly damaged pair still needs the general table.
            counter = 'lcs_anchor_hits' if left != right else 'match_cells'
            self.assertGreater(arena.stats.get(counter, 0), 0)

    def test_exponential_block_and_exponential_multiplicity(self):
        arena, n, copies = WordArena(max_work=100000), 2**500, 2**500
        block = arena.concat(arena.power(arena.from_word([1, 2]), n), arena.letter(3))
        root = arena.power(block, copies)
        with patch.object(arena, 'expand', side_effect=AssertionError('must not expand')), \
             patch('fastunknot.compressed_endpoint.endpoint_overlaps',
                   side_effect=AssertionError('old shortcut must remain first')), \
             patch('fastunknot.compressed_lcs.MatchTable',
                   side_effect=AssertionError('must not build table')):
            self.assertEqual(CommonSubstring(arena).overlaps(root, root),
                             [(2*n+1, 2*n+1, copies)])
        self.assertEqual(arena.stats['lcs_endpoint_checks'], 2)
        arena.left = 0
        with self.assertRaises(CompressedLimit):
            CommonSubstring(arena).progression_overlaps(root, root)


if __name__ == '__main__':
    unittest.main()
