"""Adaptive exact prefixes, proved-prefix reuse and cancellation boundaries."""
import random
import unittest
from unittest.mock import patch

from fastunknot.compressed_words import WordArena, CompressedLimit
from fastunknot.scan import ScanLimit


class CompressedPrefixTests(unittest.TestCase):
    def test_shared_huge_prefix_and_caps_without_equality_queries(self):
        arena, n = WordArena(), 2**500
        prefix = arena.power(arena.from_word([1, 2]), n)
        length = 2*n
        a, b = arena.concat(prefix, arena.letter(3)), arena.concat(prefix, arena.letter(4))
        with patch.object(arena, 'expand', side_effect=AssertionError), \
             patch.object(arena, 'equal', side_effect=AssertionError('direct prefix should resolve')):
            for cap in (0, 1, length-1, length, length+1, length+100):
                self.assertEqual(arena.lcp(a, b, cap), min(cap, length))
            self.assertEqual(arena.lcp(prefix, a), length)
            self.assertEqual(arena.lcp(a, prefix), length)
            self.assertEqual(arena.lcp(a, a, 7), 7)
            self.assertEqual(arena.lcp(0, a), 0)
        self.assertEqual(arena.stats['lcp_probe_fallbacks'], 0)
        self.assertLess(arena.stats['lcp_probe_steps'], 40)

    def test_fallback_never_rechecks_the_proved_prefix(self):
        arena, n = WordArena(), 2**70
        prefix = arena.power(arena.letter(1), n)
        a = arena.concat(prefix, arena.concat(arena.power(arena.from_word([2, 3]), n), arena.letter(2)))
        b = arena.concat(prefix, arena.concat(arena.letter(2), arena.power(arena.from_word([3, 2]), n)))
        with patch.object(arena, 'slice', wraps=arena.slice) as slices, \
             patch.object(arena, 'expand', side_effect=AssertionError):
            self.assertEqual(arena.lcp(a, b), 3*n+1)
        self.assertEqual(arena.stats['lcp_probe_fallbacks'], 1)
        self.assertEqual(arena.stats['lcp_probe_steps'], 64)
        self.assertTrue(slices.call_args_list)
        self.assertTrue(all(call.args[1] >= n for call in slices.call_args_list))
        # Preserve endpoints while introducing the first mismatch far beyond
        # the shared prefix, so fallback must return an interior position.
        mismatch = 2*n
        bad = arena.concat(arena.concat(arena.slice(b, 0, mismatch), arena.letter(4)),
                           arena.slice(b, mismatch+1, arena.lengths[b]))
        self.assertEqual(arena.lcp(a, bad), mismatch)
        self.assertEqual(arena.lcp(a, bad, mismatch-1), mismatch-1)

    def test_random_prefixes_caps_and_interruption(self):
        rng = random.Random(2691)
        for steps in (0, 1, 7, 64):
            for _ in range(200):
                arena = WordArena(prefix_probe_steps=steps)
                common = [rng.choice([-2, -1, 1, 2]) for _ in range(rng.randrange(80))]
                left = common+[rng.choice([-2, -1, 1, 2]) for _ in range(rng.randrange(30))]
                right = common+[rng.choice([-2, -1, 1, 2]) for _ in range(rng.randrange(30))]
                # Different parse boundaries prevent identity from deciding all cases.
                a = arena.from_word(left)
                split = rng.randrange(len(right)+1)
                b = arena.concat(arena.from_word(right[:split]), arena.from_word(right[split:]))
                expected = 0
                while expected < min(len(left), len(right)) and left[expected] == right[expected]:
                    expected += 1
                for cap in (0, rng.randrange(max(len(left), len(right))+2), expected+1):
                    self.assertEqual(arena.lcp(a, b, cap), min(expected, cap))
                self.assertEqual(arena.lcp(a, b), expected)
        for invalid in (True, -1, 0.5):
            with self.assertRaises(ValueError):
                WordArena(prefix_probe_steps=invalid)
            with self.assertRaises(ValueError):
                WordArena().lcp(0, 0, invalid)
        arena = WordArena()
        prefix = arena.power(arena.letter(1), 2**100)
        a, b = arena.concat(prefix, arena.letter(2)), arena.concat(prefix, arena.letter(3))
        arena.left = 2
        with self.assertRaises(CompressedLimit):
            arena.lcp(a, b)
        arena.left = 1000000
        def cancel():
            raise ScanLimit('global prefix interruption')
        arena.check = cancel
        with self.assertRaises(ScanLimit):
            arena.lcp(a, b)
        arena.check = lambda: None
        self.assertEqual(arena.lcp(a, b), 2**100)


if __name__ == '__main__':
    unittest.main()
