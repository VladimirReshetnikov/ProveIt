"""Literal and structural oracles for arithmetic endpoint overlap certificates."""
import itertools
import random
import unittest
from unittest.mock import patch

from fastunknot.compressed_endpoint import _rank_clip, endpoint_overlaps, occurrence_summary
from fastunknot.compressed_lcs import CommonSubstring
from fastunknot.compressed_words import CompressedLimit, WordArena
from test_compressed_lcs import parsed


def values(aps):
    result = [start+i*step for start, step, count in aps for i in range(count)]
    if len(result) != len(set(result)):
        raise AssertionError('overlap APs must be disjoint')
    return set(result)


def literal_overlaps(x, y):
    return {k for k in range(1, min(len(x), len(y))+1) if x[-k:] == y[:k]}


class EndpointOverlapTests(unittest.TestCase):
    def test_all_short_signed_occurrence_summaries(self):
        words = [word for size in range(7) for word in itertools.product((-1, 1), repeat=size)]
        patterns = [word for size in range(1, 4) for word in itertools.product((-1, 1), repeat=size)]
        for word in words:
            arena = WordArena()
            root = arena.from_word(word)
            for pattern in patterns:
                positions = [i for i in range(len(word)-len(pattern)+1)
                             if word[i:i+len(pattern)] == pattern]
                gaps = [y-x for x, y in zip(positions, positions[1:])]
                expected = ((len(positions), positions[0], positions[-1],
                             min(gaps, default=0), max(gaps, default=0))
                            if positions else (0, 0, 0, 0, 0))
                self.assertEqual(occurrence_summary(arena, root, pattern), expected)

    def test_exhaustive_signed_overlaps_and_complete_fallback(self):
        words = [word for size in range(5) for word in itertools.product((-1, 1), repeat=size)]
        rejected = accepted = 0
        for x, y in itertools.product(words, repeat=2):
            for anchors in ((1,), (2,), (1, 2, 4)):
                arena = WordArena(max_work=500000)
                u, v = arena.from_word(x), arena.from_word(y)
                answer = endpoint_overlaps(arena, u, v, anchor_sizes=anchors)
                if answer is None:
                    rejected += 1
                    answer = CommonSubstring(arena).overlaps(u, v)
                else:
                    accepted += 1
                self.assertEqual(values(answer), literal_overlaps(x, y))
        self.assertGreater(accepted, 0)
        self.assertGreater(rejected, 0)

    def test_random_parses_unequal_lengths_and_signed_qgrams(self):
        rng = random.Random(202610081)
        counts = dict(resolved=0, fallback=0)
        for trial in range(360):
            x = [rng.choice((-2, -1, 1, 2)) for _ in range(rng.randrange(1, 91))]
            y = [rng.choice((-2, -1, 1, 2)) for _ in range(rng.randrange(1, 91))]
            if trial % 3 == 0:
                k = rng.randrange(1, min(len(x), len(y))+1)
                y[:k] = x[-k:]
            arena = WordArena(max_work=2000000)
            u, v = parsed(arena, x, rng), parsed(arena, y, rng)
            answer = endpoint_overlaps(arena, u, v)
            counts['fallback' if answer is None else 'resolved'] += 1
            if answer is None:
                answer = CommonSubstring(arena).overlaps(u, v)
            self.assertEqual(values(answer), literal_overlaps(x, y))
        self.assertGreater(counts['resolved'], 300)

    def test_nonperiodic_opposite_word_and_both_directions(self):
        cases = [
            ([4, 4, 4]+[1, 2, 3]*3, [1, 2, 3]*4, {3, 6, 9}, 'suffix_anchor'),
            ([4]*11+[3], [1, 2, 3]*4, set(), 'suffix_anchor'),
            ([1, 2, 3]*3, [1, 2, 3]*2+[1, 3, 3], {3, 6}, 'prefix_anchor'),
            ([8, 8, 3, 1, 2, 3, 1, 2, 3], [3, 1, 2, 3, 1, 2, 3, 9, 9],
             {1, 4, 7}, 'suffix_anchor'),
        ]
        for x, y, expected, direction in cases:
            arena = WordArena()
            u, v = arena.from_word(x), arena.from_word(y)
            answer = endpoint_overlaps(arena, u, v, anchor_sizes=(1,))
            self.assertEqual(values(answer), expected)
            self.assertEqual(arena.stats['lcs_endpoint_'+direction+'_hits'], 1)

    def test_exact_period_rejection_and_singleton_zero_cases(self):
        arena = WordArena()
        root = arena.from_word([1, 2, 3, 2, 1, 3])
        self.assertIsNone(endpoint_overlaps(arena, root, root, anchor_sizes=(1,)))
        self.assertEqual(arena.stats['lcs_endpoint_period_rejects'], 2)
        for x, y in (([1, 2, -3], [1, 2, -3]), ([9, 2, -3], [1, 2, -3]),
                     ([1, 2, 3], [1, 2, -3]), ([], [1])):
            arena = WordArena()
            u, v = arena.from_word(x), arena.from_word(y)
            answer = endpoint_overlaps(arena, u, v, anchor_sizes=(1,))
            self.assertEqual(values(answer), literal_overlaps(x, y))

    def test_eight_letter_anchor_and_deep_occurrence_grammar(self):
        block = [1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 2, 1, 1,
                 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 1]
        arena = WordArena(max_work=1000000)
        root = arena.power(arena.from_word(block), 65)
        self.assertIsNone(endpoint_overlaps(arena, root, root, anchor_sizes=(1, 2, 4)))
        answer = endpoint_overlaps(arena, root, root, anchor_sizes=(8,))
        self.assertEqual(values(answer), literal_overlaps(block*65, block*65))
        self.assertEqual(arena.stats['lcs_endpoint_anchor_max'], 8)
        arena, root = WordArena(max_work=1000000), 0
        one = arena.letter(-1)
        for _ in range(4000):
            root = arena.concat(root, one)
        self.assertEqual(occurrence_summary(arena, root, (-1, -1)),
                         (3999, 0, 3998, 1, 1))

    def test_arbitrary_binary_period_and_count_with_dense_letters(self):
        n, copies = 2**500, 2**500
        for family, core, tail, q in (
                ('letter', [1, 2], [3], 1),
                ('bigram', [2, 1], [1], 2),
                ('fourgram', [1, 2], [1, 1], 4)):
            arena = WordArena(max_work=200000)
            block = arena.concat(arena.power(arena.from_word(core), n), arena.from_word(tail))
            root = arena.power(block, copies)
            period = 2*n+len(tail)
            matcher = CommonSubstring(arena)
            with patch.object(arena, 'expand', side_effect=AssertionError('no expansion')), \
                 patch('fastunknot.compressed_lcs.MatchTable', side_effect=AssertionError('no table')):
                answer = matcher.overlaps(root, root)
                expected = ([(1, 0, 1)] if family == 'fourgram' else [])+[(period, period, copies)]
                self.assertEqual(answer, expected)
                summaries = arena.stats['lcs_endpoint_summary_calls']
                self.assertIs(matcher.overlaps(root, root), answer)
                self.assertEqual(arena.stats['lcs_endpoint_summary_calls'], summaries)
            self.assertEqual(arena.stats['lcs_endpoint_anchor_max'], q)
            self.assertEqual(arena.stats['lcs_endpoint_period_bits'], period.bit_length())
            self.assertEqual(arena.stats['lcs_endpoint_count_bits'], 501)

    def test_rank_cutoffs_and_allocation_bound(self):
        for count, passed in ((1, 0), (1, 1), (2, 0), (2, 1), (2, 2),
                              (65, 0), (65, 1), (65, 64), (65, 65),
                              (2**18, 0), (2**18, 1), (2**18, 17),
                              (2**18, 2**17), (2**18, 2**18-17),
                              (2**18, 2**18-1), (2**18, 2**18)):
            arena = WordArena(max_work=1000000)
            block = arena.from_word([1, 2, 3])
            y = arena.power(block, count)
            if passed:
                x = arena.concat(arena.power(arena.letter(4), 3*(count-passed)),
                                 arena.power(block, passed))
            else:
                x = arena.concat(arena.power(arena.letter(4), 3*count-1), arena.letter(3))
            heights = [0]
            for rule in arena.rules[1:]:
                heights.append(1 if rule[0] == 't' else 1+max(heights[c] for c in rule[1:]))
            height = max(heights[x], heights[y])
            answer = endpoint_overlaps(arena, x, y, anchor_sizes=(1,))
            expected = [(3, 3 if passed > 1 else 0, passed)] if passed else []
            self.assertEqual(answer, expected)
            tests = arena.stats.get('lcs_endpoint_rank_tests', 0)
            if count > 1:
                if passed == count:
                    self.assertEqual(tests, 1)
                elif not passed or count == 2:
                    self.assertEqual(tests, 2)
                elif passed == count-1:
                    self.assertEqual(tests, 3)
                self.assertLessEqual(tests, 4+2*(count-passed+1).bit_length())
                self.assertLessEqual(arena.stats['lcs_endpoint_rank_nodes'], 2*height*tests)
        # A single excluded largest candidate must not cause word-length LCP
        # bisection when both the period and candidate count have 500 bits.
        arena, n = WordArena(max_work=100000), 2**500
        block = arena.concat(arena.power(arena.from_word([1, 2]), n), arena.letter(3))
        period = arena.lengths[block]
        x = arena.concat(arena.power(arena.letter(4), period), arena.power(block, n-1))
        y = arena.power(block, n)
        self.assertEqual(CommonSubstring(arena).overlaps(x, y), [(period, period, n-1)])
        self.assertEqual(arena.stats['lcs_endpoint_rank_tests'], 3)

    def test_rank_resource_exceptions_never_return_partial_progression(self):
        arena = WordArena(max_work=100000)
        block = arena.from_word([1, 2, 3])
        x = arena.concat(arena.power(arena.letter(4), 144), arena.power(block, 17))
        y = arena.power(block, 65)
        arena.max_nodes = len(arena.rules)-1
        with self.assertRaisesRegex(CompressedLimit, 'node allowance'):
            _rank_clip(arena, x, y, (3, 3, 65))
        self.assertEqual(arena.stats['lcs_endpoint_rank_queries'], 1)
        self.assertEqual(arena.stats['lcs_endpoint_rank_nodes'], 0)
        arena.left = 1
        with self.assertRaises(CompressedLimit):
            _rank_clip(arena, x, y, (3, 3, 65))

    def test_structural_failure_preserves_fallback_and_limits_interrupt(self):
        rng = random.Random(888)
        word = [1]*80+[2]*80
        rng.shuffle(word)
        arena = WordArena(max_work=3000000)
        root = parsed(arena, word, rng)
        matcher = CommonSubstring(arena)
        with patch.object(matcher, 'endpoint_overlaps', return_value=None):
            answer = matcher.overlaps(root, root)
        self.assertEqual(values(answer), literal_overlaps(word, word))
        self.assertGreater(arena.stats.get('match_cells', 0), 0)
        arena.left = 0
        with self.assertRaises(CompressedLimit):
            endpoint_overlaps(arena, root, root)
        fresh = WordArena(max_work=100000)
        root = fresh.from_word([1, 2, 1, 2])
        fresh.left = 2
        with self.assertRaises(CompressedLimit):
            occurrence_summary(fresh, root, (1, 2))
        for invalid in ((), (0,), ('1',), (True,)):
            with self.assertRaises(ValueError):
                occurrence_summary(WordArena(), 0, invalid)
        with self.assertRaises(ValueError):
            endpoint_overlaps(WordArena(), 0, 0, anchor_sizes=(0,))


if __name__ == '__main__':
    unittest.main()
