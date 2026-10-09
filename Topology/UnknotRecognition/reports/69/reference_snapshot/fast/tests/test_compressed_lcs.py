"""Literal oracles for compressed overlaps, periodic extensions and cyclic moves."""
import itertools
import random
import unittest
from unittest.mock import patch
from fastunknot.compressed_words import WordArena, CompressedLimit
from fastunknot.compressed_lcs import CommonSubstring
from fastunknot.compressed_overlap import whole_donor_move, cyclic_overlap_move, apply_cyclic_overlap
from fastunknot.compressed_search import _search
from fastunknot.group_certificate import _whitehead_cut


def lcp(x, y):
    return next((i for i, (a, b) in enumerate(zip(x, y)) if a != b), min(len(x), len(y)))


def literal_lcs(x, y):
    return max((lcp(x[i:], y[j:]) for i in range(len(x)) for j in range(len(y))), default=0)


def parsed(arena, word, rng):
    nodes = [arena.letter(x) for x in word]
    while len(nodes) > 1:
        i = rng.randrange(len(nodes)-1)
        nodes[i:i+2] = [arena.concat(nodes[i], nodes[i+1])]
    return nodes[0] if nodes else 0


class CompressedLCSTests(unittest.TestCase):
    def test_dyadic_overlap_progressions_exhaustive_and_random_parses(self):
        words = [list(w) for n in range(1, 6) for w in itertools.product((1, 2), repeat=n)]
        arena = WordArena(max_nodes=1000000, max_work=100000000)
        matcher = CommonSubstring(arena)
        for x in words:
            for y in words:
                aps = matcher.overlaps(arena.from_word(x), arena.from_word(y))
                values = [p+d*i for p, d, n in aps for i in range(n)]
                expected = {k for k in range(1, min(len(x), len(y))+1) if x[-k:] == y[:k]}
                self.assertEqual(set(values), expected, (x, y, aps))
                self.assertEqual(len(values), len(expected))
        rng = random.Random(2802)
        for _ in range(300):
            x, y = [[rng.choice((-2, -1, 1, 2)) for _ in range(rng.randrange(1, 70))] for _ in range(2)]
            arena = WordArena()
            aps = CommonSubstring(arena).overlaps(parsed(arena, x, rng), parsed(arena, y, rng))
            self.assertEqual({p+d*i for p, d, n in aps for i in range(n)},
                {k for k in range(1, min(len(x), len(y))+1) if x[-k:] == y[:k]})

    def test_cut_pair_lcs_witnesses_exhaustive_and_random(self):
        words = [list(w) for n in range(5) for w in itertools.product((1, 2), repeat=n)]
        rng = random.Random(2803)
        pairs = list(itertools.product(words, words))
        pairs += [tuple([rng.choice((-2, -1, 1, 2)) for _ in range(rng.randrange(1, 40))]
                        for _ in range(2)) for _ in range(300)]
        for x, y in pairs:
            arena = WordArena(max_work=10000000)
            u, v = parsed(arena, x, rng), parsed(arena, y, rng)
            expected = literal_lcs(x, y)
            for cap in (None, 0, 1, max(0, expected-1), expected+1):
                length, i, j = CommonSubstring(arena).longest(u, v, cap)
                self.assertEqual(length, expected if cap is None else min(cap, expected), (x, y, cap))
                self.assertEqual(x[i:i+length], y[j:j+length])
                self.assertLessEqual(i+length, len(x))
                self.assertLessEqual(j+length, len(y))

    def test_critical_alignments_against_every_progression_member(self):
        rng, checked = random.Random(2804), 0
        for _ in range(700):
            block = [rng.choice((1, 2)) for _ in range(rng.randrange(1, 5))]
            a = [rng.choice((1, 2, 3)) for _ in range(rng.randrange(5))]+block*rng.randrange(2, 9)
            b = block*rng.randrange(4)+[rng.choice((1, 2, 3)) for _ in range(rng.randrange(5))]
            c = [rng.choice((1, 2, 3)) for _ in range(rng.randrange(5))]+block*rng.randrange(4)
            d = block*rng.randrange(2, 9)+[rng.choice((1, 2, 3)) for _ in range(rng.randrange(5))]
            if not b or not c:
                continue
            arena = WordArena(max_work=10000000)
            u = arena.concat(arena.from_word(a), arena.from_word(b))
            v = arena.concat(arena.from_word(c), arena.from_word(d))
            matcher = CommonSubstring(arena)
            for ap in matcher.overlaps(arena.rules[u][1], arena.rules[v][2]):
                if ap[2] < 2:
                    continue
                values = [ap[0]+i*ap[1] for i in range(ap[2])]
                expected = max(k+lcp(a[:-k][::-1], c[::-1])+lcp(b, d[k:]) for k in values)
                critical = matcher.critical(u, v, ap)
                self.assertLessEqual(len(critical), 6)
                self.assertTrue(set(critical) <= set(values))
                self.assertEqual(max(matcher.extension(u, v, k)[0] for k in critical), expected)
                checked += 1
        self.assertGreater(checked, 400)

    def test_exponential_progression_and_witness_without_expansion(self):
        arena, n = WordArena(max_work=2000000), 2**500
        run = arena.power(arena.letter(1), n)
        u, v = arena.concat(run, arena.letter(2)), arena.concat(arena.letter(3), run)
        matcher = CommonSubstring(arena)
        with patch.object(arena, 'expand', side_effect=AssertionError('must not expand')):
            self.assertEqual(matcher.overlaps(run, run), [(1, 1, n)])
            self.assertLessEqual(len(matcher.critical(u, v, (1, 1, n))), 6)
            self.assertEqual(matcher.longest(u, v), (n, 0, 1))
        for cap in (True, -1, 2.0):
            with self.assertRaises(ValueError):
                matcher.longest(u, v, cap)
        arena.left = 0
        with self.assertRaises(CompressedLimit):
            matcher.longest(u, v)
        arena = WordArena(max_nodes=20)
        matcher = CommonSubstring(arena)
        matcher.cache_cells = 20
        with self.assertRaises(CompressedLimit):
            matcher.overlaps(arena.letter(1), arena.letter(1))

    def test_complete_cyclic_overlap_against_literal_oracle(self):
        rng = random.Random(2805)
        for _ in range(350):
            arena = WordArena(max_work=20000000)
            roots = [arena.cyclic_reduce(parsed(arena,
                [rng.choice((-3, -2, -1, 1, 2, 3)) for _ in range(rng.randrange(1, 17))], rng))
                for _ in range(2)]
            words = [arena.expand(x) for x in roots]
            if not all(words):
                continue
            expected = 0
            for source in (words[0], [-x for x in words[0][::-1]]):
                for i in range(len(source)):
                    for j in range(len(words[1])):
                        expected = max(expected, lcp(source[i:]+source[:i], words[1][j:]+words[1][:j]))
            move = cyclic_overlap_move(arena, roots)
            self.assertEqual(move is not None, 2*expected > min(map(len, words)))
            if move:
                target, donor = move['target'], move['donor']
                left, right = words[target], words[donor]
                if move['inverse']:
                    right = [-x for x in right[::-1]]
                i, j, k = move['target_rotation'], move['donor_rotation'], move['overlap']
                left, right = left[i:]+left[:i], right[j:]+right[:j]
                self.assertEqual(left[:k], right[:k])
                want = arena.cyclic_reduce(arena.from_word([-x for x in right[k:][::-1]]+left[k:]))
                apply_cyclic_overlap(arena, roots, move)
                self.assertTrue(arena.equal(roots[target], want))
                self.assertLess(sum(arena.lengths[x] for x in roots), sum(map(len, words)))

    def test_stalled_whole_donors_receive_partial_compressed_move(self):
        arena, n = WordArena(max_work=2000000), 2**500
        run = arena.power(arena.letter(1), n)
        roots = [arena.concat(run, arena.from_word([2, 2])),
                 arena.concat(run, arena.from_word([3, 3]))]
        self.assertEqual(_whitehead_cut(arena.summarize(roots, whitehead=True)[1], arena)[0], 0)
        self.assertIsNone(whole_donor_move(arena, roots))
        moves = []
        with patch.object(arena, 'expand', side_effect=AssertionError('must not expand')):
            self.assertFalse(_search(arena, roots, {1, 2, 3}, moves, relator_moves=True, max_letters=0))
        self.assertEqual(moves[0]['overlap'], n)
        self.assertGreaterEqual(arena.stats['compressed_lcs_moves'], 1)
        self.assertEqual(sum(arena.lengths[x] for x in roots), n+6)


if __name__ == '__main__':
    unittest.main()
