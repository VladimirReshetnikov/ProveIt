"""Exact power profiles, exponential unit-step families and independent replay."""
from copy import deepcopy
from itertools import product
import unittest
import random
from unittest.mock import patch

from fastunknot import Diagram
from fastunknot.compressed_words import WordArena, CompressedLimit
from fastunknot.whitehead_power import power_profile, powered_images
from fastunknot.group_certificate import group_certificate, verify_group_certificate, GroupLimit


def normalize(word):
    stack = []
    for x in word:
        if stack and stack[-1] == -x:
            stack.pop()
        else:
            stack.append(x)
    while len(stack) > 1 and stack[0] == -stack[-1]:
        stack = stack[1:-1]
    return stack


def literal_step(words, a, subset):
    def image(x):
        if abs(x) == abs(a):
            return [x]
        return ([-a] if -x in subset else [])+[x]+([a] if x in subset else [])
    return [normalize(y for x in word for y in image(x)) for word in words]


class WhiteheadPowerTests(unittest.TestCase):
    def test_exhaustive_short_cyclic_words_all_rank_three_automorphisms(self):
        letters = (-3, -2, -1, 1, 2, 3)
        words = [[]]
        for length in range(1, 4):
            words.extend(list(w) for w in product(letters, repeat=length)
                         if all(w[i] != -w[(i+1) % length] for i in range(length)))
        for a in letters:
            others = [x for x in letters if abs(x) != abs(a)]
            for bits in product((False, True), repeat=4):
                subset = {a} | {x for x, included in zip(others, bits) if included}
                arena = WordArena(max_work=100000000)
                for word in words:
                    roots = [arena.from_word(word)]*2+[0]
                    k, delta, unit = power_profile(arena, roots, a, subset)
                    current, lengths = [word, word, []], [2*len(word)]
                    for _ in range(len(word)+2):
                        current = literal_step(current, a, subset)
                        lengths.append(sum(map(len, current)))
                    self.assertEqual(k, lengths.index(min(lengths)), (word, a, subset))
                    self.assertEqual(delta, lengths[k]-lengths[0])
                    self.assertEqual(unit, lengths[1]-lengths[0])
                    actual = [arena.cyclic_reduce(x) for x in arena.substitute(
                        roots, powered_images(arena, {1, 2, 3}, a, subset, k))]
                    self.assertEqual(sum(arena.lengths[x] for x in actual), lengths[k])

    def test_random_mixed_gap_profiles(self):
        rng = random.Random(2699)
        for _ in range(400):
            arena, words = WordArena(), []
            for _ in range(rng.randrange(1, 7)):
                words.append(normalize(rng.choice((-3, -2, -1, 1, 2, 3))
                                       for _ in range(rng.randrange(1, 50))))
            a = rng.choice((-3, -2, -1, 1, 2, 3))
            subset = {a} | {x for x in (-3, -2, -1, 1, 2, 3)
                            if abs(x) != abs(a) and rng.randrange(2)}
            roots = [arena.from_word(w) for w in words]
            k, delta, unit = power_profile(arena, roots, a, subset)
            lengths, current = [sum(map(len, words))], words
            for _ in range(max(map(len, words))+1):
                current = literal_step(current, a, subset)
                lengths.append(sum(map(len, current)))
            self.assertEqual(k, lengths.index(min(lengths)))
            self.assertEqual(delta, lengths[k]-lengths[0])
            self.assertEqual(unit, lengths[1]-lengths[0])

    def test_exponential_unit_descent_finishes_in_three_moves(self):
        from fastunknot.compressed_search import _search
        for bits in (10, 100, 500):
            arena, n = WordArena(), 2**bits
            base = arena.concat(arena.letter(1), arena.power(arena.letter(2), n))
            roots = [arena.power(base, 2), arena.power(base, 3)]
            alive, moves = {1, 2}, []
            original_expand = arena.expand
            def expand(node, *, limit):
                self.assertLessEqual(arena.lengths[node], 5)
                return original_expand(node, limit=limit)
            with patch.object(arena, 'expand', side_effect=expand):
                self.assertTrue(_search(arena, roots, alive, moves, relator_moves=True, max_letters=5))
            self.assertEqual(len(moves), 3)
            self.assertEqual(moves[0]['kind'], 'whitehead_power')
            self.assertEqual(moves[0]['exponent'], n)
            self.assertEqual(arena.stats['power_moves'], 1)
            self.assertEqual(len(alive), 1)
        # Historical allocations suppress the expansion-ratio trigger. The
        # second identical unit direction must still activate the profiler.
        arena, n = WordArena(), 2**10
        for g in range(3, 2003):
            arena.letter(g)
        base = arena.concat(arena.letter(1), arena.power(arena.letter(2), n))
        roots, moves = [arena.power(base, 2), arena.power(base, 3)], []
        self.assertTrue(_search(arena, roots, {1, 2}, moves, relator_moves=True, max_letters=5))
        self.assertEqual([m['kind'] for m in moves],
                         ['whitehead', 'whitehead_power', 'relator', 'eliminate'])
        self.assertEqual(moves[1]['exponent'], n-1)

    def test_power_certificate_independent_replayers_and_forgery(self):
        d = Diagram.from_pd(Diagram.from_braid(2, [1, -1, 1]).pd)
        original = group_certificate(d)
        def inflated(exponent):
            cert = deepcopy(original)
            cert['version'] = 3
            cert['moves'] = [dict(kind='whitehead_power', multiplier=2,
                                 subset=[1, 2], exponent=exponent),
                             dict(kind='whitehead_power', multiplier=-2,
                                 subset=[1, -2], exponent=exponent)]+cert['moves']
            return cert
        cert = inflated(7)
        for compressed in (False, True):
            # No optimization helper may be trusted in replay.
            with patch('fastunknot.whitehead_power.power_profile', side_effect=AssertionError), \
                 patch('fastunknot.whitehead_power.powered_images', side_effect=AssertionError):
                self.assertTrue(verify_group_certificate(d, cert, compressed=compressed))
            for field, value in (('exponent', True), ('exponent', 0), ('exponent', 1),
                                 ('exponent', -2), ('exponent', 2.0),
                                 ('subset', [2, -2]), ('extra', 1)):
                bad = deepcopy(cert)
                bad['moves'][0][field] = value
                self.assertFalse(verify_group_certificate(d, bad, compressed=compressed), (field, value))
            bad = deepcopy(cert)
            bad['remaining_generator'] = 999
            self.assertFalse(verify_group_certificate(d, bad, compressed=compressed))
            upgraded = deepcopy(cert)
            upgraded['version'] = 4
            self.assertTrue(verify_group_certificate(d, upgraded, compressed=compressed))
            for version in (1, 2, 5):
                bad = deepcopy(cert)
                bad['version'] = version
                self.assertFalse(verify_group_certificate(d, bad, compressed=compressed))
        huge, stats = inflated(2**100), {}
        with patch.object(WordArena, 'expand', side_effect=AssertionError):
            self.assertTrue(verify_group_certificate(d, huge, compressed=True, stats=stats))
        self.assertGreater(stats['largest_word_bits'], 100)
        with self.assertRaises(GroupLimit):
            verify_group_certificate(d, huge, max_work=100000)
        with self.assertRaises(GroupLimit):
            verify_group_certificate(d, huge, compressed=True, max_nodes=10)

    def test_shared_exponential_gap_profile_and_resource_limits(self):
        arena, n = WordArena(), 2**100
        base = arena.concat(arena.letter(1), arena.power(arena.letter(2), n))
        roots = [arena.power(base, 2), arena.power(base, 3)]
        with patch.object(arena, 'expand', side_effect=AssertionError('must not expand')):
            self.assertEqual(power_profile(arena, roots, -2, {1, -2}), (n, -5*n, -5))
        self.assertLess(len(arena.rules), 120)
        arena.left = 0
        with self.assertRaises(CompressedLimit):
            power_profile(arena, roots, -2, {1, -2})


if __name__ == '__main__':
    unittest.main()
