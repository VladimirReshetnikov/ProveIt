"""Independent finite-graph and symbolic-scale checks for interval orbits."""

from itertools import combinations_with_replacement
from math import gcd
import random
import unittest

from fastunknot.interval_orbits import (
    IntervalPairing, SignedPairing, count_orbits, periodic_merge,
    same_orbit, signed_cover, signed_orbit_counts,
)


def explicit_components(n, pairings):
    """Point-by-point union-find: independent of all compressed reductions."""
    parents = list(range(n))

    def find(x):
        while parents[x] != x:
            parents[x] = parents[parents[x]]
            x = parents[x]
        return x

    for p in pairings:
        for x in range(p.a, p.b + 1):
            y = p.a + p.d - x if p.reverse else x + p.c - p.a
            parents[find(x)] = find(y)
    return tuple(find(x) for x in range(n))


def explicit_signed_counts(n, pairings):
    """BFS orientation propagation, without constructing a double cover."""
    adjacency = [[] for _ in range(n)]
    for signed in pairings:
        p, bit = signed.pairing, signed.parity
        for x in range(p.a, p.b + 1):
            y = p.a + p.d - x if p.reverse else x + p.c - p.a
            adjacency[x].append((y, bit))
            adjacency[y].append((x, bit))
    labels = {}
    consistent = inconsistent = 0
    for x in range(n):
        if x in labels:
            continue
        labels[x] = 0
        stack, okay = [x], True
        while stack:
            v = stack.pop()
            for w, bit in adjacency[v]:
                wanted = labels[v] ^ bit
                if w in labels:
                    okay &= labels[w] == wanted
                else:
                    labels[w] = wanted
                    stack.append(w)
        consistent += int(okay)
        inconsistent += int(not okay)
    return consistent, inconsistent


def all_pairings(n):
    return sorted({IntervalPairing(a, a + w - 1, c, c + w - 1, reverse)
                   for w in range(1, n + 1)
                   for a in range(n - w + 1)
                   for c in range(n - w + 1)
                   for reverse in (False, True)},
                  key=lambda p: (p.a, p.b, p.c, p.d, p.reverse))


def random_pairings(rng, n, k):
    result = []
    for _ in range(k):
        width = rng.randrange(1, n + 1)
        a = rng.randrange(n - width + 1)
        c = rng.randrange(n - width + 1)
        result.append(IntervalPairing(a, a + width - 1, c, c + width - 1,
                                      bool(rng.getrandbits(1))))
    return result


class IntervalOrbitTests(unittest.TestCase):
    def assert_counts(self, n, pairings):
        expected = len(set(explicit_components(n, pairings)))
        for rule in ('aht', 'fine_wilf'):
            actual = count_orbits(n, pairings, periodic_rule=rule, max_cycles=1000)
            self.assertTrue(actual.complete, (n, pairings, rule, actual))
            self.assertEqual(actual.orbits, expected, (n, pairings, rule))

    def test_exhaustive_small_pairs(self):
        systems = 0
        for n in range(1, 7):
            self.assert_counts(n, ())
            for pairings in combinations_with_replacement(all_pairings(n), 2):
                self.assert_counts(n, pairings)
                systems += 1
        self.assertEqual(systems, 9882)

    def test_exhaustive_small_triples(self):
        for n in range(1, 4):
            for pairings in combinations_with_replacement(all_pairings(n), 3):
                self.assert_counts(n, pairings)

    def test_seeded_random_systems(self):
        rng = random.Random(26100813)
        for _ in range(2000):
            n = rng.randrange(1, 91)
            pairs = random_pairings(rng, n, rng.randrange(0, 25))
            self.assert_counts(n, pairs)

    def test_periodic_merge_threshold_is_exact(self):
        for p in range(1, 13):
            for q in range(1, 13):
                d = gcd(p, q)
                threshold = p + q - d
                for overlap in {max(0, threshold - 2), threshold - 1,
                                threshold, threshold + 1}:
                    first = IntervalPairing(0, p + overlap - 1,
                                            p, 2 * p + overlap - 1)
                    second = IntervalPairing(2 * p, 2 * p + overlap + q - 1,
                                             2 * p + q,
                                             2 * p + overlap + 2 * q - 1)
                    n = second.d + 1
                    expected = len(set(explicit_components(n, [first, second])))
                    merged = periodic_merge(first, second)
                    if overlap >= threshold:
                        self.assertIsNotNone(merged)
                        self.assertEqual(expected, d)
                        self.assertLessEqual(merged.width, first.width + second.width)
                        self.assertEqual(expected,
                                         len(set(explicit_components(n, [merged]))))
                    else:
                        self.assertIsNone(merged)
                        self.assertGreater(expected, d)

    def test_sharp_rule_enables_previously_unavailable_merge(self):
        first = IntervalPairing(0, 3, 2, 5)
        second = IntervalPairing(2, 4, 5, 7)
        self.assertIsNone(periodic_merge(first, second, periodic_rule='aht'))
        self.assertEqual(periodic_merge(first, second), IntervalPairing(0, 6, 1, 7))
        self.assertEqual(count_orbits(8, [first, second]).orbits, 1)
        wrong = IntervalPairing(3, 5, 6, 8)
        self.assertIsNone(periodic_merge(first, wrong))
        self.assertEqual(count_orbits(9, [first, wrong]).orbits, 2)

    def test_huge_encoded_counts(self):
        n = 1 << 10000
        pairs = [IntervalPairing(0, n - 38, 37, n - 1),
                 IntervalPairing(0, n - 102, 101, n - 1)]
        self.assertEqual(count_orbits(n, pairs).orbits, 1)
        self.assertEqual(count_orbits(n, [pairs[0]]).orbits, 37)
        self.assertEqual(count_orbits(n, [IntervalPairing(0, n - 1, 0, n - 1,
                                                         True)]).orbits, n // 2)
        self.assertEqual(count_orbits(n + 1,
                                     [IntervalPairing(0, n, 0, n, True)]).orbits,
                         n // 2 + 1)
        self.assertEqual(count_orbits(n, [IntervalPairing(0, 0, n - 1, n - 1)]).orbits,
                         n - 1)

    def test_scaled_random_systems_with_independent_expected_counts(self):
        rng = random.Random(26100814)
        for bits in (16, 256, 4096):
            for _ in range(25):
                n = rng.randrange(2, 31)
                base = random_pairings(rng, n, rng.randrange(1, 15))
                signed = [SignedPairing(p, int(p.reverse)) for p in base]
                a, b = explicit_signed_counts(n, signed)
                scale = (1 << bits) + rng.randrange(2)
                scaled = [IntervalPairing(p.a * scale, (p.b + 1) * scale - 1,
                                           p.c * scale, (p.d + 1) * scale - 1,
                                           p.reverse) for p in base]
                expected = a * scale + b * ((scale + 1) // 2)
                for rule in ('aht', 'fine_wilf'):
                    actual = count_orbits(n * scale, scaled, periodic_rule=rule)
                    self.assertEqual(actual.orbits, expected)

    def test_signed_cover_against_independent_parity_propagation(self):
        rng = random.Random(26100815)
        for _ in range(700):
            n = rng.randrange(1, 71)
            signed = [SignedPairing(p, rng.randrange(2))
                      for p in random_pairings(rng, n, rng.randrange(0, 17))]
            expected = explicit_signed_counts(n, signed)
            actual = signed_orbit_counts(n, signed)
            self.assertTrue(actual.complete)
            self.assertEqual((actual.consistent_components,
                              actual.inconsistent_components), expected)
            self.assertEqual(actual.orbits, sum(expected))
        # The same order-reversing generator can carry either orientation bit.
        p = IntervalPairing(0, 2, 0, 2, True)
        self.assertEqual(signed_orbit_counts(3, [SignedPairing(p, 0)]).
                         inconsistent_components, 0)
        self.assertEqual(signed_orbit_counts(3, [SignedPairing(p, 1)]).
                         inconsistent_components, 1)

    def test_orbit_membership(self):
        rng = random.Random(26100816)
        for _ in range(100):
            n = rng.randrange(2, 35)
            pairs = random_pairings(rng, n, rng.randrange(0, 10))
            components = explicit_components(n, pairs)
            for _ in range(8):
                x, y = rng.randrange(n), rng.randrange(n)
                self.assertEqual(same_orbit(n, pairs, x, y),
                                 components[x] == components[y])

    def test_budget_is_inconclusive_and_shared(self):
        pair = IntervalPairing(0, 98, 1, 99)
        complete = count_orbits(100, [pair])
        stopped = count_orbits(100, [pair], max_cycles=complete.cycles - 1)
        self.assertFalse(stopped.complete)
        self.assertIsNone(stopped.orbits)
        self.assertEqual(stopped.cycles, complete.cycles - 1)
        self.assertEqual(count_orbits(100, [pair], max_cycles=complete.cycles).orbits, 1)
        signed = [SignedPairing(pair, 0)]
        full = signed_orbit_counts(100, signed)
        limited = signed_orbit_counts(100, signed, max_cycles=full.cycles - 1)
        self.assertFalse(limited.complete)
        self.assertIsNone(limited.orbits)
        self.assertIsNone(limited.consistent_components)
        self.assertEqual(limited.cycles, full.cycles - 1)
        self.assertIsNone(same_orbit(100, [pair], 0, 99, max_cycles=0))

    def test_cancellation_propagates_even_for_empty_input(self):
        class Cancelled(Exception):
            pass

        def cancel():
            raise Cancelled

        for n, pairs in ((0, []), (10, [IntervalPairing(0, 8, 1, 9)])):
            with self.assertRaises(Cancelled):
                count_orbits(n, pairs, check=cancel)
        calls = 0

        def later():
            nonlocal calls
            calls += 1
            if calls == 4:
                raise Cancelled

        with self.assertRaises(Cancelled):
            count_orbits(20, [IntervalPairing(0, 15, 2, 17),
                              IntervalPairing(1, 15, 5, 19)], check=later)
        self.assertEqual(calls, 4)

    def test_validation_and_input_immutability(self):
        bad = [(0, -1, 0, -1), (1, 0, 2, 1), (0, 1, 3, 5), (False, 1, 2, 3)]
        for args in bad:
            with self.assertRaises(ValueError):
                IntervalPairing(*args)
        with self.assertRaises(ValueError):
            IntervalPairing(0, 1, 2, 3, 1)
        pair = IntervalPairing(5, 8, 0, 3, True)
        self.assertEqual(pair, IntervalPairing(0, 3, 5, 8, True))
        original = [pair]
        count_orbits(9, original)
        self.assertEqual(original, [pair])
        for n, pairs, kwargs in ((8, [pair], {}), (-1, [], {}),
                                 (True, [], {}), (9, [pair], {'max_cycles': -1}),
                                 (9, [pair], {'periodic_rule': 'unchecked'})):
            with self.assertRaises(ValueError):
                count_orbits(n, pairs, **kwargs)
        self.assertEqual(count_orbits(0, [], max_cycles=0).orbits, 0)
        self.assertEqual(signed_cover(0, []), [])
        with self.assertRaises(ValueError):
            SignedPairing(pair, True)


if __name__ == '__main__':
    unittest.main()
