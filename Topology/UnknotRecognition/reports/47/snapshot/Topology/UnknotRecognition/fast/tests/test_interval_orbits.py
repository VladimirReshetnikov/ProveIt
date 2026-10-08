"""Independent graph oracles and binary-size regressions for interval orbits."""

import itertools
import random
import unittest

from fastunknot.interval_orbits import (
    OrbitLimitExceeded, analyze_orbits, count_orbits,
)


def pairing(start, stop, image_start, sign=1):
    offset = image_start - start if sign == 1 else image_start + stop - 1
    return {"start": start, "stop": stop, "sign": sign, "offset": offset}


def expanded_partition(size, pairings):
    """Literal graph components; independent of all interval-rewrite formulas."""
    adjacent = [[] for _ in range(size)]
    for p in pairings:
        for x in range(p["start"], p["stop"]):
            y = p["sign"] * x + p["offset"]
            adjacent[x].append(y)
            adjacent[y].append(x)
    unseen = set(range(size))
    result = []
    while unseen:
        first = unseen.pop()
        reached = {first}
        pending = [first]
        while pending:
            for y in adjacent[pending.pop()]:
                if y in unseen:
                    unseen.remove(y)
                    reached.add(y)
                    pending.append(y)
        result.append(frozenset(reached))
    return frozenset(result)


def all_pairings(size):
    for width in range(1, size + 1):
        for left in range(size - width + 1):
            for right in range(size - width + 1):
                for sign in (-1, 1):
                    yield pairing(left, left + width, right, sign)


class IntervalOrbitTests(unittest.TestCase):
    def test_empty_and_static(self):
        self.assertEqual(count_orbits(0, []), 0)
        self.assertEqual(count_orbits(10**1000, []), 10**1000)
        self.assertEqual(count_orbits(7, [pairing(2, 2, 500)]), 7)
        self.assertEqual(count_orbits(7, [pairing(0, 7, 0)]), 7)
        self.assertEqual(count_orbits(7, [pairing(3, 4, 3, -1)]), 7)

    def test_exhaustive_single_and_two_pairings(self):
        # Every pair of partial interval isometries on universes of at most
        # four points, including overlaps, duplicate relations and fixed points.
        for size in range(1, 5):
            candidates = list(all_pairings(size))
            for first in candidates:
                self.assertEqual(count_orbits(size, [first]),
                                 len(expanded_partition(size, [first])))
            for first, second in itertools.combinations_with_replacement(candidates, 2):
                instance = [first, second]
                self.assertEqual(count_orbits(size, instance),
                                 len(expanded_partition(size, instance)),
                                 (size, instance))

    def test_seeded_arbitrary_partial_isometries(self):
        rng = random.Random(2026100817)
        for _ in range(4000):
            size = rng.randrange(1, 121)
            instance = []
            for _ in range(rng.randrange(21)):
                width = rng.randrange(size + 1)
                left = rng.randrange(size - width + 1)
                right = rng.randrange(size - width + 1)
                instance.append(pairing(left, left + width, right, rng.choice((-1, 1))))
            self.assertEqual(count_orbits(size, instance),
                             len(expanded_partition(size, instance)),
                             (size, instance))

    def test_inverse_order_and_relabeling(self):
        rng = random.Random(712042)
        for _ in range(300):
            size = rng.randrange(2, 70)
            instance = []
            for _ in range(rng.randrange(1, 12)):
                width = rng.randrange(1, size + 1)
                left = rng.randrange(size - width + 1)
                right = rng.randrange(size - width + 1)
                instance.append(pairing(left, left + width, right, rng.choice((-1, 1))))
            expected = len(expanded_partition(size, instance))
            inverse, reflected = [], []
            for p in reversed(instance):
                images = [p["sign"] * x + p["offset"]
                          for x in (p["start"], p["stop"] - 1)]
                inverse.append({"start": min(images), "stop": max(images) + 1,
                                "sign": p["sign"],
                                "offset": -p["sign"] * p["offset"]})
                reflected.append({"start": size - p["stop"],
                                  "stop": size - p["start"], "sign": p["sign"],
                                  "offset": (size - 1) * (1 - p["sign"]) - p["offset"]})
            self.assertEqual(count_orbits(size, inverse), expected)
            self.assertEqual(count_orbits(size, reflected), expected)

    def test_reflection_fixed_point_and_partial_overlap(self):
        for size in range(1, 50):
            self.assertEqual(count_orbits(size, [pairing(0, size, 0, -1)]),
                             (size + 1) // 2)
        # Reflection of [0,6] to [4,10] has the same involution orbits
        # on its union as the complete reflection of [0,10].
        instance = [pairing(0, 7, 4, -1)]
        self.assertEqual(count_orbits(11, instance), 6)

    def test_periodic_merger_uses_union_hull(self):
        # The second periodic support protrudes beyond the first. Keeping
        # only the first support would incorrectly leave two static points.
        instance = [pairing(0, 4, 2), pairing(3, 7, 4)]
        result = analyze_orbits(8, instance, record_trace=True)
        self.assertEqual(result["orbit_count"], 1)
        self.assertEqual(result["stats"]["mergers"], 1)
        self.assertIn("merge", {op["op"] for op in result["certificate"]["operations"]})

    def test_adjacent_periodic_pairing(self):
        # AHT permits t=width: adjacent source and image count as periodic.
        # The first support has width 12; the second has period 1.
        instance = [pairing(0, 6, 6), pairing(2, 11, 3)]
        result = analyze_orbits(12, instance)
        self.assertEqual(result["orbit_count"], 1)
        self.assertEqual(result["stats"]["mergers"], 1)

    def test_binary_width_not_enumerated(self):
        width = (1 << 12000) + 1
        periodic = [pairing(0, width - 6, 6), pairing(0, width - 15, 15)]
        result = analyze_orbits(width, periodic)
        self.assertEqual(result["orbit_count"], 3)
        self.assertLess(result["stats"]["cycles"], 5)
        reflected = [pairing(0, width, 0, -1)]
        result = analyze_orbits(width, reflected)
        self.assertEqual(result["orbit_count"], (width + 1) // 2)
        self.assertLess(result["stats"]["cycles"], 5)

    def test_binary_gaps_and_long_transmission(self):
        n = 1 << 6000
        result = analyze_orbits(5 * n, [pairing(n, 2 * n, 3 * n)])
        self.assertEqual(result["orbit_count"], 4 * n)
        self.assertLess(result["stats"]["cycles"], 5)
        # The singleton is translated through exponentially many iterates,
        # recorded as one integer division and one trace operation.
        result = analyze_orbits(n, [pairing(0, n - 1, 1),
                                   pairing(0, 1, n - 1)], record_trace=True)
        self.assertEqual(result["orbit_count"], 1)
        self.assertLess(result["stats"]["cycles"], 8)
        transmissions = [op for op in result["certificate"]["operations"]
                         if op["op"] == "transmit"]
        self.assertEqual(transmissions[0]["target_power"], n - 1)

    def test_hex_transport_and_input_immutability(self):
        raw = {"start": "0x0", "stop": "0x100", "sign": "+0x1", "offset": "0x3"}
        original = dict(raw)
        self.assertEqual(count_orbits("0x103", [raw]), 3)
        self.assertEqual(raw, original)

    def test_invalid_inputs(self):
        bad = [(-1, []), (True, []), (5, {}), (5, [{"start": 0}]),
               (5, [pairing(-1, 1, 2)]), (5, [pairing(0, 7, 0)]),
               (5, [pairing(0, 1, 6)]),
               (5, [{"start": 0, "stop": 1, "sign": 0, "offset": 0}]),
               (5, [{"start": 0, "stop": 1, "sign": True, "offset": 0}])]
        for size, instance in bad:
            with self.assertRaises(ValueError):
                count_orbits(size, instance)
        with self.assertRaises(ValueError):
            analyze_orbits(3, [], record_trace=1)

    def test_resource_interruption_never_returns_a_count(self):
        with self.assertRaises(OrbitLimitExceeded):
            count_orbits(100, [pairing(0, 99, 1)], max_cycles=1)
        with self.assertRaises(ValueError):
            count_orbits(0, [], max_cycles=-1)
        self.assertEqual(count_orbits(0, [], max_cycles=0), 0)
        calls = 0

        class Stopped(Exception):
            pass

        def check():
            nonlocal calls
            calls += 1
            if calls == 4:
                raise Stopped

        with self.assertRaises(Stopped):
            count_orbits(20, [pairing(0, 15, 5), pairing(4, 14, 0, -1)], check=check)


if __name__ == "__main__":
    unittest.main()
