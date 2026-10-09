"""Independent point-expanding oracles are deliberately confined to tests."""

from collections import Counter
import copy
import itertools
import json
from pathlib import Path
import random
import sys
import time
import unittest

HERE = Path(__file__).resolve().parent

from fastunknot.interval_orbits import IntervalPairing, count_orbits
from fastunknot.weighted_orbits import (WeightRun, WeightedOrbitError,
                                      replay_weighted_orbit_profile,
                                      weighted_orbit_profile)


def literal_profile(size, pairings, runs, dimension):
    """DSU on literal points; shares no algorithmic code with weighted replay."""
    parent = list(range(size))

    def find(point):
        while parent[point] != point:
            parent[point] = parent[parent[point]]
            point = parent[point]
        return point

    for pair in pairings:
        for point in range(pair.a, pair.b + 1):
            image = pair.a + pair.d - point if pair.reverse \
                else point + pair.c - pair.a
            parent[find(point)] = find(image)
    sums = {}
    for start, stop, vector in runs:
        for point in range(start, stop):
            accumulated = sums.setdefault(find(point), [0] * dimension)
            for j, value in enumerate(vector):
                accumulated[j] += value
    grouped = Counter(tuple(vector) for vector in sums.values())
    return tuple((multiplicity, vector)
                 for vector, multiplicity in sorted(grouped.items()))


def all_pairings(size):
    return [IntervalPairing(a, a + width - 1, c, c + width - 1, reverse)
            for width in range(1, size + 1)
            for a in range(size - width + 1)
            for c in range(a, size - width + 1)
            for reverse in (False, True)]


def random_pairing(rng, size):
    width = rng.randint(1, size)
    a, c = rng.randrange(size - width + 1), rng.randrange(size - width + 1)
    return IntervalPairing(a, a + width - 1, c, c + width - 1,
                           bool(rng.randrange(2)))


def random_runs(rng, size, dimension):
    if not size:
        return []
    cuts = sorted({0, size, *(rng.randrange(size + 1)
                              for _ in range(rng.randrange(1, size + 1)))})
    return [(lo, hi, tuple(rng.randint(-11, 11) for _ in range(dimension)))
            for lo, hi in zip(cuts, cuts[1:])]


def expected_uniform_periodic(size, period, vector):
    quotient, remainder = divmod(size, period)
    result = Counter()
    if period > remainder:
        result[tuple(quotient * value for value in vector)] += period - remainder
    if remainder:
        result[tuple((quotient + 1) * value for value in vector)] += remainder
    return tuple((multiplicity, weight)
                 for weight, multiplicity in sorted(result.items()))


class WeightedTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.started = time.perf_counter()
        cls.summary = {
            "seed": 20261009,
            "exhaustive_single_systems": 0,
            "exhaustive_two_generator_systems": 0,
            "random_systems": 0,
            "compared_profiles": 0,
            "operations_observed": set(),
            "weighted_transfers": 0,
            "periodic_partial_truncations": 0,
            "max_transfer_run_increase": 0,
            "largest_universe_bit_length": 0,
        }

    @classmethod
    def tearDownClass(cls):
        cls.summary["operations_observed"] = sorted(cls.summary["operations_observed"])
        cls.summary["elapsed_seconds"] = time.perf_counter() - cls.started
        (HERE.parent / "component_profile_research" / "weighted_test_summary.json").write_text(
            json.dumps(cls.summary, indent=2) + "\n")

    def compare(self, size, pairings, runs, dimension, rule="fine_wilf"):
        result = weighted_orbit_profile(
            size, pairings, runs, dimension=dimension, periodic_rule=rule,
            record_certificate=True)
        self.assertTrue(result.complete)
        self.assertEqual(result.profiles, literal_profile(size, pairings, runs,
                                                         dimension))
        self.assertEqual(result.orbits, sum(row[0] for row in result.profiles))
        stats = result.stats
        self.assertLessEqual(stats["weight_peak_runs"],
                             stats["weight_initial_runs"]
                             + 4 * stats["weight_transfers"])
        self.summary["compared_profiles"] += 1
        self.summary["operations_observed"].update(
            event["op"] for event in result.certificate["operations"])
        self.summary["weighted_transfers"] += stats["weight_transfers"]
        self.summary["periodic_partial_truncations"] += \
            stats["weight_periodic_partial_truncations"]
        self.summary["max_transfer_run_increase"] = max(
            self.summary["max_transfer_run_increase"],
            stats["weight_max_transfer_run_increase"])
        return result

    def test_01_exhaustive_single_pairings_with_basis_weights(self):
        # Basis weights encode each complete orbit itself, so this checks
        # the whole partition rather than only a coincidental scalar sum.
        for size in range(1, 9):
            runs = [(point, point + 1,
                     tuple(int(j == point) for j in range(size)))
                    for point in range(size)]
            for pair in all_pairings(size):
                self.compare(size, [pair], runs, size)
                self.summary["exhaustive_single_systems"] += 1

    def test_02_exhaustive_two_generator_systems(self):
        for size in range(1, 5):
            runs = [(point, point + 1,
                     tuple(int(j == point) for j in range(size)))
                    for point in range(size)]
            for pairings in itertools.product(all_pairings(size), repeat=2):
                self.compare(size, pairings, runs, size)
                self.summary["exhaustive_two_generator_systems"] += 1

    def test_03_signed_random_systems_both_merger_rules(self):
        rng = random.Random(self.summary["seed"])
        for case in range(3000):
            size = rng.randint(1, 70)
            dimension = rng.randint(1, 6)
            pairings = [random_pairing(rng, size) for _ in range(rng.randrange(17))]
            runs = random_runs(rng, size, dimension)
            for rule in ("fine_wilf", "aht"):
                self.compare(size, pairings, runs, dimension, rule)
            self.summary["random_systems"] += 1

    def test_04_large_binary_universes(self):
        for bits, period in ((267, 97), (8192, (1 << 4096) + 37),
                             (65536, (1 << 32768) + 137)):
            size = (1 << bits) + 123
            vector = (1, -11, (1 << (bits // 8)) - 1)
            pair = IntervalPairing(0, size - period - 1, period, size - 1)
            result = weighted_orbit_profile(size, [pair], [(0, size, vector)])
            self.assertEqual(result.profiles,
                             expected_uniform_periodic(size, period, vector))
            self.assertEqual(result.orbits, period)
            self.assertLessEqual(result.stats["weight_peak_runs"], 4)
            self.summary["largest_universe_bit_length"] = max(
                self.summary["largest_universe_bit_length"], size.bit_length())
        size = (1 << 32768) + 1
        vector = (3, -7, 0)
        pair = IntervalPairing(0, size - 1, 0, size - 1, True)
        result = weighted_orbit_profile(size, [pair], [(0, size, vector)])
        expected = ((1, vector), ((size - 1) // 2,
                                 tuple(2 * value for value in vector)))
        self.assertEqual(result.profiles,
                         tuple(sorted(expected, key=lambda row: row[1])))
        result = weighted_orbit_profile(size, [], [(0, size, vector)])
        self.assertEqual(result.profiles, ((size, vector),))

    def test_05_invalid_trace_and_input_binding(self):
        pairings = [IntervalPairing(0, 17, 3, 20)]
        runs = [(0, 21, (1, -2))]
        certificate = count_orbits(21, pairings, record_certificate=True).certificate
        expected = replay_weighted_orbit_profile(21, pairings, runs, certificate)
        reused = weighted_orbit_profile(21, pairings, runs, certificate=certificate)
        self.assertEqual(expected.profiles, reused.profiles)
        self.assertIsNone(reused.cycles)
        for changed in (
                {**certificate, "orbit_count": certificate["orbit_count"] + 1},
                {**certificate, "size": 20}):
            with self.assertRaises(ValueError):
                replay_weighted_orbit_profile(21, pairings, runs, changed)
        changed = copy.deepcopy(certificate)
        truncate = next(event for event in changed["operations"]
                        if event["op"] == "truncate")
        truncate["new_size"] = 0
        with self.assertRaises(ValueError):
            replay_weighted_orbit_profile(21, pairings, runs, changed)
        with self.assertRaises(ValueError):
            replay_weighted_orbit_profile(21, [], runs, certificate)
        with self.assertRaises(ValueError):
            weighted_orbit_profile(21, pairings, runs, certificate=certificate,
                                   max_cycles=100)

    def test_06_weights_zero_cancellation_and_empty(self):
        self.compare(13, [], [(0, 4, (0, 0)), (4, 9, (0, 0)),
                              (9, 13, (-3, 7))], 2)
        self.compare(4, [IntervalPairing(0, 2, 1, 3)],
                     [(0, 2, (7, -3)), (2, 4, (-7, 3))], 2)
        result = weighted_orbit_profile(0, [], [], dimension=3)
        self.assertEqual(result.profiles, ())
        self.assertEqual(result.dimension, 3)
        self.assertEqual(result.orbits, 0)
        invalid = [[(1, 3, (1,))], [(0, 2, (1,)), (1, 3, (2,))],
                   [(0, 4, (1,))], [(0, 3, ())], [(0, 3, (True,))],
                   [(0, 1, (1,)), (1, 3, (1, 2))]]
        for runs in invalid:
            with self.assertRaises(ValueError):
                weighted_orbit_profile(3, [], runs)
        run = WeightRun(0, 3, (1, -2))
        self.assertEqual(weighted_orbit_profile(3, [], [run]).profiles,
                         ((3, (1, -2)),))

    def test_07_caps_and_cooperative_cancellation(self):
        pairings = [IntervalPairing(0, 98, 1, 99)]
        result = weighted_orbit_profile(100, pairings, [(0, 100, (1,))],
                                         max_cycles=0, record_certificate=True)
        self.assertFalse(result.complete)
        self.assertIsNone(result.orbits)
        self.assertIsNone(result.profiles)
        self.assertIsNone(result.certificate)

        class Cancelled(RuntimeError):
            pass

        def cancel():
            raise Cancelled("requested")

        with self.assertRaises(Cancelled):
            weighted_orbit_profile(100, pairings, [(0, 100, (1,))], check=cancel)
        certificate = count_orbits(100, pairings, record_certificate=True).certificate
        with self.assertRaises(Cancelled):
            replay_weighted_orbit_profile(100, pairings, [(0, 100, (1,))],
                                           certificate, check=cancel)

        def value_error_cancel():
            raise ValueError("callback cancellation")

        for call in (
                lambda: weighted_orbit_profile(100, pairings, [(0, 100, (1,))],
                                               check=value_error_cancel),
                lambda: replay_weighted_orbit_profile(
                    100, pairings, [(0, 100, (1,))], certificate,
                    check=value_error_cancel)):
            try:
                call()
            except WeightedOrbitError as error:
                self.fail(f"Callback exception was converted to input error: {error}")
            except ValueError as error:
                self.assertEqual(str(error), "callback cancellation")
            else:
                self.fail("The callback's ValueError did not propagate")

    def test_08_hexadecimal_trace(self):
        pairings = [IntervalPairing(0, 17, 3, 20)]
        certificate = count_orbits(21, pairings, record_certificate=True).certificate

        def hexadecimal(value):
            if type(value) is int:
                return hex(value)
            if isinstance(value, dict):
                return {key: hexadecimal(item) for key, item in value.items()}
            if isinstance(value, list):
                return [hexadecimal(item) for item in value]
            return value

        result = replay_weighted_orbit_profile(
            21, pairings, [(0, 21, (1, -2))], hexadecimal(certificate))
        self.assertEqual(result.profiles, ((3, (7, -14)),))

    def test_99_structural_coverage(self):
        self.assertEqual(self.summary["operations_observed"],
                         {"delete", "trim", "merge", "transmit", "truncate", "contract"})
        self.assertGreater(self.summary["periodic_partial_truncations"], 0)
        self.assertLessEqual(self.summary["max_transfer_run_increase"], 4)


if __name__ == "__main__":
    unittest.main(verbosity=2)
