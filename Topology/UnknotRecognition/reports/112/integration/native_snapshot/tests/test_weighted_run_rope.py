"""Local lazy weight transport against flat replay and literal finite maps."""

from collections import defaultdict
from copy import deepcopy
import random
import unittest

from fastunknot.interval_orbits import IntervalPairing
from fastunknot.weighted_orbits import weighted_orbit_histogram
from fastunknot.weighted_orbit_verify import (
    _canonical_pairings, _initial_weights, _replay, _replay_local,
    verify_weighted_orbit_certificate, verify_weighted_orbit_certificate_reference)
from fastunknot.weighted_run_rope import (
    LocalTransport, _add_tree, _concat, _segments, _split, from_runs, to_runs)


def runs_of(values):
    runs = []
    for point, value in enumerate(values):
        if runs and runs[-1][2] == value:
            runs[-1] = (runs[-1][0], point + 1, value)
        else:
            runs.append((point, point + 1, value))
    return runs


def expand(root):
    return [value for span, value in _segments(root) for _ in range(span)]


def check_structure(test, root):
    if root is None:
        return
    if root.left is None:
        test.assertIsNone(root.right)
        test.assertIsNone(root.lazy)
        test.assertEqual(root.height, 1)
        test.assertEqual(root.count, 1)
        test.assertEqual(root.first_span, root.span)
        test.assertEqual(root.last_span, root.span)
        test.assertEqual(root.first_value, root.value)
        test.assertEqual(root.last_value, root.value)
        return
    check_structure(test, root.left)
    check_structure(test, root.right)
    test.assertLessEqual(abs(root.left.height - root.right.height), 1)
    test.assertEqual(root.height, 1 + max(root.left.height, root.right.height))
    test.assertEqual(root.span, root.left.span + root.right.span)
    test.assertEqual(root.count, root.left.count + root.right.count)
    test.assertEqual(root.first_span, root.left.first_span)
    test.assertEqual(root.last_span, root.right.last_span)
    left, right = root.left.first_value, root.right.last_value
    if root.lazy is not None:
        left = tuple(a + b for a, b in zip(left, root.lazy))
        right = tuple(a + b for a, b in zip(right, root.lazy))
    test.assertEqual(root.first_value, left)
    test.assertEqual(root.last_value, right)
    # Adjacent subtrees can carry different inherited tags, so compare their
    # effective boundary values before the current node's common addition.
    test.assertNotEqual(root.left.last_value, root.right.first_value)


class WeightedRunRopeTests(unittest.TestCase):
    def test_random_lazy_updates_and_splits_preserve_avl_and_canonical_runs(self):
        rng = random.Random(261012181)
        values = [(rng.randrange(-4, 5), rng.randrange(-3, 4)) for _ in range(150)]
        root = from_runs(runs_of(values))
        for _ in range(500):
            lo, hi = sorted(rng.sample(range(len(values) + 1), 2))
            delta = (rng.randrange(-3, 4), rng.randrange(-3, 4))
            before, rest = _split(root, lo)
            middle, after = _split(rest, hi - lo)
            root = _concat(_concat(before, _add_tree(middle, delta)), after)
            values[lo:hi] = [tuple(a + b for a, b in zip(v, delta)) for v in values[lo:hi]]
            self.assertEqual(to_runs(root), runs_of(values))
            check_structure(self, root)

    def test_translation_and_reflection_against_literal_fibres(self):
        rng = random.Random(261012182)
        for _ in range(1000):
            size = rng.randrange(2, 90)
            values = [(rng.randrange(-4, 5), rng.randrange(-4, 5)) for _ in range(size)]
            old = runs_of(values)
            cut = rng.randrange(1, size)
            period = rng.randrange(1, cut + 1)
            local = LocalTransport()
            root = local.prepare(old, lambda: None)
            folded = local.translation(root, size, cut, period, 2, lambda: None)
            expected = list(values[:cut])
            for point in range(cut, size):
                target = cut - period + (point - cut) % period
                expected[target] = tuple(a + b for a, b in zip(expected[target], values[point]))
            self.assertEqual(to_runs(folded), runs_of(expected))
            self.assertLessEqual(folded.count, len(old) + 2)
            check_structure(self, folded)
            if size - cut <= cut:
                left = rng.randrange(cut - (size - cut) + 1)
                centre = left + size - 1
                reflected = local.reflection(root, size, cut, centre, 2, lambda: None)
                expected = list(values[:cut])
                for point in range(cut, size):
                    target = centre - point
                    expected[target] = tuple(a + b for a, b in zip(expected[target], values[point]))
                self.assertEqual(to_runs(reflected), runs_of(expected))
                self.assertLessEqual(reflected.count, len(old) + 2)
                check_structure(self, reflected)

    def test_static_deletion_preserves_order_and_cannot_increase_run_count(self):
        rng = random.Random(261012183)
        for _ in range(400):
            size = rng.randrange(1, 120)
            values = [(rng.randrange(-2, 3),) for _ in range(size)]
            deleted = [rng.randrange(2) == 1 for _ in range(size)]
            gaps = []
            for point, remove in enumerate(deleted):
                if remove:
                    if gaps and gaps[-1][1] == point - 1:
                        gaps[-1][1] = point
                    else:
                        gaps.append([point, point])
            old = runs_of(values)
            hist = defaultdict(int)
            local = LocalTransport()
            root = local.prepare(old, lambda: None)
            result, remaining = local.contract(root, size, gaps, hist, lambda: None)
            expected = [value for point, value in enumerate(values) if not deleted[point]]
            expected_hist = defaultdict(int)
            for point, value in enumerate(values):
                if deleted[point]:
                    expected_hist[value] += 1
            self.assertEqual(to_runs(result), runs_of(expected))
            self.assertEqual(remaining, len(expected))
            self.assertEqual(hist, expected_hist)
            self.assertLessEqual(0 if result is None else result.count, len(old))
            check_structure(self, result)

    def test_exponential_coordinates_and_signed_vectors(self):
        large = (1 << 8192) + 37
        runs = [(0, large, (7, -3)), (large, 3 * large + 1, (-2, 5))]
        local = LocalTransport()
        root = local.prepare(runs, lambda: None)
        folded = local.translation(root, 3 * large + 1, large, large, 2, lambda: None)
        self.assertEqual(to_runs(folded), [(0, 1, (1, 12)), (1, large, (3, 7))])
        self.assertEqual(local.metrics['source_runs'], 1)
        self.assertEqual(local.metrics['range_adds'], 2)
        check_structure(self, folded)

    def test_one_source_run_does_not_enumerate_many_receiving_runs(self):
        width, steps = 4000, 12
        values = [(i % 2,) for i in range(width)]
        source = runs_of(values) + [(width, (steps + 1) * width, (1,))]
        # The adjacent last prefix value and suffix value must coalesce.
        root = from_runs(source)
        local = LocalTransport()
        local.prepare([], lambda: None)
        calls = 0
        def poll():
            nonlocal calls
            calls += 1
        size = (steps + 1) * width
        for _ in range(steps):
            root = local.translation(root, size, size - width, size - width, 1, poll)
            size -= width
        self.assertLess(calls, 20 * steps)
        self.assertEqual(local.metrics['source_runs'], steps)
        self.assertGreater(local.metrics['target_runs'], width * steps - steps)
        self.assertEqual(to_runs(root), [(i, i + 1, (steps + i % 2,)) for i in range(width)])
        check_structure(self, root)

    def test_complete_legal_aht_trace_matches_both_public_verifiers(self):
        width, steps = 40, 8
        size = (steps + 1) * width
        pairs = [IntervalPairing(0, width - 1, j * width, (j + 1) * width - 1)
                 for j in range(1, steps + 1)]
        weights = [(i, i + 1, [i % 2]) for i in range(width)]
        weights.append((width, size, [1]))
        produced = weighted_orbit_histogram(size, pairs, weights, record_certificate=True)
        proof = produced['certificate']
        self.assertEqual(produced['histogram'], [dict(weight=[steps], orbits=width // 2),
                                                 dict(weight=[steps + 1], orbits=width // 2)])
        self.assertTrue(verify_weighted_orbit_certificate(size, pairs, weights, proof))
        self.assertTrue(verify_weighted_orbit_certificate_reference(size, pairs, weights, proof))
        dimension, runs = _initial_weights(size, weights, 1, lambda: None)
        trace = proof['orbit_proof']['operations']
        metrics = {}
        new = _replay_local(size, _canonical_pairings(size, pairs), runs, trace,
                            dimension, lambda: None, metrics)
        old = _replay(size, _canonical_pairings(size, pairs), runs, trace,
                      dimension, lambda: None)
        self.assertEqual(new, old)
        self.assertEqual(metrics['source_runs'], steps)
        self.assertEqual(metrics['folds'], steps)
        for key in ('histogram', 'weights', 'orbit_proof'):
            bad = deepcopy(proof)
            if key == 'histogram':
                bad[key][0]['orbits'] += 1
            elif key == 'weights':
                bad[key][0][2][0] += 1
            else:
                bad[key]['orbit_count'] += 1
            self.assertFalse(verify_weighted_orbit_certificate(size, pairs, weights, bad))

    def test_callback_exception_propagates_through_lazy_fold(self):
        class Stop(Exception):
            pass
        local = LocalTransport()
        root = from_runs([(0, 50, (1,)), (50, 100, (2,))])
        def stop():
            raise Stop('cancelled')
        with self.assertRaisesRegex(Stop, 'cancelled'):
            local.translation(root, 100, 50, 50, 1, stop)


if __name__ == '__main__':
    unittest.main()
