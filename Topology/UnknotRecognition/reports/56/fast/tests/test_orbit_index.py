"""Exact graph oracle and adversarial tests for compiled AHT point queries."""

import copy
from itertools import chain, combinations_with_replacement
import json
import random
import unittest

from fastunknot.interval_orbits import IntervalPairing, count_orbits
from fastunknot.orbit_index import OrbitIndex, prepare_orbit_index


def explicit_minima(size, pairings):
    parents = list(range(size))

    def root(x):
        while parents[x] != x:
            parents[x] = parents[parents[x]]
            x = parents[x]
        return x

    for pairing in pairings:
        for x in range(pairing.a, pairing.b + 1):
            y = pairing.a + pairing.d - x if pairing.reverse else x + pairing.c - pairing.a
            left, right = sorted((root(x), root(y)))
            parents[right] = left
    return [root(x) for x in range(size)]


def explicit_intervals(points):
    result = []
    for point in sorted(set(points)):
        if result and result[-1][1] == point:
            result[-1] = (result[-1][0], point + 1)
        else:
            result.append((point, point + 1))
    return tuple(result)


class OrbitIndexTests(unittest.TestCase):
    def test_exhaustive_relations_with_up_to_two_generators(self):
        systems = points = 0
        for size in range(1, 6):
            generators = [IntervalPairing(a, a + width - 1, c, c + width - 1, reverse)
                          for width in range(1, size + 1)
                          for a in range(size - width + 1)
                          for c in range(a, size - width + 1)
                          for reverse in (False, True)]
            sources = chain([()], ((p,) for p in generators),
                            combinations_with_replacement(generators, 2))
            for pairings in sources:
                expected = explicit_minima(size, pairings)
                minima = sorted(set(expected))
                for rule in ('aht', 'fine_wilf'):
                    index, _ = prepare_orbit_index(size, pairings, periodic_rule=rule)
                    self.assertEqual([index.representative(x) for x in range(size)], expected)
                    self.assertEqual(index.minimum_intervals, explicit_intervals(minima))
                    self.assertEqual([index.select_minimum(i) for i in range(index.count)], minima)
                    self.assertEqual([index.orbit_rank(x) for x in range(size)],
                                     [minima.index(x) for x in expected])
                    systems += 1
                    points += size
        print(json.dumps(dict(exhaustive_indices=systems, exhaustive_point_checks=points,
                              maximum_universe=5, maximum_generators=2)))

    def test_random_literal_graphs(self):
        rng = random.Random(202610090731)
        systems = points = comparisons = 0
        event_types = set()
        for size in range(1, 65):
            for _ in range(50):
                pairings = []
                for __ in range(rng.randrange(0, 14)):
                    width = rng.randint(1, size)
                    a = rng.randrange(size - width + 1)
                    c = rng.randrange(size - width + 1)
                    pairings.append(IntervalPairing(a, a + width - 1,
                                                    c, c + width - 1,
                                                    bool(rng.randrange(2))))
                expected = explicit_minima(size, pairings)
                previous = None
                for rule in ('aht', 'fine_wilf'):
                    index, raw = prepare_orbit_index(size, pairings, periodic_rule=rule)
                    self.assertIsNotNone(index)
                    actual = [index.representative(x) for x in range(size)]
                    self.assertEqual(actual, expected)
                    self.assertEqual(index.count, len(set(expected)))
                    minima = sorted(set(expected))
                    ranks = {minimum: rank for rank, minimum in enumerate(minima)}
                    self.assertEqual(index.minimum_intervals, explicit_intervals(expected))
                    self.assertLessEqual(len(index.minimum_intervals), index.statistics['gap_records'])
                    self.assertEqual([index.select_minimum(i) for i in range(index.count)], minima)
                    selected = [index.select(i) for i in range(index.count)]
                    self.assertEqual(set(selected), set(expected))
                    self.assertEqual(len(selected), len(set(selected)))
                    for x in range(size):
                        location = index.locate(x)
                        self.assertEqual(index.select(location.ordinal), expected[x])
                        self.assertLessEqual(location.representative, x)
                        self.assertEqual(index.orbit_rank(x), ranks[expected[x]])
                    for rank, minimum in enumerate(minima):
                        self.assertEqual(index.minimum_rank(minimum), rank)
                    for __ in range(10):
                        x, y = rng.randrange(size), rng.randrange(size)
                        self.assertEqual(index.same_orbit(x, y), expected[x] == expected[y])
                        comparisons += 1
                    if previous is not None:
                        self.assertEqual(previous, actual)
                    previous = actual
                    event_types.update(event['op'] for event in raw.certificate['operations'])
                    points += size
                    systems += 1
        self.assertEqual(event_types, {'delete', 'contract', 'trim', 'merge',
                                      'transmit', 'truncate'})
        print(json.dumps(dict(systems=systems, point_minimum_checks=points,
                              sampled_membership_checks=comparisons,
                              event_types=sorted(event_types))))

    def test_binary_scale_and_periods(self):
        width = (1 << 16000) + 7
        size = width * 3 + 19
        pairings = [IntervalPairing(5, 5 + 2 * width - 1,
                                   5 + width, 5 + 3 * width - 1)]
        index, _ = prepare_orbit_index(size, pairings)
        for x in (0, 4, 5, 6, 5 + width, 4 + 3 * width, size - 1):
            expected = x if x < 5 or x >= 5 + 3 * width else 5 + (x - 5) % width
            self.assertEqual(index.representative(x), expected)
        self.assertEqual(index.count, width + 19)
        self.assertEqual(index.minimum_intervals, ((0, 5 + width),
                                                   (5 + 3 * width, size)))
        for label in (0, 4, index.count // 2, index.count - 1):
            representative = index.select(label)
            self.assertEqual(index.representative(representative), representative)
        self.assertLess(index.statistics['point_steps'], 20)

    def test_reflection_and_singletons(self):
        size = (1 << 17000) + 1
        index, _ = prepare_orbit_index(size, [IntervalPairing(0, size - 1,
                                                             0, size - 1, True)])
        self.assertEqual(index.count, (size + 1) // 2)
        for x in (0, 1, size // 2, size // 2 + 1, size - 1):
            self.assertEqual(index.representative(x), min(x, size - 1 - x))

    def test_static_empty_and_validation(self):
        empty, _ = prepare_orbit_index(0, [])
        self.assertEqual(empty.count, 0)
        for method in (empty.select, empty.representative, empty.minimum_rank,
                       empty.orbit_rank, empty.select_minimum):
            with self.assertRaises(ValueError):
                method(0)
        size = 1 << 20000
        index, raw = prepare_orbit_index(size, [])
        for x in (0, 1, size - 1):
            self.assertEqual(index.representative(x), x)
            self.assertEqual(index.select(x), x)
            self.assertEqual(index.select_minimum(x), x)
            self.assertEqual(index.minimum_rank(x), x)
        for bad in (True, False, -1, size, 0.5, '1'):
            with self.assertRaises(ValueError):
                index.representative(bad)
            with self.assertRaises(ValueError):
                index.select(bad)
            with self.assertRaises(ValueError):
                index.select_minimum(bad)
        self.assertEqual(index.representative(hex(size - 1)), size - 1)
        snapshot = copy.deepcopy(raw.certificate)
        raw.certificate['operations'].clear()
        self.assertEqual(index.representative(size - 1), size - 1)
        with self.assertRaises(ValueError):
            OrbitIndex.from_certificate(size, [], raw.certificate)
        with self.assertRaises(ValueError):
            OrbitIndex.from_certificate(size + 1, [], snapshot)

    def test_source_binding_and_mutations(self):
        pairings = [IntervalPairing(0, 10, 5, 15), IntervalPairing(12, 14, 17, 19, True)]
        index, raw = prepare_orbit_index(23, pairings)
        mutations = []
        proof = copy.deepcopy(raw.certificate)
        proof['orbit_count'] += 1
        mutations.append(proof)
        proof = copy.deepcopy(raw.certificate)
        proof['operations'].pop()
        mutations.append(proof)
        proof = copy.deepcopy(raw.certificate)
        proof['pairings'][0][0] += 1
        mutations.append(proof)
        for event_index, event in enumerate(raw.certificate['operations']):
            if event['op'] == 'truncate':
                proof = copy.deepcopy(raw.certificate)
                proof['operations'][event_index]['new_size'] += 1
                mutations.append(proof)
                break
        for proof in mutations:
            with self.assertRaises(ValueError):
                OrbitIndex.from_certificate(23, pairings, proof)
        with self.assertRaises(ValueError):
            OrbitIndex.from_certificate(23, pairings[:-1], raw.certificate)
        self.assertEqual(index.count, len(set(explicit_minima(23, pairings))))

    def test_ordinals_are_not_canonical_but_minima_are(self):
        pairing = IntervalPairing(0, 0, 0, 0)
        common = dict(version=2, size=3, pairings=[[0, 0, 0, 0, 1]], orbit_count=3)
        first = dict(common, operations=[dict(op='delete', index=0),
                                        dict(op='contract', gaps=[[0, 2]])])
        second = dict(common, operations=[dict(op='contract', gaps=[[1, 2]]),
                                         dict(op='delete', index=0),
                                         dict(op='contract', gaps=[[0, 0]])])
        left = OrbitIndex.from_certificate(3, [pairing], first)
        right = OrbitIndex.from_certificate(3, [pairing], second)
        self.assertEqual([left.representative(x) for x in range(3)], [0, 1, 2])
        self.assertEqual([right.representative(x) for x in range(3)], [0, 1, 2])
        self.assertEqual([left.select(x) for x in range(3)], [0, 1, 2])
        self.assertEqual([right.select(x) for x in range(3)], [1, 2, 0])
        self.assertEqual(left.minimum_intervals, right.minimum_intervals)
        self.assertEqual([left.select_minimum(x) for x in range(3)], [0, 1, 2])
        self.assertEqual([right.select_minimum(x) for x in range(3)], [0, 1, 2])
        shifted, _ = prepare_orbit_index(10, [IntervalPairing(5, 5, 8, 8)])
        self.assertEqual(shifted.representative(8), 5)
        with self.assertRaises(ValueError):
            shifted.minimum_rank(8)

    def test_genuine_normal_arc_systems(self):
        from fastunknot.normal_surface_geometry import normal_arc_pairings
        from normal_orbit_research.fixtures import layered_torus, interior_vertex_torus
        systems = points = 0
        sources = []
        for tetrahedra in range(1, 11):
            raw, primitive = layered_torus(tetrahedra)
            for scale in (1, 2, 3, 7):
                vector = [[scale * entry for entry in row] for row in primitive]
                sources.append((raw, vector))
        raw, basis = interior_vertex_torus()
        for first in range(3):
            for second in range(3):
                for third in range(3):
                    vector = [[first * a + second * b + third * c
                               for a, b, c in zip(x, y, z)]
                              for x, y, z in zip(basis['sphere'], basis['boundary_disk'],
                                                 basis['mobius'])]
                    sources.append((raw, vector))
        for raw, vector in sources:
            for boundary in (False, True):
                size, pairings = normal_arc_pairings(raw, vector, boundary=boundary)
                expected = explicit_minima(size, pairings)
                for rule in ('aht', 'fine_wilf'):
                    index, _ = prepare_orbit_index(size, pairings, periodic_rule=rule)
                    self.assertEqual([index.representative(x) for x in range(size)], expected)
                    self.assertEqual(set(index.select(i) for i in range(index.count)), set(expected))
                    self.assertEqual(index.minimum_intervals, explicit_intervals(expected))
                    self.assertEqual([index.select_minimum(i) for i in range(index.count)],
                                     sorted(set(expected)))
                    systems += 1
                    points += size
        print(json.dumps(dict(native_arc_systems=systems, native_point_checks=points,
                              normal_vectors=len(sources))))

    def test_many_minimum_intervals_with_huge_binary_multiplicity(self):
        blocks, width = 512, (1 << 4096) + 3
        size = 2 * blocks * width
        pairs = [IntervalPairing(2 * i * width, (2 * i + 1) * width - 1,
                                  (2 * i + 1) * width, (2 * i + 2) * width - 1)
                 for i in range(blocks)]
        operations = []
        for i in reversed(range(blocks)):
            operations.append(dict(op='truncate', index=i, new_size=(2 * i + 1) * width))
            operations.append(dict(op='contract', gaps=[[2 * i * width, (2 * i + 1) * width - 1]]))
        proof = dict(version=2, size=size,
                     pairings=[[p.a, p.b, p.c, p.d, 1] for p in pairs],
                     orbit_count=blocks * width, operations=operations)
        index = OrbitIndex.from_certificate(size, pairs, proof)
        expected = tuple((2 * i * width, (2 * i + 1) * width) for i in range(blocks))
        self.assertEqual(index.minimum_intervals, expected)
        self.assertEqual(index.statistics['gap_records'], blocks)
        self.assertEqual(index.statistics['minimum_intervals'], blocks)
        for rank in (0, width - 1, width, width + 1, 257 * width + 13, index.count - 1):
            block, offset = divmod(rank, width)
            minimum = 2 * block * width + offset
            self.assertEqual(index.select_minimum(rank), minimum)
            self.assertEqual(index.minimum_rank(minimum), rank)
            self.assertEqual(index.orbit_rank(minimum + width), rank)
            self.assertEqual(index.representative(minimum + width), minimum)
            with self.assertRaises(ValueError):
                index.minimum_rank(minimum + width)
        print(json.dumps(dict(large_gap_records=blocks, minimum_intervals=blocks,
                              universe_bits=size.bit_length(),
                              orbit_count_bits=index.count.bit_length())))

    def test_no_producer_during_preparation_or_queries(self):
        import fastunknot.interval_orbits as producer
        pairings = [IntervalPairing(0, 15, 8, 23)]
        raw = producer.count_orbits(24, pairings, record_certificate=True)
        original = producer.count_orbits

        def disabled(*args, **kwargs):
            raise AssertionError('orbit discovery was called')

        producer.count_orbits = disabled
        try:
            index = OrbitIndex.from_certificate(24, pairings, raw.certificate)
            self.assertEqual(index.representative(22), 6)
            self.assertTrue(index.same_orbit(2, 18))
            self.assertEqual(set(index.select(i) for i in range(index.count)), set(range(8)))
        finally:
            producer.count_orbits = original

    def test_budget_and_cancellation(self):
        pairings = [IntervalPairing(0, 12, 7, 19)]
        index, raw = prepare_orbit_index(20, pairings, max_cycles=0)
        self.assertIsNone(index)
        self.assertFalse(raw.complete)
        index, raw = prepare_orbit_index(20, pairings)

        class Cancelled(RuntimeError):
            pass

        class Cancel:
            def __bool__(self):
                return False
            def __call__(self):
                raise Cancelled

        for call in (lambda: OrbitIndex.from_certificate(20, pairings, raw.certificate, check=Cancel()),
                     lambda: index.representative(10, check=Cancel()),
                     lambda: index.select(0, check=Cancel()),
                     lambda: index.select_minimum(0, check=Cancel()),
                     lambda: index.minimum_rank(0, check=Cancel()),
                     lambda: index.orbit_rank(10, check=Cancel()),
                     lambda: index.same_orbit(0, 0, check=Cancel())):
            with self.assertRaises(Cancelled):
                call()


if __name__ == '__main__':
    unittest.main(verbosity=2)
