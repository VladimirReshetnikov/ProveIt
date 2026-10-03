#!/usr/bin/env python3
"""Public-boundary regressions; unittest checks remain active under python -O."""
from copy import deepcopy
from types import SimpleNamespace
import unittest

from radius_one import RadiusOneCA


class IntSubclass(int):
    pass


def toy():
    return SimpleNamespace(
        names=['a', 'b', 'c', 'd'], velocity=[-1, 0, 1, 0],
        single={0: 2, 2: 1, 1: 0, 3: 3},
        pairs={(0, 1): [2, 3], (2, 3): [0, 1]},
        halt='halt', type_ids={('L', 0, ('halt', 0, 0)): 0, ('S', 0): 1})


class RadiusOneBoundaryTests(unittest.TestCase):
    def setUp(self):
        self.base = toy()
        self.ca = RadiusOneCA(self.base, 4)

    def test_r_is_exact_int_and_large_enough(self):
        for r in (True, False, 4.0, 4.5, '4', [], {}, -1, 0, IntSubclass(4)):
            with self.subTest(r=r), self.assertRaises(ValueError):
                RadiusOneCA(toy(), r)
        fast = toy()
        fast.velocity[0] = 5
        with self.assertRaises(ValueError):
            RadiusOneCA(fast, 4)
        self.assertEqual(RadiusOneCA(fast).r, 5)
        self.assertEqual(RadiusOneCA(toy()).r, 1)

    def test_malformed_base_descriptors(self):
        for obj in (None, object(), {}, SimpleNamespace(names=[])):
            with self.subTest(base=obj), self.assertRaises(ValueError):
                RadiusOneCA(obj)
        replacements = {
            'names': [None, 4, 'abcd', {}],
            'velocity': [None, 4, {}, [], [0, 1, 2], [True, 0, 1, 0],
                         [0.0, 0, 1, 0], [IntSubclass(0), 0, 1, 0]],
            'single': [None, [], {}, {0: 0}, {0: 0, 1: 1, 2: 2, 3: 2},
                       {False: 0, 1: 1, 2: 2, 3: 3},
                       {0: 0.0, 1: 1, 2: 2, 3: 3},
                       {0: 0, 1: 1, 2: 2, 4: 3}],
            'pairs': [None, [], {(0,): (0, 1)}, {(0, 0): (0, 1)},
                      {(1, 0): (0, 1)}, {(0, 4): (0, 1)},
                      {(False, 1): (0, 1)}, {(0, 1.0): (0, 1)},
                      {(0, 1): (0, True)}, {(0, 1): (0, 4)},
                      {(0, 1): (2, 3)}, {(0, 1): 2}, {(0, 1): '23'},
                      {(0, 1): (2, 3), (2, 3): (2, 3)}],
        }
        for field, values in replacements.items():
            for value in values:
                base = toy()
                setattr(base, field, value)
                with self.subTest(field=field, value=value), self.assertRaises(ValueError):
                    RadiusOneCA(base)

    def test_exact_ids_and_phases_in_scalar_helpers(self):
        for method in (self.ca.encode_channel, self.ca.epsilon):
            for bad in (True, False, 0.0, 0.5, '0', None, [], {}, -1, 4, IntSubclass(0)):
                with self.subTest(method=method.__name__, bad_id=bad), self.assertRaises(ValueError):
                    method(bad, 0)
                with self.subTest(method=method.__name__, bad_phase=bad), self.assertRaises(ValueError):
                    method(0, bad)
        self.assertEqual(self.ca.encode_channel(3, 3), 15)
        self.assertEqual([self.ca.epsilon(0, p) for p in range(4)], [-1, 0, 0, 0])

    def test_every_particle_boundary_rejects_malformed_and_duplicate_lanes(self):
        calls = [self.ca.embed, self.ca.project, self.ca.step, self.ca.inverse_step,
                 lambda p: self.ca.committed_halt(p, self.base)]
        bad_inputs = [None, 2, '00', b'00', {0: 0}, [None], [0], ['00'],
                      [()], [(0,)], [(0, 0, 0)], [(None, 0)], [(True, 0)],
                      [(0.0, 0)], [(IntSubclass(0), 0)], [([], 0)],
                      [(0, True)], [(0, 0.0)], [(0, IntSubclass(0))],
                      [(0, None)], [(0, [])], [(0, {})], [(0, -1)],
                      [(0, 100)], [(0, 0), (0, 0)], [[0, 0], [0, 0]]]
        for index, call in enumerate(calls):
            for value in bad_inputs:
                with self.subTest(helper=index, value=value), self.assertRaises(ValueError):
                    call(deepcopy(value))
        with self.assertRaises(ValueError):
            self.ca.embed([(0, self.ca.base_type_count)])
        for call in calls[1:]:
            with self.assertRaises(ValueError):
                call([(0, self.ca.channel_count)])

    def test_project_checks_phase_even_on_vacuum(self):
        for bad in (True, False, 0.0, None, '0', -1, 4, IntSubclass(0)):
            with self.subTest(phase=bad), self.assertRaises(ValueError):
                self.ca.project((), bad)
        with self.assertRaises(ValueError):
            self.ca.project(((0, 1),), 0)
        with self.assertRaises(ValueError):
            self.ca.project(((0, 0), (1, 1)), 0)
        self.assertEqual(self.ca.project(((2, 13),), 1), ((2, 3),))

    def test_local_zero_checks_channels_and_direction(self):
        for bad in (None, 0, '0', {}, [True], [False], [0.0], [IntSubclass(0)],
                    [None], [[]], [(0,)], [-1], [16], [0, 0]):
            with self.subTest(present=bad), self.assertRaises(ValueError):
                self.ca.local_zero(bad)
        for inverse in (None, 0, 1, 'yes', [], IntSubclass(1)):
            with self.subTest(inverse=inverse), self.assertRaises(ValueError):
                self.ca.local_zero((), inverse)
        self.assertEqual(self.ca.local_zero([0, 4, 1]), (1, 8, 12))
        self.assertEqual(self.ca.local_zero([1, 8, 12], True), (0, 1, 4))
        self.assertEqual(self.ca.local_zero([0, 4, 8]), (0, 4, 8))
        self.assertEqual(self.ca.local_zero(iter([0, 4])), (8, 12))

    def test_halt_descriptor_validation_and_explicit_base_binding(self):
        for base in (None, object(), SimpleNamespace(halt='halt', type_ids=None),
                     SimpleNamespace(halt='halt', type_ids={})):
            with self.subTest(base=base), self.assertRaises(ValueError):
                self.ca.committed_halt((), base)
        for bad in (True, False, 0.0, None, [], -1, 4, IntSubclass(0), 1):
            base = toy()
            base.type_ids[('L', 0, ('halt', 0, 0))] = bad
            with self.subTest(id=bad), self.assertRaises(ValueError):
                self.ca.committed_halt((), base)
        base = toy()
        base.halt = []
        with self.assertRaises(ValueError):
            self.ca.committed_halt((), base)
        self.assertTrue(self.ca.committed_halt(((0, 0), (0, 4)), self.base))
        self.assertFalse(self.ca.committed_halt(((0, 0), (0, 4), (0, 8)), self.base))
        self.assertFalse(self.ca.committed_halt(((0, 1), (0, 5)), self.base))
        alternate = toy()
        alternate.type_ids[('L', 0, ('halt', 0, 0))] = 2
        self.assertTrue(self.ca.committed_halt(((0, 8), (0, 4)), alternate))
        self.assertFalse(self.ca.committed_halt(((0, 0), (0, 4)), alternate))

    def test_transition_descriptor_snapshots_are_immutable_and_independent(self):
        before = self.ca.step(((0, 0), (0, 4)))
        for name in ('single', 'pairs', 'inverse_single', 'inverse_pairs'):
            mapping = getattr(self.ca, name)
            key = next(iter(mapping))
            with self.subTest(mapping=name), self.assertRaises(TypeError):
                mapping[key] = mapping[key]
        self.assertIsInstance(self.ca.base_velocity, tuple)
        self.assertIsInstance(self.ca.displacement, tuple)
        self.assertIsInstance(self.ca.pairs[(0, 1)], tuple)
        self.base.names.append('extra')
        self.base.velocity[0] = 999
        self.base.single.clear()
        self.base.pairs[(0, 1)][0] = 0
        self.base.pairs.clear()
        self.assertEqual(self.ca.base_type_count, 4)
        self.assertEqual(self.ca.base_velocity, (-1, 0, 1, 0))
        self.assertEqual(self.ca.step(((0, 0), (0, 4))), before)
        self.assertEqual(self.ca.inverse_step(before), ((0, 0), (0, 4)))

    def test_particle_inputs_are_not_mutated_and_iterated_only_once(self):
        class Once:
            def __init__(self, values):
                self.values, self.calls = values, 0

            def __iter__(self):
                self.calls += 1
                if self.calls != 1:
                    raise RuntimeError('input was iterated more than once')
                return iter(self.values)

        cases = [(self.ca.embed, [[5, 1], [-3, 0]]),
                 (self.ca.project, [[5, 4], [-3, 0]]),
                 (self.ca.step, [[5, 4], [-3, 0]]),
                 (self.ca.inverse_step, [[5, 4], [-3, 0]]),
                 (lambda p: self.ca.committed_halt(p, self.base), [[0, 4], [0, 0]])]
        for call, particles in cases:
            original = deepcopy(particles)
            expected = call(particles)
            self.assertEqual(particles, original)
            source = Once(particles)
            self.assertEqual(call(source), expected)
            self.assertEqual(source.calls, 1)
            self.assertEqual(particles, original)
            with self.assertRaises(ValueError):
                call(iter([[0, 0], [0, 0]]))
        channels = [4, 0, 1]
        self.assertEqual(self.ca.local_zero(Once(channels)), (1, 8, 12))
        self.assertEqual(channels, [4, 0, 1])
        base = toy()
        base.names, base.velocity = iter(base.names), iter(base.velocity)
        self.assertEqual(RadiusOneCA(base).base_velocity, (-1, 0, 1, 0))

    def test_iterable_snapshots_lists_vacuum_and_large_positions(self):
        particles = [[-10**100, 0], [10**100, 1]]
        embedded = self.ca.embed(iter(particles))
        self.assertEqual(self.ca.project(iter(embedded)), tuple(map(tuple, particles)))
        advanced = self.ca.step(iter(embedded))
        self.assertEqual(self.ca.inverse_step(iter(advanced)), embedded)
        self.assertTrue(self.ca.committed_halt(iter([[0, 0], [0, 4]]), self.base))
        for call in (self.ca.embed, self.ca.project, self.ca.step, self.ca.inverse_step):
            self.assertEqual(call(iter(())), ())
        self.assertFalse(self.ca.committed_halt(iter(()), self.base))
        empty = SimpleNamespace(names=[], velocity=[], single={}, pairs={})
        self.assertEqual(RadiusOneCA(empty).step(()), ())


if __name__ == '__main__':
    unittest.main(verbosity=2)
