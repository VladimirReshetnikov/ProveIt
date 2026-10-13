"""Independent bounded cone audits for reusable-kernel ray enumeration."""
from fractions import Fraction as Q
from itertools import combinations
from math import comb
import random
import unittest

from .common import Block, compile_two_block
from .kernel_rays import KernelCone, enumerate_rays_kernel
from projective_ports.model import ResourceLimit
from projective_ports.fixtures import (sleeve_blocks, centroid_blocks,
    false_convexification, nonextreme_assembly, solid_torus, capped_solid_torus,
    matching)
from experiments.oracle import all_rays


def block(n, rows=(), conflicts=()):
    return Block(n, tuple(rows), ((1,)*n,), tuple(conflicts))


def repeated_coordinates(groups, copies):
    n = groups*copies
    rows = []
    for g in range(groups):
        for k in range(1, copies):
            row = [0]*n
            row[g*copies+k] = 1
            row[g*copies] = -(k+1)
            rows.append(tuple(row))
    return block(n, rows)


class KernelRayTests(unittest.TestCase):
    def assertOracle(self, b):
        expected = set(all_rays(b.n, b.equations, b.conflicts))
        stats = {}
        actual = enumerate_rays_kernel(b, stats=stats)
        self.assertEqual(set(actual), expected)
        self.assertEqual(len(actual), len(set(actual)))
        self.assertEqual(stats['rays'], len(expected))
        self.assertTrue(stats['complete'])
        self.assertEqual(stats['candidates'], stats['candidate_bound'])
        return actual, stats

    def test_random_small_cones_against_independent_support_oracle(self):
        rng = random.Random(11820261012)
        checked = 0
        for n in range(1, 8):
            for case in range(60):
                rows = []
                for _ in range(rng.randrange(n+2)):
                    if case % 4 == 0:
                        rows.append(tuple(rng.randrange(3) for _ in range(n)))
                    elif case % 4 == 1:
                        row = [0]*n
                        a, b = rng.randrange(n), rng.randrange(n)
                        row[a] += rng.randrange(1, 4)
                        row[b] -= rng.randrange(1, 4)
                        rows.append(tuple(row))
                    elif case % 4 == 2:
                        rows.append(tuple(Q(rng.randrange(-2, 3), rng.randrange(1, 4))
                                          for _ in range(n)))
                    else:
                        rows.append(tuple(rng.randrange(-2, 3) for _ in range(n)))
                conflicts = tuple(p for p in combinations(range(n), 2) if rng.random() < .15)
                self.assertOracle(block(n, rows, conflicts))
                checked += 1
        self.assertEqual(checked, 420)

    def test_delivered_fixture_blocks(self):
        cases = list(sleeve_blocks(1)) + list(centroid_blocks())
        cases += list(false_convexification()) + list(nonextreme_assembly())
        source = matching(solid_torus())
        cases.append(block(source.n, source.equations, source.conflicts))
        source = matching(capped_solid_torus())
        cases.extend(compile_two_block(source, range(7)).blocks)
        for b in cases:
            with self.subTest(n=b.n, equations=b.equations):
                self.assertOracle(b)
        self.assertEqual(len(cases), 10)

    def test_full_rank_nullity_one_and_empty_equations(self):
        rays, stats = self.assertOracle(block(3, ((1, 0, 0), (0, 1, 0), (0, 0, 1))))
        self.assertEqual(rays, ())
        self.assertEqual(stats['candidate_kernel_solves'], 0)
        self.assertEqual(enumerate_rays_kernel(block(1, ((1,),)), max_supports=0), ())
        rays, stats = self.assertOracle(block(3, ((3, -2, 0), (0, 5, -3))))
        self.assertEqual(rays, ((2, 3, 5),))
        self.assertEqual(stats['nullity'], 1)
        self.assertEqual(stats['candidate_bound'], 1)
        self.assertOracle(block(6))
        self.assertOracle(block(1, ((0,), (0,))))

    def test_opposite_forms_lower_dimensional_cone_and_forced_zeros(self):
        rays, stats = self.assertOracle(block(4, ((1, 1, 0, 0),)))
        self.assertEqual(rays, ((0, 0, 0, 1), (0, 0, 1, 0)))
        self.assertEqual(stats['nullity'], 3)
        self.assertEqual(stats['hyperplanes'], 3)
        self.assertEqual(stats['repeated_coordinate_hyperplanes'], 1)
        self.assertOracle(block(5, ((1, 1, 1, 0, 0),)))
        rays, stats = self.assertOracle(block(3, ((1, 0, 0), (0, 1, -2))))
        self.assertEqual(rays, ((0, 2, 1),))
        self.assertEqual(stats['zero_coordinate_forms'], 1)
        self.assertEqual(self.assertOracle(block(2, ((1, 1),)))[0], ())

    def test_conflicts_are_applied_to_reconstructed_support(self):
        b = block(4, ((1, -1, 0, 0),), ((0, 1),))
        rays, stats = self.assertOracle(b)
        self.assertEqual(rays, ((0, 0, 0, 1), (0, 0, 1, 0)))
        self.assertGreater(stats['incompatible_systems'], 0)

    def test_proportional_coordinate_deduplication_and_reuse(self):
        b = repeated_coordinates(3, 20)
        prepared = KernelCone(b)
        stats = {}
        rays = prepared.rays(stats=stats)
        self.assertEqual(stats['nullity'], 3)
        self.assertEqual(stats['hyperplanes'], 3)
        self.assertEqual(stats['repeated_coordinate_hyperplanes'], 57)
        self.assertEqual(stats['candidate_kernel_solves'], 3)
        self.assertEqual(stats['candidate_bound'], 3)
        self.assertEqual(comb(b.n, stats['nullity']-1), 1770)
        expected = set()
        for g in range(3):
            row = [0]*60
            row[g*20:g*20+20] = range(1, 21)
            expected.add(tuple(row))
        self.assertEqual(set(rays), expected)
        basis = prepared.basis
        self.assertEqual(prepared.rays(max_supports=3), rays)
        self.assertIs(prepared.basis, basis)
        with self.assertRaises(ResourceLimit):
            prepared.rays(max_supports=2)

    def test_large_binary_rational_coefficients(self):
        a, b = 2**257+1, 2**263+3
        rays, _ = self.assertOracle(block(3, ((Q(1, a), Q(-1, b), 0),)))
        self.assertEqual(set(rays), {(a, b, 0), (0, 0, 1)})

    def test_equation_and_coordinate_changes_preserve_rays(self):
        rng = random.Random(118)
        source = block(6, ((1, 2, -1, 0, 0, 0), (0, 0, 1, -2, -1, 0)), ((0, 1), (4, 5)))
        expected = set(all_rays(source.n, source.equations, source.conflicts))
        for _ in range(30):
            order = list(range(source.n))
            rng.shuffle(order)
            inverse = {old: new for new, old in enumerate(order)}
            a, b = source.equations
            mixed = (tuple(3*x+2*y for x, y in zip(a, b)),
                     tuple(5*x+3*y for x, y in zip(a, b)), (0,)*source.n)
            moved = block(source.n, (tuple(row[j] for j in order) for row in mixed),
                          ((inverse[x], inverse[y]) for x, y in source.conflicts))
            actual = enumerate_rays_kernel(moved)
            restored = {tuple(ray[inverse[j]] for j in range(source.n)) for ray in actual}
            self.assertEqual(restored, expected)

    def test_caps_count_hyperplane_candidates_and_reject_invalid_caps(self):
        b = block(3)
        stats = {}
        with self.assertRaisesRegex(ResourceLimit, 'kernel-hyperplane'):
            enumerate_rays_kernel(b, max_supports=1, stats=stats)
        self.assertEqual(stats['candidates'], 2)
        self.assertEqual(stats['candidate_kernel_solves'], 1)
        self.assertFalse(stats['complete'])
        self.assertEqual(len(enumerate_rays_kernel(b, max_supports=3)), 3)
        for invalid in (True, False, -1, 1.0, '1'):
            with self.subTest(cap=invalid), self.assertRaises(ValueError):
                enumerate_rays_kernel(b, max_supports=invalid)
        with self.assertRaises(TypeError):
            enumerate_rays_kernel(b, stats=[])
        with self.assertRaises(TypeError):
            KernelCone(object())

    def test_callback_exceptions_propagate_from_preparation_and_candidates(self):
        class Stop:
            def __init__(self, stop_after):
                self.calls = 0
                self.stop_after = stop_after
                self.error = ResourceLimit('external cancellation')
            def __bool__(self):
                return False
            def __call__(self):
                self.calls += 1
                if self.calls == self.stop_after:
                    raise self.error
        for after in (1, 12):
            callback = Stop(after)
            with self.assertRaises(ResourceLimit) as caught:
                enumerate_rays_kernel(repeated_coordinates(2, 8), check=callback)
            self.assertIs(caught.exception, callback.error)
            self.assertEqual(callback.calls, after)
        prepared = KernelCone(block(4))
        callback = Stop(8)
        with self.assertRaises(ResourceLimit) as caught:
            prepared.rays(check=callback)
        self.assertIs(caught.exception, callback.error)
        callback = Stop(1)
        stats = {'complete': True, 'rays': 99}
        with self.assertRaises(ResourceLimit):
            enumerate_rays_kernel(block(1, ((1,),)), check=callback, stats=stats)
        self.assertFalse(stats['complete'])
        self.assertNotIn('rays', stats)


if __name__ == '__main__':
    unittest.main()
