"""Geometric core proofs and independent algebraic tests of exact saturation."""

from copy import deepcopy
from itertools import permutations
import random
import unittest
from unittest.mock import patch

from fastunknot.core_handlebody import (
    capped_cancellation_plan, core_handlebody_certificate, leaf_cancellation_plan)
from fastunknot.core_handlebody_verify import verify_core_handlebody_certificate
from fastunknot.normal_parallelity_geometry import _parallelity_geometry
from fastunknot.normal_surface_geometry import _prepare, _coordinates
from normal_orbit_research.fixtures import layered_torus, interior_vertex_torus


def source_core(raw, rows):
    p = _prepare(raw, lambda: None)
    x = _coordinates(p, rows, lambda: None)
    return _parallelity_geometry(p, x, lambda: None)['core']


class CoreHandlebodyTests(unittest.TestCase):
    def test_saturated_schedule_matches_unbounded_integer_counts(self):
        rng = random.Random(26101201)
        for _ in range(1200):
            counts = {r: {c: rng.randrange(5) for c in range(rng.randrange(1, 8))}
                      for r in range(rng.randrange(1, 8))}
            result = capped_cancellation_plan(counts)
            exact = deepcopy(counts)
            for r, c in result['cancellations']:
                self.assertEqual(exact[r].get(c, 0), 1)
                donor = exact.pop(r)
                donor.pop(c)
                for row in exact.values():
                    n = row.pop(c, 0)
                    for h, value in donor.items():
                        row[h] = row.get(h, 0) + n * value
            self.assertEqual(result['remaining_rows'], sorted(exact))
            for row in exact.values():
                self.assertNotIn(1, row.values())

    def test_square_leaf_completeness_against_exact_permanents(self):
        rng = random.Random(26101202)
        for n in range(1, 6):
            for _ in range(150):
                matrix = [[rng.randrange(3) for _ in range(n)] for _ in range(n)]
                permanent = 0
                for sigma in permutations(range(n)):
                    value = 1
                    for r, c in enumerate(sigma):
                        value *= matrix[r][c]
                    permanent += value
                counts = {r: dict(enumerate(row)) for r, row in enumerate(matrix)}
                result = leaf_cancellation_plan(counts)
                self.assertEqual(not result['remaining_rows'], permanent == 1)

    def test_layered_ball_and_empty_solid_torus_cores(self):
        for t in (1, 2, 3, 4, 8, 16, 64):
            raw, base = layered_torus(t)
            for multiple in (0, 1, 1 << 256):
                rows = [[multiple * x for x in row] for row in base]
                core = source_core(raw, rows)
                result = core_handlebody_certificate(core)
                self.assertEqual(result['status'], 'COMPLETE')
                if multiple:
                    self.assertEqual(result['certificate']['method'], 'leaf')
                self.assertTrue(verify_core_handlebody_certificate(core, result['certificate']))
                self.assertEqual([c['genus'] for c in result['components']], [int(multiple == 0)])
                if multiple:
                    self.assertEqual(len(result['certificate']['cancellations']), 2 * t - 2)

    def test_forged_counts_cannot_enter_small_certificate(self):
        raw, rows = layered_torus(4)
        core = source_core(raw, rows)
        proof = core_handlebody_certificate(core)['certificate']
        for key, value in [('method', 'group'), ('forest', [True]),
                           ('cancellations', proof['cancellations'][:-1]),
                           ('components', [])]:
            bad = deepcopy(proof)
            bad[key] = value
            self.assertFalse(verify_core_handlebody_certificate(core, bad))
        bad = deepcopy(proof)
        bad['counts'] = [[1]]
        self.assertFalse(verify_core_handlebody_certificate(core, bad))
        bad = deepcopy(proof)
        bad['cancellations'][0][1] = True
        self.assertFalse(verify_core_handlebody_certificate(core, bad))

    def test_independent_replay_does_not_use_producer(self):
        raw, rows = layered_torus(8)
        core = source_core(raw, rows)
        proof = core_handlebody_certificate(core)['certificate']
        with patch('fastunknot.core_handlebody._occurrences', side_effect=AssertionError), \
             patch('fastunknot.core_handlebody.leaf_cancellation_plan', side_effect=AssertionError), \
             patch('fastunknot.core_handlebody.capped_cancellation_plan', side_effect=AssertionError):
            self.assertTrue(verify_core_handlebody_certificate(core, proof))

    def test_three_handles_and_zero_relator_are_inconclusive(self):
        raw, bases = interior_vertex_torus()
        result = core_handlebody_certificate(source_core(raw, bases['sphere']))
        self.assertEqual(result['status'], 'INCONCLUSIVE')
        self.assertEqual(result['reason'], 'core_has_three_handles')
        self.assertEqual(leaf_cancellation_plan({0: {}})['remaining_rows'], [0])

    def test_callbacks_propagate(self):
        class Stop(Exception):
            pass
        def stop():
            raise Stop
        raw, rows = layered_torus(1)
        core = source_core(raw, rows)
        proof = core_handlebody_certificate(core)['certificate']
        with self.assertRaises(Stop):
            core_handlebody_certificate(core, check=stop)
        with self.assertRaises(Stop):
            verify_core_handlebody_certificate(core, proof, check=stop)


if __name__ == '__main__':
    unittest.main()
