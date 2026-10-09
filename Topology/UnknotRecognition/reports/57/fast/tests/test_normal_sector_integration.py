"""Standalone integration tests for supplied-sector normal-disc discovery.

Only the standard library and fastunknot are required. From fast/, run:
python -S -m unittest discover -s tests -p test_normal_sector_integration.py -v
"""

from copy import deepcopy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from fastunknot.normal_sector import (
    build_sector_kernel, discover_in_sector, enumerate_sector, sparse_disc_search,
)
from fastunknot.normal_sector_verify import (
    verify_sector_exhaustion, verify_sector_witness,
)


def solid_torus():
    """One tetrahedron with faces 0 and 1 identified; faces 2 and 3 bound a torus."""
    return {'tetrahedra': [[
        {'tetrahedron': 0, 'permutation': [1, 2, 3, 0]},
        {'tetrahedron': 0, 'permutation': [3, 0, 1, 2]},
        None, None,
    ]]}


def capped_solid_torus():
    """Attach a tetrahedral ball to face 2; the manifold remains a solid torus."""
    result = solid_torus()
    result['tetrahedra'][0][2] = {
        'tetrahedron': 1, 'permutation': [0, 1, 3, 2]}
    result['tetrahedra'].append([
        None, None, None,
        {'tetrahedron': 0, 'permutation': [0, 1, 3, 2]},
    ])
    return result


def vector_set(surfaces):
    return {tuple(x for row in surface for x in row) for surface in surfaces}


class NormalSectorIntegrationTests(unittest.TestCase):
    def test_meridian_witness_and_replay(self):
        tri = solid_torus()
        expected = [[1, 1, 0, 0, 0, 0, 1]]
        rays, stats = enumerate_sector(tri, [(0, 2)], phase='quadrilateral')
        self.assertEqual(rays, [expected])
        self.assertEqual(stats['matching_nullity'], 1)
        answer = discover_in_sector(tri, [(0, 2)])
        self.assertEqual(answer['status'], 'DISC_FOUND')
        self.assertEqual(answer['coordinates'], expected)
        self.assertTrue(verify_sector_witness(tri, answer['certificate']))

    def test_standard_methods_match_literal_two_type_ray_set(self):
        tri = capped_solid_torus()
        expected = vector_set([
            [[1, 1, 0, 0, 0, 0, 1], [1, 2, 0, 0, 0, 0, 0]],
            [[1, 1, 1, 1, 0, 0, 0], [1, 1, 0, 0, 1, 0, 0]],
        ])
        for method in ('auto', 'arrangement', 'supports'):
            with self.subTest(method=method):
                rays, _ = enumerate_sector(tri, [(0, 2), (1, 0)], method=method)
                self.assertEqual(vector_set(rays), expected)

    def test_positive_euler_does_not_imply_essential_disc(self):
        tri = capped_solid_torus()
        for phase, status in [('quadrilateral', 'POSITIVE_EULER_ONLY'),
                              ('standard', 'NO_VERTEX_DISC_IN_SECTOR')]:
            with self.subTest(phase=phase):
                answer = discover_in_sector(tri, [(1, 0)], phase=phase)
                self.assertEqual(answer['status'], status)
                self.assertEqual(answer['certificate']['rays'][0]
                                 ['euler_characteristic'], 1)
                self.assertTrue(verify_sector_exhaustion(tri, answer['certificate']))

    def test_empty_sector_and_exhausted_allowances(self):
        tri = solid_torus()
        answer = discover_in_sector(tri, [], max_bases=0)
        self.assertEqual(answer['status'], 'NO_POSITIVE_EULER')
        self.assertTrue(verify_sector_exhaustion(tri, answer['certificate']))
        for allowance in ({'max_bases': 0}, {'max_orbit_cycles': 0}):
            with self.subTest(allowance=allowance):
                answer = discover_in_sector(tri, [(0, 2)], **allowance)
                self.assertEqual(answer['status'], 'INCONCLUSIVE')
                self.assertNotIn('certificate', answer)

    def test_false_witness_and_exhaustion_assertions_are_rejected(self):
        tri = solid_torus()
        original = discover_in_sector(tri, [(0, 2)])['certificate']
        changed = deepcopy(original)
        changed['coordinates'][0][0] += 1
        self.assertFalse(verify_sector_witness(tri, changed))
        changed = deepcopy(original)
        changed['allowed_types'] = []
        self.assertFalse(verify_sector_witness(tri, changed))
        changed = deepcopy(original)
        changed['source_sha256'] = '0' * 64
        self.assertFalse(verify_sector_witness(tri, changed))
        original = discover_in_sector(tri, [(0, 0)])['certificate']
        self.assertTrue(original['rays'])
        changed = deepcopy(original)
        changed['rays'].clear()
        self.assertFalse(verify_sector_exhaustion(tri, changed))
        changed = deepcopy(original)
        changed['rays'][0]['euler_characteristic'] += 1
        self.assertFalse(verify_sector_exhaustion(tri, changed))

    def test_false_valued_cancellation_propagates(self):
        class Cancel:
            def __init__(self):
                self.calls = 0

            def __bool__(self):
                return False

            def __call__(self):
                self.calls += 1
                if self.calls == 4:
                    raise ValueError('integration cancellation')

        tri = solid_torus()
        for typ, verifier in [(2, verify_sector_witness),
                              (0, verify_sector_exhaustion)]:
            proof = discover_in_sector(tri, [(0, typ)])['certificate']
            with self.assertRaisesRegex(ValueError, 'integration cancellation'):
                verifier(tri, proof, check=Cancel())

    def test_outer_search_reports_restricted_scope_and_caps(self):
        tri = solid_torus()
        self.assertEqual(sparse_disc_search(tri, max_active=0)['status'],
                         'NO_VERTEX_DISC_UP_TO_SUPPORT')
        self.assertEqual(sparse_disc_search(tri, max_active=1,
                         max_sectors=0)['status'], 'INCONCLUSIVE')
        answer = sparse_disc_search(tri, max_active=1)
        self.assertEqual(answer['status'], 'DISC_FOUND')
        self.assertTrue(verify_sector_witness(tri, answer['certificate']))

    def test_invalid_support_is_rejected(self):
        for support in [[(0, 0), (0, 1)], [(0, True)], [(1, 0)], [(0, 3)]]:
            with self.subTest(support=support):
                with self.assertRaises(ValueError):
                    build_sector_kernel(solid_torus(), support)


if __name__ == '__main__':
    unittest.main()
