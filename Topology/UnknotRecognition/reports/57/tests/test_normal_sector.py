"""Focused public-contract tests, backed by independent frozen Regina vectors."""

from copy import deepcopy
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT/'fast'), str(ROOT/'scripts')]
from fibonacci_fixture import fibonacci_torus
from fastunknot.normal_sector import (
    build_sector_kernel, enumerate_sector, discover_in_sector, sparse_disc_search,
)
from fastunknot.normal_sector_verify import (
    verify_sector_witness, verify_sector_exhaustion,
)


class NormalSectorTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        data = json.loads((ROOT/'results'/'discovery_corpus.json').read_text())
        cls.fixtures = {r['id']:r for r in data['records']}
        cls.tri = cls.fixtures['fibonacci_lst_01']['triangulation']

    def test_known_meridian_witness(self):
        result = discover_in_sector(self.tri, [(0, 2)])
        self.assertEqual(result['status'], 'DISC_FOUND')
        self.assertTrue(verify_sector_witness(self.tri, result['certificate']))

    def test_empty_sector_is_all_links(self):
        result = discover_in_sector(self.tri, [], max_bases=0)
        self.assertEqual(result['status'], 'NO_POSITIVE_EULER')
        self.assertTrue(verify_sector_exhaustion(self.tri, result['certificate']))

    def test_all_standard_methods_match_independent_vectors(self):
        fixture = self.fixtures['cap_1_2_1']
        tri = fixture['triangulation']
        allowed = [(0,2), (1,0)]
        expected = {tuple(x for row in s['coordinates'] for x in row)
                    for s in fixture['standard_vertices']
                    if s['quadrilateral_support'] and all(
                        not value or (t,q) in allowed
                        for t,row in enumerate(s['coordinates'])
                        for q,value in enumerate(row[4:]))}
        for method in ('auto','supports','arrangement'):
            actual, _ = enumerate_sector(tri, allowed, method=method)
            self.assertEqual({tuple(x for row in r for x in row) for r in actual}, expected)

    def test_positive_euler_inessential_disc(self):
        tri = self.fixtures['cap_1_2_1']['triangulation']
        result = discover_in_sector(tri, [(1,0)])
        self.assertEqual(result['status'], 'POSITIVE_EULER_ONLY')
        self.assertTrue(verify_sector_exhaustion(tri, result['certificate']))

    def test_standard_exhaustion_is_restricted(self):
        tri = self.fixtures['cap_1_2_1']['triangulation']
        result = discover_in_sector(tri, [(1,0)], phase='standard')
        self.assertEqual(result['status'], 'NO_VERTEX_DISC_IN_SECTOR')
        self.assertTrue(verify_sector_exhaustion(tri, result['certificate']))

    def test_missing_ray_is_rejected(self):
        result = discover_in_sector(self.tri, [(0,0)])
        proof = deepcopy(result['certificate'])
        proof['rays'].clear()
        self.assertFalse(verify_sector_exhaustion(self.tri, proof))

    def test_changed_coordinates_are_rejected(self):
        result = discover_in_sector(self.tri, [(0,2)])
        proof = deepcopy(result['certificate'])
        proof['coordinates'][0][0] += 1
        self.assertFalse(verify_sector_witness(self.tri, proof))

    def test_changed_allowed_types_are_rejected(self):
        result = discover_in_sector(self.tri, [(0,2)])
        proof = deepcopy(result['certificate'])
        proof['allowed_types'] = [[0,1]]
        self.assertFalse(verify_sector_witness(self.tri, proof))

    def test_source_digest_is_binding(self):
        result = discover_in_sector(self.tri, [(0,2)])
        proof = deepcopy(result['certificate'])
        proof['source_sha256'] = '0'*64
        self.assertFalse(verify_sector_witness(self.tri, proof))

    def test_basis_exhaustion_has_no_certificate(self):
        result = discover_in_sector(self.tri, [(0,2)], max_bases=0)
        self.assertEqual(result['status'], 'INCONCLUSIVE')
        self.assertNotIn('certificate', result)

    def test_orbit_exhaustion_has_no_certificate(self):
        result = discover_in_sector(self.tri, [(0,2)], max_orbit_cycles=0)
        self.assertEqual(result['status'], 'INCONCLUSIVE')
        self.assertNotIn('certificate', result)

    def test_outer_search_has_honest_cutoffs(self):
        self.assertEqual(sparse_disc_search(self.tri, max_active=0)['status'],
                         'NO_VERTEX_DISC_UP_TO_SUPPORT')
        self.assertEqual(sparse_disc_search(self.tri, max_active=1,
                         max_sectors=0)['status'], 'INCONCLUSIVE')
        self.assertEqual(sparse_disc_search(self.tri, max_active=1)['status'], 'DISC_FOUND')

    def test_invalid_support_is_rejected(self):
        for value in [[(0,0),(0,1)], [(0,True)], [(1,0)], [(0,3)]]:
            with self.assertRaises(ValueError):
                build_sector_kernel(self.tri, value)

    def test_empty_outer_search_still_validates_allowances(self):
        with self.assertRaises(ValueError):
            sparse_disc_search(self.tri, max_active=0, max_bases_per_sector=-1)

    def test_false_valued_cancellation_propagates(self):
        class Stop:
            def __bool__(self):
                return False
            def __init__(self):
                self.calls = 0
            def __call__(self):
                self.calls += 1
                if self.calls == 4:
                    raise ValueError('user cancellation')
        for typ, verify in [(2,verify_sector_witness),(0,verify_sector_exhaustion)]:
            result = discover_in_sector(self.tri, [(0,typ)])
            with self.assertRaisesRegex(ValueError, 'user cancellation'):
                verify(self.tri, result['certificate'], check=Stop())

    def test_large_dense_dimension_one_ray(self):
        fixture = fibonacci_torus(32)
        rows, stats = enumerate_sector(fixture['triangulation'],
                                      [(i,2) for i in range(32)], phase='quadrilateral')
        self.assertEqual(rows, [fixture['coordinates']])
        self.assertEqual(stats['matching_nullity'], 1)
        self.assertEqual(stats['bases_attempted'], 1)
        self.assertGreater(sum(map(sum,rows[0])), 10**7)

    def test_contracted_matrix_has_special_structure(self):
        fixture = self.fixtures['cap_1_2_1']
        kernel = build_sector_kernel(fixture['triangulation'], [(0,2),(1,0)])
        p, k = len(kernel.classes),len(kernel.support)
        self.assertLessEqual(p+k, 9*k)
        self.assertLessEqual(len(kernel.matrix), 4*k)
        for row in kernel.matrix:
            self.assertLessEqual(sum(x*x for x in row),4)
        for q in range(k):
            self.assertLessEqual(sum(abs(row[p+q]) for row in kernel.matrix),4)


if __name__ == '__main__':
    unittest.main()
