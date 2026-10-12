"""Exact block factorization, genuine-source separation and independent replay."""

from copy import deepcopy
from fractions import Fraction
from itertools import product
from math import comb
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from fastunknot.normal_sector import _hyperplanes, sector_rays, SearchLimit
from fastunknot.normal_sector_verify import dense_sector_model, dense_reference_rays
from fastunknot.normal_surface_geometry import _coordinates
from fastunknot.sector_blocks import (
    block_sector_rays, coordinate_blocks, enumerate_sector_blocks,
    minimum_interaction_clusters, screen_sector_blocks, certify_sector_block_rays,
)
from fastunknot.sector_blocks_verify import verify_block_euler, verify_block_ray_certificate
from fastunknot.sector_sparse import PreparedSectorSource
from sector_block_research.fixtures import capped_bipyramid_chain, fibonacci_solid_torus


def ray_set(rows):
    return {tuple(value for row in surface for value in row) for surface in rows}


class SectorBlockTests(unittest.TestCase):
    def test_coordinate_blocks_are_invariant_under_dense_basis_mixing(self):
        expected = ((0,), (1,), (2, 3))
        basis = ((1, 0, 0, 0, 0), (0, 1, 0, 0, 0), (0, 0, 1, 1, 0))
        mixed = ((1, 1, 1, 1, 0), (2, -1, 1, 1, 0), (0, 1, 2, 2, 0))
        for supplied in (basis, mixed, mixed + (mixed[0], (0, 0, 0, 0, 0))):
            blocks, zero = coordinate_blocks(supplied, 5)
            self.assertEqual(tuple(block.indices for block in blocks), expected)
            self.assertEqual(zero, (4,))
            self.assertEqual(tuple(len(block.basis) for block in blocks), (1, 1, 1))
        self.assertEqual(coordinate_blocks((), 3), ((), (0, 1, 2)))
        with self.assertRaises(ValueError):
            coordinate_blocks(((1, 2),), 3)

    def test_minimum_interactions_cannot_be_ignored_for_standard_rays(self):
        blocks, _ = coordinate_blocks(((1, 0), (0, 1)), 2)
        kernel = SimpleNamespace(groups=((0, 1),), potentials={0: (1, 0), 1: (0, 1)})
        self.assertEqual(minimum_interaction_clusters(kernel, blocks), ((0, 1),))
        shifted = SimpleNamespace(groups=((0, 1),),
                                  potentials={0: (8, -13), 1: (7, -12)})
        self.assertEqual(minimum_interaction_clusters(shifted, blocks), ((0, 1),))
        independent = SimpleNamespace(groups=((0, 1), (2, 3)),
                                      potentials={0: (0, 0), 1: (1, 0),
                                                  2: (0, 0), 3: (0, 1)})
        self.assertEqual(minimum_interaction_clusters(independent, blocks), ((0,), (1,)))

    def test_connected_solid_torus_family_has_proved_local_kernel(self):
        for balls in (1, 2, 3, 8):
            fixture = capped_bipyramid_chain(balls)
            kernel = PreparedSectorSource(fixture['triangulation']).build(fixture['allowed_types'])
            blocks, zero = coordinate_blocks(kernel.basis, len(kernel.support))
            self.assertEqual(zero, ())
            self.assertEqual(len(kernel.prepared['tetrahedra']), 9 + 3 * balls)
            self.assertEqual(len(kernel.basis), 2 * balls)
            self.assertEqual(len(_hyperplanes(kernel, 'quadrilateral', lambda: None)), 3 * balls)
            self.assertEqual([block.indices for block in blocks],
                             [tuple(range(3 * i, 3 * i + 3)) for i in range(balls)])
            for block in blocks:
                self.assertEqual(block.basis, ((-1, 1, 0), (1, 0, 1)))
            stats = {}
            rays = list(block_sector_rays(kernel, stats=stats))
            self.assertEqual(stats['bases_attempted'], 3 * balls)
            self.assertEqual(len(rays), 2 * balls)
            for surface in rays:
                self.assertEqual(_coordinates(kernel.prepared, surface, lambda: None)
                                 ['euler_characteristic'], 1)
            if balls <= 3:
                old_stats = {}
                old = list(sector_rays(kernel, phase='quadrilateral', stats=old_stats))
                self.assertEqual(ray_set(rays), ray_set(old))
                self.assertEqual(old_stats['bases_attempted'], comb(3 * balls, 2 * balls - 1))
        # The square-equator variant has four irredundant coordinate facets
        # in each three-dimensional Q factor; redundancy removal cannot
        # eliminate its exponential global-subset enumeration obstruction.
        for balls in (1, 2, 5):
            fixture = capped_bipyramid_chain(balls, equator=4)
            kernel = PreparedSectorSource(fixture['triangulation']).build(fixture['allowed_types'])
            stats = {}
            rays = list(block_sector_rays(kernel, stats=stats))
            self.assertEqual(len(kernel.basis), 3 * balls)
            self.assertEqual(stats['block_nullities'], [3] * balls)
            self.assertEqual(stats['bases_attempted'], 6 * balls)
            self.assertEqual(len(rays), 4 * balls)
            if balls <= 2:
                old_stats = {}
                old = list(sector_rays(kernel, phase='quadrilateral', stats=old_stats))
                self.assertEqual(ray_set(rays), ray_set(old))
                self.assertEqual(old_stats['bases_attempted'], comb(4 * balls, 3 * balls - 1))

    def test_all_small_source_sectors_match_independent_dense_oracle(self):
        raw = fibonacci_solid_torus(3)
        source = PreparedSectorSource(raw)
        count = 0
        for types in product((-1, 0, 1, 2), repeat=3):
            support = [(i, typ) for i, typ in enumerate(types) if typ >= 0]
            kernel = source.build(support)
            model = dense_sector_model(raw, support)
            for phase in ('quadrilateral', 'standard'):
                actual = list(block_sector_rays(kernel, phase=phase))
                expected = [rows for rows, _ in dense_reference_rays(model, phase).values()]
                self.assertEqual(ray_set(actual), ray_set(expected), (types, phase))
                self.assertEqual(len(actual), len(ray_set(actual)), (types, phase))
            count += 1
        self.assertEqual(count, 64)

    def test_block_negative_certificate_replays_without_producer(self):
        raw = fibonacci_solid_torus(9)
        support = [(i, (0, 2, 1)[i % 3]) for i in range(9)]
        result = screen_sector_blocks(raw, support)
        self.assertEqual(result['status'], 'NO_POSITIVE_EULER')
        self.assertGreater(len(result['certificate']['blocks']), 1)
        with patch('fastunknot.sector_blocks.coordinate_blocks', side_effect=AssertionError('producer disabled')):
            self.assertTrue(verify_block_euler(raw, result['certificate']))
        damaged = deepcopy(result['certificate'])
        damaged['blocks'].pop()
        self.assertFalse(verify_block_euler(raw, damaged))
        damaged = deepcopy(result['certificate'])
        damaged['blocks'][0]['indices'].append(damaged['blocks'][0]['indices'][0])
        self.assertFalse(verify_block_euler(raw, damaged))
        damaged = deepcopy(result['certificate'])
        damaged['source_sha256'] = '0' * 64
        self.assertFalse(verify_block_euler(raw, damaged))

    def test_complete_ray_certificates_and_genuine_cross_block_standard_ray(self):
        fixture = capped_bipyramid_chain(2)
        raw, support = fixture['triangulation'], fixture['allowed_types']
        quad = certify_sector_block_rays(raw, support, phase='quadrilateral')
        standard = certify_sector_block_rays(raw, support, phase='standard')
        self.assertEqual(len(quad['rays']), 4)
        self.assertEqual(len(standard['rays']), 5)
        self.assertEqual(len(quad['certificate']['blocks']), 2)
        self.assertEqual(len(standard['certificate']['blocks']), 1)
        mixed = (1, 0, 1, 0, 1, 1)
        self.assertIn(mixed, {tuple(rows[t][4 + typ] for t, typ in support)
                              for rows in standard['rays']})
        with patch('fastunknot.sector_blocks.coordinate_blocks', side_effect=AssertionError('producer disabled')):
            self.assertTrue(verify_block_ray_certificate(raw, quad['certificate']))
            self.assertTrue(verify_block_ray_certificate(raw, standard['certificate']))
        forged = deepcopy(quad['certificate'])
        forged['phase'] = 'standard'
        self.assertFalse(verify_block_ray_certificate(raw, forged))
        forged = deepcopy(quad['certificate'])
        forged['blocks'][0]['quadrilaterals'].pop()
        self.assertFalse(verify_block_ray_certificate(raw, forged))
        forged = deepcopy(quad['certificate'])
        forged['blocks'][0]['quadrilaterals'].append(forged['blocks'][0]['quadrilaterals'][0])
        self.assertFalse(verify_block_ray_certificate(raw, forged))
        transported = deepcopy(quad['certificate'])
        for block in transported['blocks']:
            block['quadrilaterals'] = [[hex(value) for value in row]
                                       for row in block['quadrilaterals']]
        self.assertTrue(verify_block_ray_certificate(raw, transported))

    def test_negative_certificate_rejects_an_unsound_fine_partition(self):
        # Splitting one true matching block into single coordinates would
        # discard positive feasible dependencies, even if every singleton
        # sector individually contains no nonzero Q vector.
        fixture = capped_bipyramid_chain(1)
        raw, support = fixture['triangulation'], fixture['allowed_types']
        from fastunknot.normal_sector import _source_hash
        blocks = []
        for i, item in enumerate(support):
            local = screen_sector_blocks(raw, [item])
            self.assertEqual(local['status'], 'NO_POSITIVE_EULER')
            blocks.append(dict(indices=[i], certificate=dict(
                schema='normal-sector-exhaustion-v1', source_sha256=_source_hash(raw),
                allowed_types=[list(item)], phase='quadrilateral',
                status='NO_POSITIVE_EULER', rays=[])))
        forged = dict(schema='normal-sector-block-euler-v1', source_sha256=_source_hash(raw),
                      allowed_types=[list(item) for item in support], blocks=blocks)
        self.assertFalse(verify_block_euler(raw, forged))

    def test_positive_certificate_checks_source_canonicality_and_euler(self):
        fixture = capped_bipyramid_chain(3)
        raw = fixture['triangulation']
        result = screen_sector_blocks(raw, fixture['allowed_types'])
        self.assertEqual(result['status'], 'POSITIVE_EULER')
        self.assertTrue(verify_block_euler(raw, result['certificate']))
        damaged = deepcopy(result['certificate'])
        damaged['coordinates'] = [[0] * 7 for _ in raw['tetrahedra']]
        self.assertFalse(verify_block_euler(raw, damaged))
        # Adding one complete vertex link preserves matching and raises Euler,
        # but the certificate promises canonical coordinates.
        damaged = deepcopy(result['certificate'])
        model = dense_sector_model(raw, fixture['allowed_types'])
        for c in next(iter(model['groups'].values())):
            damaged['coordinates'][c // 4][c % 4] += 1
        self.assertFalse(verify_block_euler(raw, damaged))

    def test_budget_and_callback_cannot_produce_partial_exhaustion(self):
        fixture = capped_bipyramid_chain(2)
        raw, support = fixture['triangulation'], fixture['allowed_types']
        result = screen_sector_blocks(raw, support, max_bases=0)
        self.assertEqual(result['status'], 'INCONCLUSIVE')
        self.assertNotIn('certificate', result)
        with self.assertRaises(SearchLimit):
            enumerate_sector_blocks(raw, support, max_bases=1)
        count = 0

        def stop():
            nonlocal count
            count += 1
            if count > 20:
                raise InterruptedError('cancelled')

        with self.assertRaises(InterruptedError):
            screen_sector_blocks(raw, support, check=stop)


if __name__ == '__main__':
    unittest.main()
