"""Focused rejection controls for the retained algebra and exact collar maps."""
from copy import deepcopy
from math import gcd
import unittest

from .common import load, verify_generation_provenance
from .replay import check_layer, observation


class ReplayTests(unittest.TestCase):
    def setUp(self):
        self.fixture = load('lower_witnesses.json')['records'][0]
        self.record = load('provenance/layer-refuter.json')['records'][0]

    def test_smallest_refuter(self):
        first = self.record['steps'][0]
        check_layer(self.fixture['source'], first)
        obs, proof = observation(first['source'], first['coordinates'])
        self.assertEqual(obs['conflicts'], [0, 5])
        self.assertEqual(obs['boundary_edge_tetrahedra'], [2, 3, 6, 9, 10])
        self.assertEqual(proof, dict(standard_columns=54, standard_rank=52,
            triangle_columns=44, triangle_rank=43,
            triangle_kernel_dimension=1, q_support_nullity=1))

    def test_noninteger_or_broken_matching_rejected(self):
        rows = deepcopy(self.record['initial_coordinates'])
        rows[0][0] = True
        with self.assertRaises(AssertionError):
            observation(self.fixture['source'], rows)
        rows[0][0] = self.record['initial_coordinates'][0][0]+1
        with self.assertRaises(AssertionError):
            observation(self.fixture['source'], rows)

    def test_noncanonical_vertex_link_addition_rejected(self):
        rows = [[x+int(j < 4) for j, x in enumerate(row)]
                for row in self.record['initial_coordinates']]
        with self.assertRaises(AssertionError):
            observation(self.fixture['source'], rows)

    def test_nonprimitive_ray_rejected(self):
        rows = [[2*x for x in row] for row in self.record['initial_coordinates']]
        with self.assertRaises(AssertionError):
            observation(self.fixture['source'], rows)

    def test_nonextreme_matching_sum_rejected(self):
        a, b = [w['coordinates'] for w in self.fixture['witnesses'][:2]]
        rows = [[x+y for x, y in zip(ra, rb)] for ra, rb in zip(a, b)]
        minimum = min(x for row in rows for x in row[:4])
        rows = [[x-minimum*int(j < 4) for j, x in enumerate(row)] for row in rows]
        self.assertEqual(gcd(*(x for row in rows for x in row[4:])), 1)
        # The two distinct rays give a >=2-dimensional supported space;
        # matching/nonnegativity/canonicality alone must not certify a ray.
        with self.assertRaises(AssertionError):
            observation(self.fixture['source'], rows)

    def test_wrong_declared_layer_edge_rejected(self):
        step = deepcopy(self.record['steps'][0])
        step['flipped_original_local_edge'] = [6, 3]
        with self.assertRaises(AssertionError):
            check_layer(self.fixture['source'], step)

    def test_historical_inputs_pinned(self):
        verify_generation_provenance()


if __name__ == '__main__':
    unittest.main()
