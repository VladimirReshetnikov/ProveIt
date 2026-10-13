"""Focused evidence-tamper controls; no discovery solver is executed."""
from copy import deepcopy
import unittest
from .common import load, verify_provenance
from .replay import audit, check_hypergraph, verify_factors
from .standard import observation


class ReplayTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.state = load('generation/tt-state.json.gz')
        cls.key = cls.state['source_sha256']
        cls.source = cls.state['stage_sources'][cls.key]
        cls.rays = cls.state['raw_rays'][cls.key]

    def test_retained_original_bytes(self):
        self.assertEqual(verify_provenance()['schema'], 'conflict-composition-generation-v1')

    def test_factor_identity_requires_slot_preserving_map(self):
        fixtures = load('generation/fixtures.json.gz')
        verify_factors(self.state, fixtures)
        mapping = fixtures['records'][0]['factors'][0]['base_edge_to_factor_edge']
        mapping[0], mapping[1] = mapping[1], mapping[0]
        with self.assertRaises(AssertionError):
            verify_factors(self.state, fixtures)

    def test_core_and_every_four_subset(self):
        graph = check_hypergraph([r['conflicts'] for r in self.rays])
        self.assertEqual(graph['source_h_lower_bound'], 5)
        self.assertIsNone(graph['source_h_upper_bound'])
        self.assertEqual(graph['four_subsets_excluded'], 8855)

    def test_core_cannot_be_replaced_by_claimed_conflicts(self):
        edges = [r['conflicts'][:] for r in self.rays]
        edges[6] = [3]
        with self.assertRaises(AssertionError):
            check_hypergraph(edges)

    def test_original_matching_and_exact_integer_controls(self):
        rows = deepcopy(self.rays[6]['coordinates'])
        obs, ranks = observation(self.source, rows)
        self.assertEqual(obs['conflicts'], [5])
        self.assertEqual(ranks['q_support_nullity'], 1)
        rows[0][0] += 1
        with self.assertRaises(AssertionError):
            observation(self.source, rows)
        rows = deepcopy(self.rays[6]['coordinates'])
        rows[0][0] = bool(rows[0][0])
        with self.assertRaises(AssertionError):
            observation(self.source, rows)

    def test_nonprimitive_or_unpeeled_coordinates_rejected(self):
        rows = [[2*x for x in row] for row in self.rays[6]['coordinates']]
        with self.assertRaises(AssertionError):
            observation(self.source, rows)
        rows = deepcopy(self.rays[6]['coordinates'])
        for row in rows:
            for j in range(4):
                row[j] += 1
        with self.assertRaises(AssertionError):
            observation(self.source, rows)

    def test_caller_exception_identity(self):
        class Stop(Exception):
            pass
        error = Stop('test interruption')
        def check():
            raise error
        with self.assertRaises(Stop) as caught:
            audit(check=check)
        self.assertIs(caught.exception, error)


if __name__ == '__main__':
    unittest.main()
