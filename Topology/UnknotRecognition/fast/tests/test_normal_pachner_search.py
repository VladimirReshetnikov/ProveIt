from copy import deepcopy
import unittest
from unittest.mock import patch

from fastunknot import Diagram
from fastunknot.normal_pachner_search import pachner_seed_decide
from fastunknot.normal_transport_verify import verify_transport_disk_certificate
from fastunknot.pachner_regions import search_pachner_regions
from fastunknot.normal_cocycle import CocycleLimit, rank_one_cocycle_seed
from fastunknot.normal_surface_geometry import NormalOrbitError
from fastunknot.diagram_exterior import diagram_exterior


class SourceBoundSearchTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.unknot = Diagram.from_braid(2, [1])
        cls.answer = pachner_seed_decide(cls.unknot, max_work=None)
        cls.raw = diagram_exterior(cls.unknot)
        cls.heights = rank_one_cocycle_seed(cls.raw)['heights']

    def test_positive_and_independent_source_binding(self):
        self.assertEqual(self.answer['status'], 'UNKNOT')
        proof = self.answer['certificate']
        self.assertTrue(verify_transport_disk_certificate(self.unknot, proof))
        self.assertFalse(verify_transport_disk_certificate(
            Diagram.from_braid(2, [1, 1, 1]), proof))
        with patch('fastunknot.pachner_commitments.search_pachner_endpoints',
                   side_effect=AssertionError), \
             patch('fastunknot.diagram_exterior.diagram_exterior',
                   side_effect=AssertionError), \
             patch('fastunknot.normal_cocycle.rank_one_cocycle_seed',
                   side_effect=AssertionError):
            self.assertTrue(verify_transport_disk_certificate(self.unknot, proof))
        bad = deepcopy(proof)
        bad['coordinates'][0][0] += 1
        self.assertFalse(verify_transport_disk_certificate(self.unknot, bad))

    def test_source_options_and_empty_region(self):
        for options in ({'shellings': True}, {'optimize': True},
                        {'max_region_size': 0, 'max_components': 0},
                        {'method': 'commitments'}, {'method': 'naive'}):
            answer = pachner_seed_decide(self.unknot, max_work=None, **options)
            self.assertEqual(answer['status'], 'UNKNOT')
            self.assertTrue(verify_transport_disk_certificate(
                self.unknot, answer['certificate']))

    def test_exhaustion_is_not_a_negative_knot_verdict(self):
        knot = Diagram.from_braid(2, [1, 1, 1])
        for size in (None, 0):
            answer = pachner_seed_decide(knot, max_region_size=size,
                max_nodes=5, shellings=True, max_work=None)
            self.assertEqual(answer['status'], 'INCONCLUSIVE')
            self.assertNotIn('certificate', answer)
            self.assertIn(answer['bounded_search_status'],
                          ('COMPLETE_BOUNDED_FAMILY', 'COMPLETE_BOUNDED_REGIONS', 'COMPLETE_BOUNDED_COVER_FAMILY'))

    def test_limits_and_input_validation(self):
        for options in ({'max_nodes': 0}, {'max_work': 0},
                        {'max_region_size': 0, 'max_nodes': 0}):
            answer = pachner_seed_decide(self.unknot, **options)
            self.assertEqual(answer['status'], 'INCONCLUSIVE')
            self.assertNotIn('certificate', answer)
        for options in ({'max_upward': True}, {'max_region_size': -1},
                        {'max_components': -1}, {'method': 'bad'},
                        {'shellings': 1}, {'max_cycles': -1}):
            with self.assertRaises(ValueError):
                pachner_seed_decide(self.unknot, **options)

    def test_caller_exception_identity(self):
        for error_type in (RuntimeError, CocycleLimit, NormalOrbitError, ValueError):
            error = error_type('caller cancellation')
            def cancel():
                raise error
            with self.assertRaises(error_type) as caught:
                pachner_seed_decide(self.unknot, check=cancel)
            self.assertIs(caught.exception, error)
            with self.assertRaises(error_type) as caught:
                search_pachner_regions(self.raw, self.heights,
                    max_region_size=0, seek_disc=False, check=cancel)
            self.assertIs(caught.exception, error)
            def endpoint(proof):
                raise error
            with self.assertRaises(error_type) as caught:
                search_pachner_regions(self.raw, self.heights,
                    max_region_size=0, seek_disc=False, endpoint=endpoint)
            self.assertIs(caught.exception, error)


if __name__ == '__main__':
    unittest.main()
