"""Authenticated transversal recognition and budgets across strict crushes."""
from copy import deepcopy
import unittest
from unittest.mock import patch

from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_chain import verify_crushing_chain
from fastunknot.normal_crushing_search import recognize_by_crushing, verify_crushing_recognition
from fastunknot.normal_euler_transversal import search_euler_transversal
from fastunknot.normal_sector import SearchLimit


class CrushingEulerTransversalTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.circle = Diagram.from_pd([])
        cls.trefoil = Diagram.from_braid(2, [1, 1, 1])
        cls.positive = recognize_by_crushing(cls.circle, sector_method='transversal',
                                           reduce_vertices=False)
        cls.negative = recognize_by_crushing(cls.trefoil, sector_method='transversal')

    def test_complete_positive_and_negative_diagram_certificates(self):
        for diagram, result, status, schema in (
                (self.circle, self.positive, 'UNKNOT', 'diagram-crushing-recognition-v1'),
                (self.trefoil, self.negative, 'KNOTTED', 'diagram-crushing-recognition-v2')):
            self.assertEqual(result['status'], status)
            self.assertEqual(result['certificate']['schema'], schema)
            self.assertTrue(verify_crushing_recognition(diagram, result['certificate']))
            self.assertGreater(result['stats']['nodes_attempted'], 0)
            self.assertGreater(result['stats']['hitting_subsets_tested'], 0)
            self.assertEqual(result['stats']['sectors_attempted'], 0)
            self.assertEqual(result['stats']['bases_attempted'], 0)
        proof = self.negative['certificate']['exhaustion']
        count = len(self.negative['certificate']['chain']['triangulation']['tetrahedra'])
        self.assertEqual(proof['allowed_types'], [[t, q] for t in range(count) for q in range(3)])
        self.assertGreater(self.negative['stats']['transversal_restarts'], 0)
        self.assertGreater(self.negative['stats']['nodes_attempted'], len(proof['nodes']))

    def test_independent_replay_needs_no_search_and_rejects_partial_coverage(self):
        with patch('fastunknot.normal_euler_transversal.search_euler_transversal',
                   side_effect=AssertionError('discovery during independent replay')):
            for diagram, result in ((self.circle, self.positive), (self.trefoil, self.negative)):
                self.assertTrue(verify_crushing_recognition(diagram, result['certificate']))
        for mutation in ('node', 'mask', 'chain'):
            proof = deepcopy(self.negative['certificate'])
            if mutation == 'node':
                proof['exhaustion']['nodes'].pop()
            elif mutation == 'mask':
                proof['exhaustion']['allowed_types'].pop()
            else:
                proof['chain']['steps'].pop()
            self.assertFalse(verify_crushing_recognition(self.trefoil, proof), mutation)

    def test_zero_caps_return_only_authenticated_partial_chains(self):
        for option in ('max_tree_nodes', 'max_pivots', 'max_anchors',
                       'max_hitting_subsets', 'max_crushes'):
            result = recognize_by_crushing(self.circle, sector_method='transversal',
                reduce_vertices=False, lp_strategy='anchors', **{option: 0})
            self.assertEqual(result['status'], 'INCONCLUSIVE', option)
            self.assertNotIn('certificate', result)
            self.assertTrue(verify_crushing_chain(self.circle, result['partial_chain']))
        result = recognize_by_crushing(self.circle, sector_method='transversal',
            reduce_vertices=False, max_sectors=0, max_bases=0)
        self.assertEqual(result['status'], 'UNKNOT')

    def test_all_search_caps_are_shared_across_genuine_crushing_successors(self):
        def reduction_first(source, **kwargs):
            # A genuine positive first-source face forces multiple native
            # search/extraction/crushing steps before the terminal certificate.
            allowed = [[t, 2] for t in range(5)] if len(source['tetrahedra']) == 5 else None
            return search_euler_transversal(source, allowed, **kwargs)

        config = dict(sector_method='transversal', lp_strategy='anchors',
                      reduce_vertices=False, max_tree_nodes=None, max_pivots=None,
                      max_anchors=None, max_hitting_subsets=None)
        with patch('fastunknot.normal_euler_transversal.search_euler_transversal', reduction_first):
            full = recognize_by_crushing(self.circle, **config)
            self.assertEqual(full['status'], 'UNKNOT')
            self.assertEqual(full['stats']['crushing_steps'], 3)
            self.assertTrue(verify_crushing_recognition(self.circle, full['certificate']))
            for cap, counter in (('max_tree_nodes', 'nodes_attempted'),
                                 ('max_pivots', 'lp_pivots'),
                                 ('max_anchors', 'anchors_tested'),
                                 ('max_hitting_subsets', 'hitting_subsets_tested'),
                                 ('max_crushes', 'crushing_steps')):
                self.assertEqual(full['stats'][counter], 3)
                for limit in (1, 2):
                    result = recognize_by_crushing(self.circle, **dict(config, **{cap: limit}))
                    self.assertEqual(result['status'], 'INCONCLUSIVE', (cap, limit))
                    self.assertEqual(result['stats'][counter], limit)
                    self.assertEqual(result['stats']['crushing_steps'], limit)
                    self.assertTrue(verify_crushing_chain(self.circle, result['partial_chain']))

    def test_strict_subset_cap_and_source_model_requirement(self):
        for value in (True, False, -1, 1.5, '1', [], {}):
            with self.subTest(value=value), self.assertRaises(ValueError):
                recognize_by_crushing(self.circle, sector_method='transversal',
                                      max_hitting_subsets=value)
        with self.assertRaises(ValueError):
            recognize_by_crushing(self.circle, sector_method='transversal', tree_model='restricted')

    def test_caller_exceptions_inside_learning_escape_with_identity(self):
        class StopNow(BaseException):
            pass
        for error in (SearchLimit('caller'), ValueError('caller'), StopNow('caller')):
            entered = False

            def producer(source, *, check, **kwargs):
                nonlocal entered
                entered = True
                check()
                raise AssertionError('callback must interrupt learning')

            def callback():
                if entered:
                    raise error

            with patch('fastunknot.normal_euler_transversal.search_euler_transversal', producer):
                with self.assertRaises(type(error)) as seen:
                    recognize_by_crushing(self.circle, sector_method='transversal',
                        reduce_vertices=False, check=callback)
                self.assertIs(seen.exception, error)


if __name__ == '__main__':
    unittest.main()
