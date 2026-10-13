"""Diagram authentication, full-mask coverage and shared Euler-tree limits."""
from copy import deepcopy
import unittest
from unittest.mock import patch

from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_chain import verify_crushing_chain
from fastunknot.normal_crushing_search import recognize_by_crushing, verify_crushing_recognition
from fastunknot.normal_euler_tree_verify import verify_euler_branch_tree
from fastunknot.normal_sector import SearchLimit


class CrushingEulerTreeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.circle = Diagram.from_pd([])
        cls.trefoil = Diagram.from_braid(2, [1, 1, 1])
        cls.positive = recognize_by_crushing(cls.circle, sector_method='tree',
                                           reduce_vertices=False)
        cls.negative = recognize_by_crushing(cls.trefoil, sector_method='tree',
            max_tree_nodes=None, max_pivots=None, max_anchors=None)

    def test_actual_tree_search_recognizes_positive_and_negative_diagrams(self):
        for diagram, result, status, schema in (
                (self.circle, self.positive, 'UNKNOT', 'diagram-crushing-recognition-v1'),
                (self.trefoil, self.negative, 'KNOTTED', 'diagram-crushing-recognition-v2')):
            self.assertEqual(result['status'], status)
            self.assertEqual(result['certificate']['schema'], schema)
            self.assertTrue(verify_crushing_recognition(diagram, result['certificate']))
            self.assertGreater(result['stats']['nodes_attempted'], 0)
            self.assertEqual(result['stats']['sectors_attempted'], 0)
            self.assertEqual(result['stats']['bases_attempted'], 0)
        source = self.negative['certificate']['chain']['triangulation']
        proof = self.negative['certificate']['exhaustion']
        self.assertTrue(verify_euler_branch_tree(source, proof))
        self.assertEqual(proof['allowed_types'], [[t, q] for t in range(len(source['tetrahedra']))
                                                 for q in range(3)])
        self.assertGreater(self.negative['stats']['branch_splits'], 0)
        self.assertLess(len(proof['nodes']), 3**len(source['tetrahedra']))

    def test_replay_does_not_call_discovery(self):
        with patch('fastunknot.normal_euler_tree.search_euler_tree',
                   side_effect=AssertionError('producer must not run during replay')):
            self.assertTrue(verify_crushing_recognition(self.circle, self.positive['certificate']))
            self.assertTrue(verify_crushing_recognition(self.trefoil, self.negative['certificate']))

    def test_partial_root_mask_cannot_certify_global_knottedness(self):
        certificate = deepcopy(self.negative['certificate'])
        # Isolate the full-root gate even if a lower-level partial-mask tree
        # were valid; actual hostile leaf mutations are independently tested.
        certificate['exhaustion']['allowed_types'].pop()
        with patch('fastunknot.normal_crushing_search.verify_euler_branch_tree', return_value=True):
            self.assertFalse(verify_crushing_recognition(self.trefoil, certificate))

    def test_corrupt_tree_or_diagram_provenance_is_rejected(self):
        original = self.negative['certificate']
        for mutation in ('missing_node', 'extra_node', 'source', 'schema', 'status', 'chain'):
            certificate = deepcopy(original)
            if mutation == 'missing_node':
                certificate['exhaustion']['nodes'].pop()
            elif mutation == 'extra_node':
                certificate['exhaustion']['nodes'].append(deepcopy(certificate['exhaustion']['nodes'][-1]))
            elif mutation == 'source':
                certificate['exhaustion']['source_sha256'] = '0'*64
            elif mutation == 'schema':
                certificate['schema'] = 'diagram-crushing-recognition-v1'
            elif mutation == 'status':
                certificate['status'] = 'UNKNOT'
            else:
                certificate['chain']['steps'].pop()
            self.assertFalse(verify_crushing_recognition(self.trefoil, certificate), mutation)
        self.assertFalse(verify_crushing_recognition(self.circle, original))
        forged = deepcopy(self.positive['certificate'])
        forged['schema'] = 'diagram-crushing-recognition-v2'
        self.assertFalse(verify_crushing_recognition(self.circle, forged))

    def test_zero_tree_resources_are_inconclusive_and_unused_sector_caps_do_not_stop_tree(self):
        for name in ('max_tree_nodes', 'max_pivots', 'max_anchors', 'max_crushes'):
            result = recognize_by_crushing(self.circle, sector_method='tree',
                lp_strategy='anchors', reduce_vertices=False, **{name: 0})
            self.assertEqual(result['status'], 'INCONCLUSIVE', name)
            self.assertNotIn('certificate', result)
            self.assertTrue(verify_crushing_chain(self.circle, result['partial_chain']))
        result = recognize_by_crushing(self.circle, sector_method='tree',
            reduce_vertices=False, max_sectors=0, max_bases=0)
        self.assertEqual(result['status'], 'UNKNOT')
        for value in (True, False, -1, 1.5, '1', [], {}):
            with self.subTest(value=value), self.assertRaises(ValueError):
                recognize_by_crushing(self.circle, sector_method='tree', max_tree_nodes=value)

    def test_tree_limits_are_shared_across_actual_search_driven_crushes(self):
        from fastunknot.normal_euler_tree import search_euler_tree

        def reduction_first(source, **kwargs):
            # Select a genuine positive submask on the first source. Discovery,
            # extraction, geometry and every crushing proof remain native.
            allowed = [[t, 2] for t in range(5)] if len(source['tetrahedra']) == 5 else None
            return search_euler_tree(source, allowed, **kwargs)

        config = dict(sector_method='tree', lp_strategy='anchors', reduce_vertices=False,
                      max_tree_nodes=None, max_pivots=None, max_anchors=None)
        with patch('fastunknot.normal_euler_tree.search_euler_tree', reduction_first):
            full = recognize_by_crushing(self.circle, **config)
            self.assertEqual(full['status'], 'UNKNOT')
            self.assertEqual(full['stats']['crushing_steps'], 3)
            self.assertTrue(verify_crushing_recognition(self.circle, full['certificate']))
            for cap, counter in (('max_tree_nodes', 'nodes_attempted'),
                                 ('max_pivots', 'lp_pivots'),
                                 ('max_anchors', 'anchors_tested'),
                                 ('max_crushes', 'crushing_steps')):
                self.assertEqual(full['stats'][counter], 3)
                for limit in (1, 2):
                    with self.subTest(cap=cap, limit=limit):
                        result = recognize_by_crushing(self.circle, **dict(config, **{cap: limit}))
                        self.assertEqual(result['status'], 'INCONCLUSIVE')
                        self.assertEqual(result['stats'][counter], limit)
                        self.assertEqual(result['stats']['crushing_steps'], limit)
                        self.assertEqual(len(result['partial_chain']['triangulation']['tetrahedra']), 5-limit)
                        self.assertTrue(verify_crushing_chain(self.circle, result['partial_chain']))

    def test_caller_failures_inside_tree_discovery_escape_unchanged(self):
        class StopNow(BaseException):
            pass
        for error in (SearchLimit('caller'), ValueError('caller'), StopNow('caller')):
            entered = False

            def producer(source, *, check, **kwargs):
                nonlocal entered
                entered = True
                check()
                raise AssertionError('callback must stop this call')

            def callback():
                if entered:
                    raise error

            with patch('fastunknot.normal_euler_tree.search_euler_tree', producer):
                with self.assertRaises(type(error)) as caught:
                    recognize_by_crushing(self.circle, sector_method='tree',
                        reduce_vertices=False, check=callback)
                self.assertIs(caught.exception, error)


if __name__ == '__main__':
    unittest.main()
