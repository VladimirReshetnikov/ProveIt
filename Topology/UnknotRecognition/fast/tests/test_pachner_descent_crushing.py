"""Versioned strict macros, genuine diagram proofs, and shared allowances."""
from contextlib import ExitStack
from copy import deepcopy
import unittest
from unittest.mock import patch

from fastunknot.diagram import Diagram
from fastunknot.factored_crushing import recognize_factored_by_crushing
from fastunknot.factored_crushing_verify import verify_factored_crushing_recognition
from fastunknot.normal_crushing_chain import verify_crushing_chain
from fastunknot.normal_crushing_search import recognize_by_crushing, verify_crushing_recognition
from fastunknot.normal_pachner_descent import reduce_pachner_descent_once
from fastunknot.pachner23 import pachner_23
from normal_orbit_research.fixtures import layered_torus


OPTIONS = dict(sector_method='transversal', transversal_candidate_policy='conflicts',
               unlayer_boundary=True, reduce_pachner32=True, reduce_pachner_descent=True)
REDUCTIONS = ('crushing_steps', 'boundary_unlayerings', 'pachner32_moves',
              'pachner_descent_macros')


class PachnerDescentCrushingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.trefoil = Diagram.from_braid(2, [1, 1, 1])
        cls.result = recognize_by_crushing(cls.trefoil, **OPTIONS)

    def test_genuine_complete_proof_and_producer_free_replay(self):
        result = self.result
        self.assertEqual(result['status'], 'KNOTTED')
        chain = result['certificate']['chain']
        self.assertEqual(chain['schema'], 'diagram-crushing-v4')
        self.assertEqual(len(chain['steps']), sum(result['stats'].get(k, 0) for k in REDUCTIONS))
        macros = [s for s in chain['steps'] if s['schema'] == 'normal-pachner-descent-v1']
        self.assertGreater(len(macros), 0)
        self.assertEqual(len(macros), result['stats']['pachner_descent_macros'])
        upward = sum(s['transport']['move']['schema'] == 'pachner-23-v1'
                     for m in macros for s in m['certificate']['moves'])
        downward = sum(s['transport']['move']['schema'] == 'pachner-32-v1'
                       for m in macros for s in m['certificate']['moves'])
        self.assertEqual(upward, result['stats']['pachner_descent_upward_moves'])
        self.assertEqual(downward, result['stats']['pachner_descent_downward_moves'])
        self.assertGreater(upward, 0)
        with patch('fastunknot.normal_pachner_descent.reduce_pachner_descent_once', side_effect=AssertionError), \
             patch('fastunknot.pachner_cover_search.find_pachner_descent', side_effect=AssertionError), \
             patch('fastunknot.pachner23.pachner_23', side_effect=AssertionError), \
             patch('fastunknot.pachner32.pachner_32', side_effect=AssertionError):
            self.assertTrue(verify_crushing_recognition(self.trefoil, result['certificate']))

    def test_old_chain_versions_reject_macros_and_source_corruption(self):
        for version in ('diagram-crushing-v1', 'diagram-crushing-v2', 'diagram-crushing-v3'):
            bad = deepcopy(self.result['certificate'])
            bad['chain']['schema'] = version
            self.assertFalse(verify_crushing_recognition(self.trefoil, bad))
        bad = deepcopy(self.result['certificate'])
        step = next(s for s in bad['chain']['steps'] if s['schema'] == 'normal-pachner-descent-v1')
        step['source_sha256'] = '0'*64
        self.assertFalse(verify_crushing_recognition(self.trefoil, bad))

    def test_default_false_preserves_all_previous_schemas_and_shapes(self):
        circle = Diagram.from_pd([])
        for flags, schema in (({}, 'diagram-crushing-v1'),
                              ({'unlayer_boundary': True}, 'diagram-crushing-v2'),
                              ({'reduce_pachner32': True}, 'diagram-crushing-v3')):
            baseline = recognize_by_crushing(circle, **flags)
            self.assertEqual(baseline, recognize_by_crushing(
                circle, reduce_pachner_descent=False, **flags))
            self.assertEqual(baseline['certificate']['chain']['schema'], schema)
            self.assertFalse(any(k.startswith('pachner_descent_') for k in baseline['stats']))
        enabled = recognize_by_crushing(circle, **OPTIONS)
        self.assertEqual(enabled['status'], 'UNKNOT')
        self.assertEqual(enabled['certificate']['chain']['schema'], 'diagram-crushing-v4')
        self.assertEqual(enabled['stats']['pachner_descent_calls'], 0)
        self.assertTrue(verify_crushing_recognition(circle, enabled['certificate']))
        self.assertNotIn('pachner_descent_macros', recognize_factored_by_crushing(circle)['stats'])

    def test_strict_flag_validation_before_discovery(self):
        with patch('fastunknot.diagram_exterior.diagram_exterior', side_effect=AssertionError):
            for function in (recognize_by_crushing, recognize_factored_by_crushing):
                for value in (0, 1, None, 'yes', [], {}):
                    with self.subTest(function=function.__name__, value=value), self.assertRaises(ValueError):
                        function(Diagram.from_pd([]), reduce_pachner_descent=value)

    def source_harness(self, source):
        # Only the diagram/source premise is stubbed. The genuine local moves,
        # manifold checks and chain replay test scheduling and budget semantics.
        stack = ExitStack()
        stack.enter_context(patch('fastunknot.diagram_exterior.diagram_exterior', return_value=source))
        stack.enter_context(patch('fastunknot.diagram_exterior_verify.verify_diagram_exterior', return_value=True))
        stack.enter_context(patch('fastunknot.normal_crushing_chain.verify_diagram_exterior', return_value=True))
        return stack

    def test_macro_unlayer_terminal_budget_and_denied_search_diagnostics(self):
        source = pachner_23(layered_torus(2)[0], 0, 0)['triangulation']
        circle = Diagram.from_pd([])
        with self.source_harness(source):
            for cap in range(4):
                result = recognize_by_crushing(circle, **dict(
                    OPTIONS, reduce_pachner32=False, max_crushes=cap))
                chain = result['certificate']['chain'] if result['status'] == 'UNKNOT' else result['partial_chain']
                self.assertEqual(len(chain['steps']), cap)
                self.assertEqual(result['stats']['pachner_descent_macros'], int(cap >= 1))
                self.assertEqual(result['stats']['pachner_descent_upward_moves'], 0)
                self.assertEqual(result['stats']['pachner_descent_downward_moves'], int(cap >= 1))
                self.assertEqual(result['stats']['boundary_unlayerings'], int(cap >= 2))
                self.assertEqual(result['stats']['crushing_steps'], int(cap >= 3))
                self.assertGreater(result['stats']['pachner_descent_work'], 0)
                self.assertEqual(result['status'], 'UNKNOT' if cap == 3 else 'INCONCLUSIVE')
                self.assertTrue(verify_crushing_chain(circle, chain))
        self.assertFalse(verify_crushing_chain(circle, chain))

    def test_independent_rejection_and_unexpected_status(self):
        source = pachner_23(layered_torus(2)[0], 0, 0)['triangulation']
        broken = reduce_pachner_descent_once(source)
        broken['certificate']['source_sha256'] = '0'*64
        with self.source_harness(source), patch(
                'fastunknot.normal_pachner_descent.reduce_pachner_descent_once', return_value=broken):
            with self.assertRaisesRegex(ArithmeticError, 'independent Pachner descent replay failed'):
                recognize_by_crushing(Diagram.from_pd([]), **dict(OPTIONS, reduce_pachner32=False))
        broken['status'] = 'INCONCLUSIVE'
        with self.source_harness(source), patch(
                'fastunknot.normal_pachner_descent.reduce_pachner_descent_once', return_value=broken):
            with self.assertRaisesRegex(ArithmeticError, 'unexpected Pachner descent outcome'):
                recognize_by_crushing(Diagram.from_pd([]), **dict(OPTIONS, reduce_pachner32=False))

    def test_genuine_partial_factor_budget_counts_macro_once(self):
        diagram = Diagram.from_braid(3, [1, 1, 1, 2, 2, 2])
        result = recognize_factored_by_crushing(diagram, **dict(OPTIONS, max_crushes=15, max_tree_nodes=0))
        self.assertEqual(result['status'], 'INCONCLUSIVE')
        self.assertEqual(result['stats']['factors_attempted'], 2)
        self.assertEqual(result['stats']['crushing_steps'], 12)
        self.assertEqual(result['stats']['pachner32_moves'], 2)
        self.assertEqual(result['stats']['pachner_descent_macros'], 1)
        self.assertEqual(result['stats']['pachner_descent_upward_moves'], 1)
        self.assertEqual(result['stats']['pachner_descent_downward_moves'], 2)
        self.assertEqual(sum(result['stats'].get(k, 0) for k in REDUCTIONS), 15)
        self.assertEqual(len(result['factor_results'][1]['result']['partial_chain']['steps']), 0)
        for attempt in result['factor_results']:
            factor = Diagram.from_pd(result['factor_pds'][attempt['factor_index']])
            self.assertTrue(verify_crushing_chain(factor, attempt['result']['partial_chain']))

    def test_genuine_factored_negative_child_contains_macro(self):
        diagram = Diagram.from_braid(3, [1, 1, 1, 2, 2, 2])
        result = recognize_factored_by_crushing(diagram, **OPTIONS)
        self.assertEqual(result['status'], 'KNOTTED')
        self.assertEqual(result['stats']['factors_attempted'], 1)
        self.assertGreater(result['stats']['pachner_descent_macros'], 0)
        self.assertTrue(verify_factored_crushing_recognition(diagram, result['certificate']))


if __name__ == '__main__':
    unittest.main()
