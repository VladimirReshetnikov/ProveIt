"""Genuine recognition, versioned replay, and shared strict-reduction limits."""
from contextlib import ExitStack
from copy import deepcopy
import unittest
from unittest.mock import patch

from fastunknot.diagram import Diagram
from fastunknot.factored_crushing import recognize_factored_by_crushing
from fastunknot.factored_crushing_verify import verify_factored_crushing_recognition
from fastunknot.normal_crushing_chain import verify_crushing_chain
from fastunknot.normal_crushing_search import recognize_by_crushing, verify_crushing_recognition
from fastunknot.normal_pachner32 import reduce_pachner32_once
from fastunknot.pachner23 import pachner_23
from normal_orbit_research.fixtures import layered_torus


OPTIONS = dict(sector_method='transversal', transversal_candidate_policy='conflicts',
               unlayer_boundary=True, reduce_pachner32=True)


class PachnerCrushingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.genuine = []
        for name, diagram in (
                ('circle', Diagram.from_pd([])),
                ('trefoil', Diagram.from_braid(2, [1, 1, 1])),
                ('figure_eight', Diagram.from_braid(3, [1, -2, 1, -2])),
                ('TT', Diagram.from_braid(3, [1, 1, 1, 2, 2, 2]))):
            cls.genuine.append((name, diagram, recognize_by_crushing(diagram, **OPTIONS)))

    def test_genuine_complete_proofs_and_discovery_free_replay(self):
        for name, diagram, result in self.genuine:
            with self.subTest(name=name):
                self.assertEqual(result['status'], 'UNKNOT' if name == 'circle' else 'KNOTTED')
                chain = result['certificate']['chain']
                self.assertEqual(chain['schema'], 'diagram-crushing-v3')
                self.assertEqual(len(chain['steps']), sum(result['stats'].get(key, 0)
                    for key in ('crushing_steps', 'boundary_unlayerings', 'pachner32_moves')))
                if name != 'circle':
                    self.assertGreater(result['stats']['pachner32_moves'], 0)
                with patch('fastunknot.normal_pachner32.reduce_pachner32_once', side_effect=AssertionError), \
                     patch('fastunknot.pachner32.pachner_32', side_effect=AssertionError):
                    self.assertTrue(verify_crushing_recognition(diagram, result['certificate']))

    def test_legacy_chain_versions_reject_pachner_steps(self):
        _, diagram, result = self.genuine[1]
        for version in ('diagram-crushing-v1', 'diagram-crushing-v2'):
            bad = deepcopy(result['certificate'])
            bad['chain']['schema'] = version
            self.assertFalse(verify_crushing_recognition(diagram, bad))
        bad = deepcopy(result['certificate'])
        step = next(step for step in bad['chain']['steps'] if step['schema'] == 'normal-pachner-32-v1')
        step['source_sha256'] = '0'*64
        self.assertFalse(verify_crushing_recognition(diagram, bad))

    def test_disabled_policy_preserves_legacy_schema_and_result_shape(self):
        circle = Diagram.from_pd([])
        default = recognize_by_crushing(circle)
        self.assertEqual(default, recognize_by_crushing(circle, reduce_pachner32=False))
        self.assertEqual(default['certificate']['chain']['schema'], 'diagram-crushing-v1')
        self.assertFalse(any(key.startswith('pachner32_') for key in default['stats']))
        old = recognize_by_crushing(circle, unlayer_boundary=True)
        self.assertEqual(old['certificate']['chain']['schema'], 'diagram-crushing-v2')
        self.assertTrue(verify_crushing_recognition(circle, old['certificate']))
        factored = recognize_factored_by_crushing(circle)
        self.assertNotIn('pachner32_moves', factored['stats'])

    def test_strict_flag_validation_before_discovery(self):
        for function in (recognize_by_crushing, recognize_factored_by_crushing):
            for value in (0, 1, None, 'yes', [], {}):
                with self.subTest(function=function.__name__, value=value), self.assertRaises(ValueError):
                    function(Diagram.from_pd([]), reduce_pachner32=value)

    def source_harness(self, source):
        # Only the diagram-to-source premise is stubbed. Real local operations,
        # finite manifold checks and chain replay remain enabled. This controls
        # scheduling and accounting, not a genuine diagram authentication.
        stack = ExitStack()
        stack.enter_context(patch('fastunknot.diagram_exterior.diagram_exterior', return_value=source))
        stack.enter_context(patch('fastunknot.diagram_exterior_verify.verify_diagram_exterior', return_value=True))
        stack.enter_context(patch('fastunknot.normal_crushing_chain.verify_diagram_exterior', return_value=True))
        return stack

    def test_shared_cap_across_pachner_unlayer_and_terminal_crush(self):
        source = pachner_23(layered_torus(2)[0], 0, 0)['triangulation']
        circle = Diagram.from_pd([])
        with self.source_harness(source):
            for cap in range(4):
                result = recognize_by_crushing(circle, max_crushes=cap, **OPTIONS)
                chain = result['certificate']['chain'] if result['status'] == 'UNKNOT' else result['partial_chain']
                self.assertEqual(len(chain['steps']), cap)
                self.assertEqual(result['stats']['pachner32_moves'], int(cap >= 1))
                self.assertEqual(result['stats']['boundary_unlayerings'], int(cap >= 2))
                self.assertEqual(result['stats']['crushing_steps'], int(cap >= 3))
                self.assertEqual(result['status'], 'UNKNOT' if cap == 3 else 'INCONCLUSIVE')
                self.assertTrue(verify_crushing_chain(circle, chain))
        self.assertFalse(verify_crushing_chain(circle, chain))

    def test_bad_move_rejected_before_recording_partial_progress(self):
        source = pachner_23(layered_torus(2)[0], 0, 0)['triangulation']
        broken = reduce_pachner32_once(source)
        broken['certificate']['source_sha256'] = '0'*64
        with self.source_harness(source), patch(
                'fastunknot.normal_pachner32.reduce_pachner32_once', return_value=broken):
            with self.assertRaisesRegex(ArithmeticError, 'independent Pachner 3-2 replay failed'):
                recognize_by_crushing(Diagram.from_pd([]), max_crushes=1, **OPTIONS)

    def test_genuine_partial_factor_work_charges_pachner_moves(self):
        diagram = Diagram.from_braid(3, [1, 1, 1, 2, 2, 2])
        result = recognize_factored_by_crushing(diagram, max_crushes=13, max_tree_nodes=0, **OPTIONS)
        self.assertEqual(result['status'], 'INCONCLUSIVE')
        self.assertEqual(result['stats']['factors_attempted'], 2)
        self.assertEqual(result['stats']['crushing_steps'], 12)
        self.assertEqual(result['stats']['pachner32_moves'], 1)
        self.assertEqual(result['stats']['boundary_unlayerings'], 0)
        for attempt in result['factor_results']:
            factor = Diagram.from_pd(result['factor_pds'][attempt['factor_index']])
            self.assertTrue(verify_crushing_chain(factor, attempt['result']['partial_chain']))
        self.assertEqual(len(result['factor_results'][1]['result']['partial_chain']['steps']), 0)

    def test_genuine_factored_verdict_with_pachner_child(self):
        diagram = Diagram.from_braid(3, [1, 1, 1, 2, 2, 2])
        result = recognize_factored_by_crushing(diagram, **OPTIONS)
        self.assertEqual(result['status'], 'KNOTTED')
        self.assertEqual(result['stats']['factors_attempted'], 1)
        self.assertGreater(result['stats']['pachner32_moves'], 0)
        self.assertTrue(verify_factored_crushing_recognition(diagram, result['certificate']))


if __name__ == '__main__':
    unittest.main()
