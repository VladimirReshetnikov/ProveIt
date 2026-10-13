"""Direct native positives, narrow repair, and authenticated driver boundaries."""
from contextlib import ExitStack
from copy import deepcopy
import unittest
from unittest.mock import patch

from fastunknot.diagram import Diagram
from fastunknot.integer_codec import json_safe
from fastunknot.normal_crushing import (crush_normal_ray, _NonPrimitiveNormalPoint,
                                        _NonExtremeNormalPoint)
from fastunknot.normal_crushing_chain import verify_crushing_chain
from fastunknot.normal_crushing_search import recognize_by_crushing, verify_crushing_recognition
from fastunknot.normal_crushing_verify import verify_normal_crushing
from fastunknot.normal_euler import decide_sector_euler
from fastunknot.normal_euler_tree import search_euler_tree
from fastunknot.normal_euler_transversal import search_euler_transversal
from fastunknot.normal_euler_verify import verify_sector_euler_certificate
from fastunknot.normal_surface_geometry import _prepare, _coordinates, NormalOrbitError
from fastunknot.positive_ray import extract_positive_ray
from fastunknot import normal_vertex_reduction as vertex_module
from fastunknot.factored_crushing import recognize_factored_by_crushing
from fastunknot.factored_crushing_verify import verify_factored_crushing_recognition
from normal_orbit_research.fixtures import layered_torus, boundary_cap


class DirectCrushPositiveTests(unittest.TestCase):
    def setUp(self):
        self.circle = Diagram.from_pd([])
        self.one, self.ray = layered_torus(1)
        self.capped, _ = boundary_cap(self.one, self.ray)
        self.mixture = [[1, 1, 2, 2, 1, 0, 0], [1, 1, 0, 0, 3, 0, 0]]

    def options(self, method='tree', **updates):
        return dict(dict(sector_method=method, reduce_vertices=False, max_bases=0,
                         sector_order='canonical', tree_model='source',
                         transversal_candidate_policy='conflicts'), **updates)

    def source_harness(self, source):
        """Only diagram provenance is artificial; shelling and ray replay are real.

        Such a result is conditional supplied-source evidence. Tests below
        separately check that its purported diagram chain fails outside this
        harness. Genuine diagram controls never use these patches.
        """
        stack = ExitStack()
        stack.enter_context(patch('fastunknot.diagram_exterior.diagram_exterior', return_value=source))
        stack.enter_context(patch('fastunknot.diagram_exterior_verify.verify_diagram_exterior', return_value=True))
        stack.enter_context(patch('fastunknot.normal_crushing_chain.verify_diagram_exterior', return_value=True))
        stack.enter_context(patch('fastunknot.boundary_shellings.shell_boundary',
                                  return_value=dict(triangulation=source, moves=[])))
        return stack

    def inject_point(self, method, source, point, *, certify_lp=False):
        """Replace one returned positive point after an actual native query."""
        path, original = {
            'lp': ('fastunknot.normal_euler.decide_sector_euler', decide_sector_euler),
            'tree': ('fastunknot.normal_euler_tree.search_euler_tree', search_euler_tree),
            'transversal': ('fastunknot.normal_euler_transversal.search_euler_transversal', search_euler_transversal),
        }[method]

        def supplied(current, *args, **kwargs):
            answer = original(current, *args, **kwargs)
            if current == source and answer['status'] == 'POSITIVE_EULER':
                answer = deepcopy(answer)
                answer['coordinates'] = deepcopy(point)
                if certify_lp:
                    proof = answer['certificate']
                    proof['coordinates'] = deepcopy(point)
                    proof['quadrilaterals'] = [point[t][4+q] for t, q in proof['allowed_types']]
                    proof['euler_characteristic'] = _coordinates(
                        _prepare(source, lambda: None), point, lambda: None)['euler_characteristic']
                    self.assertTrue(verify_sector_euler_certificate(source, proof))
            return answer
        return patch(path, supplied)

    def assert_legacy_extraction_same(self, diagram, options, result):
        """Emulate the removed redundant step with real extraction and crushing."""
        def extract_first(source, rows, **kwargs):
            repaired = extract_positive_ray(source, rows, **kwargs)
            self.assertEqual(repaired['coordinates'], rows)
            self.assertEqual(repaired['stats']['descent_steps'], 0)
            return crush_normal_ray(source, repaired['coordinates'], **kwargs)
        with patch('fastunknot.normal_crushing.crush_normal_ray', extract_first) as old:
            reference = recognize_by_crushing(diagram, **options)
        self.assertEqual(reference, result)

    def test_real_flat_lp_anchors_envelope_bland_and_forced_fallback_skip_extraction(self):
        for strategy in ('anchors', 'envelope'):
            for policy, fast in (('bland', None), ('polynomial', 0)):
                with self.subTest(strategy=strategy, policy=policy), ExitStack() as stack:
                    # Forced fallback on the tiny supplied source tests the
                    # actual LP fallback without requiring a large uncapped
                    # whole-diagram ellipsoid run. Bland uses genuine provenance.
                    if policy == 'polynomial':
                        stack.enter_context(self.source_harness(self.one))
                    stack.enter_context(patch('fastunknot.positive_ray.extract_positive_ray',
                        side_effect=AssertionError('redundant driver extraction')))
                    options = self.options('lp', lp_strategy=strategy, lp_policy=policy,
                                           lp_fast_path_pivots=fast)
                    result = recognize_by_crushing(self.circle, **options)
                    self.assertEqual(result['status'], 'UNKNOT')
                    self.assertEqual(result['stats']['extraction_steps'], 0)
                    self.assertGreater(result['stats']['crushing_steps'], 0)
                    self.assertEqual(result['stats']['bases_attempted'], 0)
                    if policy == 'polynomial':
                        self.assertGreater(result['stats']['lp_fallbacks'], 0)
                    self.assertTrue(verify_crushing_recognition(self.circle, result['certificate']))
                    self.assert_legacy_extraction_same(self.circle, options, result)
                if policy == 'polynomial':
                    self.assertFalse(verify_crushing_recognition(self.circle, result['certificate']))

    def test_real_tree_and_transversal_native_points_skip_driver_extraction(self):
        for method in ('tree', 'transversal'):
            with self.subTest(method=method), patch('fastunknot.positive_ray.extract_positive_ray',
                    side_effect=AssertionError('redundant driver extraction')):
                result = recognize_by_crushing(self.circle, **self.options(method))
            self.assertEqual(result['status'], 'UNKNOT')
            self.assertGreater(result['stats']['nodes_attempted'], 0)
            self.assertEqual(result['stats']['extraction_steps'], 0)
            self.assertTrue(verify_crushing_recognition(self.circle, result['certificate']))
            self.assert_legacy_extraction_same(self.circle, self.options(method), result)

    def test_actual_canonical_nonextreme_point_repairs_once_in_all_positive_paths(self):
        expected = extract_positive_ray(self.capped, self.mixture)
        self.assertEqual(expected['stats']['descent_steps'], 1)
        for method in ('lp', 'tree', 'transversal'):
            with self.subTest(method=method), self.source_harness(self.capped), \
                 self.inject_point(method, self.capped, self.mixture, certify_lp=method == 'lp'), \
                 patch('fastunknot.positive_ray.extract_positive_ray', wraps=extract_positive_ray) as repair:
                result = recognize_by_crushing(self.circle, **self.options(method))
                self.assertEqual(result['status'], 'UNKNOT')
                self.assertTrue(verify_crushing_recognition(self.circle, result['certificate']))
            repair.assert_called_once()
            self.assertEqual(repair.call_args.args, (self.capped, self.mixture))
            self.assertEqual(result['stats']['extraction_steps'], 1)
            first = result['certificate']['chain']['steps'][0]
            self.assertEqual(first['coordinates'], expected['coordinates'])
            self.assertTrue(verify_normal_crushing(self.capped, first))
            self.assertFalse(verify_crushing_recognition(self.circle, result['certificate']))

    def test_huge_nonprimitive_point_normalizes_before_single_retry(self):
        for scale in (2, 1 << 20000):
            point = json_safe([[scale*x for x in row] for row in self.ray])
            with self.subTest(scale_bits=scale.bit_length()), self.source_harness(self.one), \
                 self.inject_point('tree', self.one, point), \
                 patch('fastunknot.positive_ray.extract_positive_ray', wraps=extract_positive_ray) as repair:
                result = recognize_by_crushing(self.circle, **self.options())
            repair.assert_called_once()
            self.assertEqual(result['status'], 'UNKNOT')
            self.assertEqual(result['stats']['crushing_steps'], 1)
            self.assertEqual(result['stats']['extraction_steps'], 0)
            packet = result['certificate']['chain']['steps'][0]
            self.assertEqual(packet['coordinates'], self.ray)
            self.assertTrue(verify_normal_crushing(self.one, packet))
            self.assertFalse(verify_crushing_recognition(self.circle, result['certificate']))

    def test_independent_replay_rejects_a_constructed_false_quotient_without_repair(self):
        observed = []
        def corrupt(source, rows, **kwargs):
            result = crush_normal_ray(source, rows, **kwargs)
            result['certificate']['components'] = []
            observed.append((source, result['certificate']))
            return result
        with patch('fastunknot.normal_crushing.crush_normal_ray', corrupt), patch(
                'fastunknot.positive_ray.extract_positive_ray', side_effect=AssertionError('unexpected repair')):
            with self.assertRaisesRegex(ArithmeticError, 'independent normal crushing replay failed'):
                recognize_by_crushing(self.circle, **self.options('lp'))
        self.assertEqual(len(observed), 1)
        self.assertFalse(verify_normal_crushing(*observed[0]))

    def test_unclassified_errors_and_verifier_classifiers_do_not_trigger_repair(self):
        cases = [('fastunknot.normal_crushing.crush_normal_ray', NormalOrbitError('ordinary invalid geometry'))]
        cases += [('fastunknot.normal_crushing_verify.verify_normal_crushing', kind('verifier failure'))
                  for kind in (_NonPrimitiveNormalPoint, _NonExtremeNormalPoint)]
        for target, error in cases:
            with self.subTest(target=target, kind=type(error)), patch(target, side_effect=error), patch(
                    'fastunknot.positive_ray.extract_positive_ray', side_effect=AssertionError('unexpected repair')):
                with self.assertRaises(type(error)) as caught:
                    recognize_by_crushing(self.circle, **self.options())
            self.assertIs(caught.exception, error)

    def test_retry_classifier_propagates_without_recursive_repair(self):
        point = [[2*x for x in row] for row in self.ray]
        error = _NonExtremeNormalPoint('retry must not reenter repair')
        calls = []
        def reject_retry(source, rows, **kwargs):
            calls.append(deepcopy(rows))
            if len(calls) == 2:
                raise error
            return crush_normal_ray(source, rows, **kwargs)
        with self.source_harness(self.one), self.inject_point('tree', self.one, point), \
             patch('fastunknot.normal_crushing.crush_normal_ray', reject_retry), \
             patch('fastunknot.positive_ray.extract_positive_ray', wraps=extract_positive_ray) as repair:
            with self.assertRaises(_NonExtremeNormalPoint) as caught:
                recognize_by_crushing(self.circle, **self.options())
        self.assertIs(caught.exception, error)
        repair.assert_called_once()
        self.assertEqual(calls, [point, self.ray])

    def test_callbacks_keep_identity_during_direct_repair_retry_and_verification(self):
        for stage in ('direct', 'repair', 'retry', 'verify'):
            for kind in (_NonPrimitiveNormalPoint, _NonExtremeNormalPoint, KeyboardInterrupt):
                error = kind('caller interruption')
                active = [False]
                crush_calls = [0]
                repair_calls = [0]
                def invoke(function, enabled, *args, **kwargs):
                    active[0] = enabled
                    try:
                        return function(*args, **kwargs)
                    finally:
                        active[0] = False
                def crush(*args, **kwargs):
                    crush_calls[0] += 1
                    return invoke(crush_normal_ray, stage == 'direct' or
                                  stage == 'retry' and crush_calls[0] == 2, *args, **kwargs)
                def repair(*args, **kwargs):
                    repair_calls[0] += 1
                    return invoke(extract_positive_ray, stage == 'repair', *args, **kwargs)
                def verify(*args, **kwargs):
                    return invoke(verify_normal_crushing, stage == 'verify', *args, **kwargs)
                def check():
                    if active[0]:
                        raise error
                with self.subTest(stage=stage, kind=kind), self.source_harness(self.capped), \
                     self.inject_point('tree', self.capped, self.mixture), \
                     patch('fastunknot.normal_crushing.crush_normal_ray', crush), \
                     patch('fastunknot.positive_ray.extract_positive_ray', repair), \
                     patch('fastunknot.normal_crushing_verify.verify_normal_crushing', verify):
                    with self.assertRaises(kind) as caught:
                        recognize_by_crushing(self.circle, check=check, **self.options())
                self.assertIs(caught.exception, error)
                self.assertEqual(repair_calls[0], 0 if stage == 'direct' else 1)

    def test_zero_reduction_budget_denies_crushing_and_extraction_after_positive_search(self):
        for method in ('lp', 'tree', 'transversal'):
            with self.subTest(method=method), patch('fastunknot.normal_crushing.crush_normal_ray',
                    side_effect=AssertionError('unaccepted crush')), patch(
                    'fastunknot.positive_ray.extract_positive_ray', side_effect=AssertionError('unaccepted repair')):
                result = recognize_by_crushing(self.circle, **self.options(method, max_crushes=0))
            self.assertEqual(result['status'], 'INCONCLUSIVE')
            self.assertGreater(result['stats']['positive_euler_rays'], 0)
            self.assertEqual(result['stats']['crushing_steps'], 0)
            self.assertEqual(result['stats']['extraction_steps'], 0)
            self.assertEqual(result['partial_chain']['steps'], [])
            self.assertTrue(verify_crushing_chain(self.circle, result['partial_chain']))

    def test_genuine_factor_shared_allowance_counts_only_accepted_direct_crushes(self):
        diagram = Diagram.from_braid(3, [1, 2])
        for cap in (1, 2):
            with self.subTest(cap=cap), patch('fastunknot.positive_ray.extract_positive_ray',
                    side_effect=AssertionError('redundant factor extraction')), patch(
                    'fastunknot.normal_crushing.crush_normal_ray', wraps=crush_normal_ray) as crush:
                result = recognize_factored_by_crushing(diagram, **self.options(max_crushes=cap))
            self.assertEqual(result['stats']['factors_attempted'], 2)
            self.assertEqual(result['stats']['crushing_steps'], cap)
            self.assertEqual(crush.call_count, cap)
            self.assertEqual(result['stats']['extraction_steps'], 0)
            self.assertEqual(result['status'], 'UNKNOT' if cap == 2 else 'INCONCLUSIVE')
            if cap == 2:
                self.assertTrue(verify_factored_crushing_recognition(diagram, result['certificate']))
            for attempt in result['factor_results']:
                factor = Diagram.from_pd(result['factor_pds'][attempt['factor_index']])
                child = attempt['result']
                if child['status'] == 'UNKNOT':
                    self.assertTrue(verify_crushing_recognition(factor, child['certificate']))
                else:
                    self.assertEqual(child['stats']['crushing_steps'], 0)
                    self.assertTrue(verify_crushing_chain(factor, child['partial_chain']))

    def test_genuine_vertex_preprocessing_keeps_its_needed_extraction_calls(self):
        diagram = Diagram.from_braid(2, [1, 1, 1])
        with patch.object(vertex_module, 'extract_positive_ray', wraps=extract_positive_ray) as needed, \
             patch('fastunknot.positive_ray.extract_positive_ray', side_effect=AssertionError('driver extraction')):
            result = recognize_by_crushing(diagram, max_sectors=0)
        self.assertEqual(result['status'], 'INCONCLUSIVE')
        self.assertGreater(needed.call_count, 0)
        self.assertEqual(needed.call_count, result['stats']['vertex_reduction_crushes'])
        self.assertTrue(verify_crushing_chain(diagram, result['partial_chain']))
        self.assertEqual(_prepare(result['partial_chain']['triangulation'], lambda: None)['vertices'], 1)

    def test_noncanonical_positive_point_still_fails_checked_repair(self):
        point = [[value+1 if j < 4 else value for j, value in enumerate(row)] for row in self.mixture]
        with self.source_harness(self.capped), self.inject_point('tree', self.capped, point), \
             patch('fastunknot.positive_ray.extract_positive_ray', wraps=extract_positive_ray) as repair:
            with self.assertRaisesRegex(NormalOrbitError, 'canonical'):
                recognize_by_crushing(self.circle, **self.options())
        repair.assert_called_once()


if __name__ == '__main__':
    unittest.main()
