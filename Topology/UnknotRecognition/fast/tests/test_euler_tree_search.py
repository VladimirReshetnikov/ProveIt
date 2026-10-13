"""Partial-mask Q relaxation, complete branching and shared search allowances."""
from copy import deepcopy
from itertools import product
import unittest
from unittest.mock import patch

from fastunknot.normal_crushing import crush_normal_ray
from fastunknot.normal_crushing_verify import verify_normal_crushing
from fastunknot.normal_euler import decide_sector_euler
from fastunknot.normal_euler_tree import search_euler_tree
from fastunknot import normal_euler_tree as tree_module
from fastunknot.normal_euler_tree_verify import (
    verify_euler_branch_tree, verify_euler_relaxation_certificate,
)
from fastunknot.normal_sector import SearchLimit, build_sector_kernel
from fastunknot.normal_surface_geometry import _prepare, _coordinates, NormalOrbitError
from fastunknot.positive_ray import extract_positive_ray
from normal_orbit_research.fixtures import layered_torus, boundary_cap


def restricted_tree(*args, **kwargs):
    """Preserve regression coverage of the original per-mask model."""
    return search_euler_tree(*args, model="restricted", **kwargs)


class EulerTreeSearchTests(unittest.TestCase):
    def setUp(self):
        self.source, _ = layered_torus(2)
        self.binary_mask = [(0, 0), (1, 0), (1, 2)]
        self.ternary_mask = [(0, 0), (1, 0), (1, 1), (1, 2)]
        self.budget_mask = [(0, 1), (1, 0), (1, 2)]

    def assert_positive(self, source, result):
        self.assertEqual(result['status'], 'POSITIVE_EULER')
        self.assertNotIn('certificate', result)
        prepared = _prepare(source, lambda: None)
        analysed = _coordinates(prepared, result['coordinates'], lambda: None)
        self.assertEqual(analysed['euler_characteristic'], result['euler_characteristic'])
        self.assertGreater(analysed['euler_characteristic'], 0)
        ray = extract_positive_ray(source, result['coordinates'])
        packet = crush_normal_ray(source, ray['coordinates'])['certificate']
        self.assertTrue(verify_normal_crushing(source, packet))

    def test_compatible_positive_output_is_checked_and_extracts_to_a_crushable_ray(self):
        sources = [layered_torus(1)[0], self.source, boundary_cap(*layered_torus(1))[0]]
        for source in sources:
            for strategy in ('envelope', 'anchors'):
                result = restricted_tree(source, strategy=strategy)
                self.assert_positive(source, result)

    def test_real_incompatible_positive_relaxations_split_into_every_allowed_child(self):
        for mask, expected_types in ((self.binary_mask, [0, 2]),
                                      (self.ternary_mask, [0, 1, 2])):
            result = restricted_tree(self.source, mask)
            self.assertEqual(result['status'], 'NO_POSITIVE_EULER')
            self.assertEqual(result['stats']['branch_splits'], 1)
            self.assertEqual(result['stats']['incompatible_positive_points'], 1)
            self.assertEqual(result['stats']['negative_leaves'], len(expected_types))
            self.assertEqual(result['stats']['nodes_attempted'], 1+len(expected_types))
            proof = result['certificate']
            self.assertEqual(proof['nodes'][0], dict(kind='split', tetrahedron=1))
            self.assertEqual([node['certificate']['allowed_types'] for node in proof['nodes'][1:]],
                             [[[0, 0], [1, q]] for q in expected_types])
            self.assertTrue(verify_euler_branch_tree(self.source, proof))
            for node in proof['nodes'][1:]:
                self.assertTrue(verify_euler_relaxation_certificate(self.source, node['certificate']))

    def test_positive_envelope_with_nonpositive_actual_euler_continues_all_anchors(self):
        mask = [(0, 0), (0, 1), (1, 0), (1, 1)]
        result = restricted_tree(self.source, mask)
        self.assertEqual(result['status'], 'NO_POSITIVE_EULER')
        self.assertEqual(result['stats']['nonpositive_envelope_points'], 1)
        self.assertEqual(result['stats']['branch_splits'], 0)
        self.assertEqual(result['stats']['anchors_tested'], 7)
        self.assertEqual(result['stats']['reused_anchors'], 6)
        leaf = result['certificate']['nodes'][0]['certificate']
        self.assertEqual(leaf['proof_kind'], 'anchors')
        self.assertEqual(len(leaf['duals']), 7)
        self.assertTrue(verify_euler_branch_tree(self.source, result['certificate']))

    def test_shared_caps_charge_all_children_and_emit_no_partial_negative_certificate(self):
        full = restricted_tree(self.source, self.budget_mask)
        self.assertEqual(full['stats']['nodes_attempted'], 3)
        self.assertEqual(full['stats']['lp_pivots'], 7)
        self.assertEqual(full['stats']['anchors_tested'], 8)
        for name, field, value in (('max_nodes', 'nodes_attempted', 2),
                                    ('max_pivots', 'lp_pivots', 6),
                                    ('max_anchors', 'anchors_tested', 7)):
            result = restricted_tree(self.source, self.budget_mask, **{name: value})
            self.assertEqual(result['status'], 'INCONCLUSIVE', name)
            self.assertEqual(result['stats'][field], value, name)
            self.assertNotIn('certificate', result)
        exact = restricted_tree(self.source, self.budget_mask,
                                 max_nodes=3, max_pivots=7, max_anchors=8)
        self.assertEqual(exact, full)
        for name in ('max_nodes', 'max_pivots', 'max_anchors'):
            kwargs = {name: 0}
            if name == 'max_anchors':
                kwargs['strategy'] = 'anchors'
            result = restricted_tree(self.source, self.budget_mask, **kwargs)
            self.assertEqual(result['status'], 'INCONCLUSIVE')
            self.assertNotIn('certificate', result)

    def test_empty_mask_still_has_one_empty_anchor_obligation(self):
        result = restricted_tree(self.source, [], strategy='anchors')
        self.assertEqual(result['status'], 'NO_POSITIVE_EULER')
        self.assertEqual(result['stats']['anchors_tested'], 1)
        leaf = result['certificate']['nodes'][0]['certificate']
        self.assertEqual(leaf['duals'], [dict(anchors=[], multipliers=[])])
        self.assertTrue(verify_euler_branch_tree(self.source, result['certificate']))
        incomplete = restricted_tree(self.source, [], strategy='anchors', max_anchors=0)
        self.assertEqual(incomplete['status'], 'INCONCLUSIVE')
        self.assertNotIn('certificate', incomplete)

    def test_compatible_queries_agree_with_the_original_sector_lp(self):
        for choices in product(range(3), repeat=2):
            mask = list(enumerate(choices))
            expected = decide_sector_euler(self.source, mask)
            result = restricted_tree(self.source, mask, strategy='anchors')
            self.assertEqual(result['status'], expected['status'], mask)
            self.assertEqual(result['stats']['branch_splits'], 0)
            if result['status'] == 'NO_POSITIVE_EULER':
                self.assertTrue(verify_euler_branch_tree(self.source, result['certificate']))
            else:
                self.assert_positive(self.source, result)

    def test_independent_verifier_model_is_not_used_for_production(self):
        with patch('fastunknot.normal_euler_verify._reference_model', side_effect=AssertionError), \
             patch('fastunknot.normal_sector.sector_rays', side_effect=AssertionError):
            result = restricted_tree(self.source, self.ternary_mask)
        self.assertTrue(verify_euler_branch_tree(self.source, result['certificate']))
        # The private shared assembly did not broaden the existing sector API.
        with self.assertRaisesRegex(ValueError, 'at most one'):
            build_sector_kernel(self.source, self.ternary_mask)

    def test_exact_input_validation_and_no_input_mutation(self):
        original_source, original_mask = deepcopy(self.source), deepcopy(self.ternary_mask)
        result = restricted_tree(self.source, self.ternary_mask)
        self.assertEqual(self.source, original_source)
        self.assertEqual(self.ternary_mask, original_mask)
        self.assertEqual(restricted_tree(self.source, self.ternary_mask), result)
        for mask in (True, {}, [(0, True)], [(0, 0.0)], [(0, '0')],
                     [(0, 3)], [(2, 0)], [(0, 0), (0, 0)], [(1, 0), (0, 0)]):
            with self.assertRaises(ValueError):
                restricted_tree(self.source, mask)
        for name in ('max_nodes', 'max_pivots', 'max_anchors'):
            for value in (True, -1, 0.5, '1'):
                with self.assertRaises(ValueError):
                    restricted_tree(self.source, **{name: value})
        for strategy in (None, True, 'unknown'):
            with self.assertRaises(ValueError):
                restricted_tree(self.source, strategy=strategy)
        for source in (None, [], {}, {'tetrahedra': []}):
            with self.assertRaises(ValueError):
                restricted_tree(source)

    def test_caller_exceptions_propagate_unchanged_through_nested_lp_and_branches(self):
        calls = [0]
        def count():
            calls[0] += 1
        restricted_tree(self.source, self.budget_mask, check=count)
        for error_type in (ValueError, TypeError, NormalOrbitError, SearchLimit, RuntimeError):
            for stop in (1, calls[0]//3, 2*calls[0]//3, calls[0]):
                counter = [0]
                error = error_type('external cancellation')
                def check():
                    counter[0] += 1
                    if counter[0] == stop:
                        raise error
                with self.assertRaises(error_type) as raised:
                    restricted_tree(self.source, self.budget_mask, check=check)
                self.assertIs(raised.exception, error)

    def test_source_model_prepares_once_and_reuses_duals_across_sibling_masks(self):
        mask = [(0, 1), (1, 0), (1, 1), (1, 2)]
        with patch.object(tree_module, '_assemble_sector_kernel',
                          wraps=tree_module._assemble_sector_kernel) as prepare:
            source_result = search_euler_tree(self.source, mask)
            self.assertEqual(prepare.call_count, 1)
        restricted = restricted_tree(self.source, mask)
        self.assertEqual(source_result['status'], 'NO_POSITIVE_EULER')
        self.assertEqual(source_result['stats']['nodes_attempted'], 4)
        self.assertEqual(source_result['stats']['kernel_preparations'], 1)
        self.assertEqual(restricted['stats']['kernel_preparations'], 4)
        self.assertEqual(source_result['stats']['lp_calls'], 4)
        self.assertEqual(restricted['stats']['lp_calls'], 6)
        self.assertEqual(source_result['stats']['lp_pivots'], 7)
        self.assertEqual(restricted['stats']['lp_pivots'], 9)
        self.assertEqual(source_result['stats']['reused_envelopes'], 2)
        self.assertEqual(restricted['stats']['reused_envelopes'], 1)
        self.assertTrue(verify_euler_branch_tree(self.source, source_result['certificate']))
        self.assertTrue(verify_euler_branch_tree(self.source, restricted['certificate']))
        for node in source_result['certificate']['nodes'][1:]:
            self.assertEqual(node['certificate']['schema'], 'normal-euler-relaxation-v2')
            self.assertTrue(verify_euler_relaxation_certificate(self.source, node['certificate']))

    def test_source_model_retains_all_full_source_anchors_on_empty_masks(self):
        source_result = search_euler_tree(self.source, [], strategy='anchors')
        leaf = source_result['certificate']['nodes'][0]['certificate']
        self.assertEqual(leaf['schema'], 'normal-euler-relaxation-v2')
        self.assertEqual(len(leaf['duals']), 7)
        self.assertEqual(source_result['stats']['anchors_tested'], 7)
        self.assertEqual(source_result['stats']['lp_calls'], 0)
        self.assertTrue(verify_euler_branch_tree(self.source, source_result['certificate']))
        partial = search_euler_tree(self.source, [], strategy='anchors', max_anchors=6)
        self.assertEqual(partial['status'], 'INCONCLUSIVE')
        self.assertNotIn('certificate', partial)
        envelope = search_euler_tree(self.source, [], max_pivots=0, max_anchors=0)
        self.assertEqual(envelope['stats']['reused_envelopes'], 1)
        self.assertEqual(envelope['stats']['lp_calls'], 0)
        self.assertTrue(verify_euler_branch_tree(self.source, envelope['certificate']))

    def test_source_model_caps_and_positive_zero_extension_remain_sound(self):
        mask = [(0, 1), (1, 0), (1, 1), (1, 2)]
        complete = search_euler_tree(self.source, mask)
        for name, field in (('max_nodes', 'nodes_attempted'), ('max_pivots', 'lp_pivots'),
                            ('max_anchors', 'anchors_tested')):
            cap = complete['stats'][field]-1
            incomplete = search_euler_tree(self.source, mask, **{name: cap})
            self.assertEqual(incomplete['status'], 'INCONCLUSIVE', name)
            self.assertEqual(incomplete['stats'][field], cap)
            self.assertNotIn('certificate', incomplete)
        for strategy in ('envelope', 'anchors'):
            result = search_euler_tree(self.source, [(0, 2), (1, 2)], strategy=strategy)
            self.assert_positive(self.source, result)
            self.assertTrue(all(not row[4] and not row[5] for row in result['coordinates']))
        for model in (None, True, 'unknown'):
            with self.assertRaises(ValueError):
                search_euler_tree(self.source, model=model)

    def test_source_cache_cancellation_keeps_the_original_exception(self):
        mask = [(0, 1), (1, 0), (1, 1), (1, 2)]
        calls = [0]
        def count():
            calls[0] += 1
        search_euler_tree(self.source, mask, check=count)
        for stop in (1, calls[0]//2, calls[0]):
            error, seen = SearchLimit('caller interruption in source model'), [0]
            def check():
                seen[0] += 1
                if seen[0] == stop:
                    raise error
            with self.assertRaises(SearchLimit) as caught:
                search_euler_tree(self.source, mask, check=check)
            self.assertIs(caught.exception, error)


if __name__ == '__main__':
    unittest.main()
