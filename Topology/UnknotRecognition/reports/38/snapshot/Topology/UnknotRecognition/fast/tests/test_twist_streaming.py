"""Cross-checks of the additive streamed backend, including independent cubes."""
import json
import random
import unittest
from itertools import product

from fastunknot.twist import Run, ResourceLimit, components, runs_from_word
from fastunknot.twist.core import (
    _dot_map, _geometry, _saddle_map, homology as original_homology,
)
from fastunknot.twist.reference import cube_homology
from fastunknot.twist.streaming import (
    StreamBudget, _Meter, _compile_dot, _compile_saddle, _verify_pair,
    bounded_compositions, homology, recognize,
)


class BoundedCompositionTests(unittest.TestCase):
    def test_complete_partition_and_no_duplicates(self):
        for caps in ((), (0,), (5,), (2, 3, 1), (1, 1, 1, 1, 1), (0, 2, 0, 1)):
            actual = []
            for total in range(sum(caps) + 1):
                layer = list(bounded_compositions(caps, total))
                self.assertTrue(all(sum(a) == total for a in layer))
                self.assertEqual(layer, sorted(set(layer)))
                actual.extend(layer)
            expected = list(product(*(range(m + 1) for m in caps)))
            self.assertEqual(sorted(actual), expected)

    def test_out_of_range_and_long_nonrecursive_input(self):
        self.assertEqual(list(bounded_compositions((2, 3), -1)), [])
        self.assertEqual(list(bounded_compositions((2, 3), 6)), [])
        caps = (0,) * 1500
        self.assertEqual(list(bounded_compositions(caps, 0)), [(0,) * 1500])


class CompactAlgebraTests(unittest.TestCase):
    def test_all_edge_maps_against_original_tables(self):
        cases = (
            (2, (Run(1, 3), Run(1, -2))),
            (3, (Run(1, 2), Run(2, -2), Run(1, -2))),
            (4, (Run(1, 2), Run(3, -2), Run(2, 2), Run(1, -1))),
        )
        kinds = set()
        for strands, runs in cases:
            for state in product(*(range(abs(r.exponent) + 1) for r in runs)):
                support = sum(1 << j for j, k in enumerate(state) if k)
                source = _geometry(strands, runs, support)
                for j, (k, run) in enumerate(zip(state, runs)):
                    if (run.exponent > 0 and k == run.exponent) or (
                        run.exponent < 0 and k == 0
                    ):
                        continue
                    kk = k + 1 if run.exponent > 0 else k - 1
                    if not k or not kk:
                        target_support = support ^ (1 << j)
                        target = _geometry(strands, runs, target_support)
                        compact = _compile_saddle(source, target)
                        table = _saddle_map(source, target)
                    else:
                        a = j * strands + run.generator - 1
                        b = (j + 1) * strands + run.generator - 1
                        compact = _compile_dot(source, a, b)
                        table = _dot_map(source, a, b)
                    kinds.add(compact.kind)
                    actual = tuple(tuple(sorted(compact.images(label)))
                                   for label in range(source.dimension))
                    self.assertEqual(actual, table)
        self.assertEqual(kinds, {0, 1, 2, 3})

    def test_d_squared_detects_corruption(self):
        with self.assertRaisesRegex(ArithmeticError, r'd\^2 != 0'):
            _verify_pair([1], [1], 1, 1, _Meter(StreamBudget()), -2)


class ExactHomologyTests(unittest.TestCase):
    def assert_same_macro(self, strands, runs, *, budget=None):
        expected = original_homology(strands, runs, check_d2=True)
        for check in (False, True):
            actual = homology(strands, runs, check_d2=check, budget=budget)
            for key in ('reduced_rank', 'by_degree', 'chain_dimensions', 'boundary_ranks'):
                self.assertEqual(actual[key], expected[key], (strands, runs, check, key))
            self.assertTrue(actual['homology_complete'])
            self.assertEqual(actual['d_squared_checked'], check)
            self.assertLessEqual(actual['stats']['peak_live_layers'], 2)
            self.assertEqual(actual['stats']['enumerated_macro_states'],
                             actual['stats']['macro_states'])
            if not check:
                self.assertEqual(actual['stats']['peak_materialized_matrix_columns'], 0)
            for key in ('basis', 'differential_entries', 'matrix_bit_upper_bound',
                        'rank_xor_bit_upper_bound', 'peak_chain_dimension'):
                self.assertEqual(actual['stats'][key], expected['stats'][key], key)
        return actual

    def test_empty_unlinks_and_both_gradings(self):
        for strands in (1, 2, 4):
            self.assert_same_macro(strands, ())
        for exponent in (1, -1, 3, -3, 21, -21):
            actual = self.assert_same_macro(2, (Run(1, exponent),))
            if abs(exponent) > 1:
                self.assertEqual(actual['reduced_rank'], abs(exponent))
        self.assertEqual(homology(2, [Run(1, -3)])['by_degree'], {-3: 1, -2: 1, 0: 1})

    def test_signed_actual_braid_closures(self):
        cases = (
            (3, [1, -2, 1, -2]),
            (3, [1, 1, -2, -2, 1, -2]),
            (3, [-2, -2, 1, 1, -2]),
            (4, [1, 1, -2, 3, -2, -2, 1]),
            (3, [1] * 4 + [2] + [-1] * 3),
            (4, [-3, -3, 2, -3, 2, 1, 1, 1, -2, 1, -2]),
        )
        for strands, word in cases:
            actual = self.assert_same_macro(strands, runs_from_word(strands, word))
            reference = cube_homology(strands, word)
            self.assertEqual(actual['by_degree'], reference['by_degree'])

    def test_exhaustive_independent_cubes(self):
        # 127 two-strand words + 341 three-strand words; empty cases included.
        count = 0
        for strands, alphabet, maximum in ((2, (1, -1), 6), (3, (1, -1, 2, -2), 4)):
            for length in range(maximum + 1):
                for word in product(alphabet, repeat=length):
                    actual = homology(strands, runs_from_word(strands, word), check_d2=True)
                    reference = cube_homology(strands, list(word))
                    self.assertEqual(actual['by_degree'], reference['by_degree'], word)
                    count += 1
        self.assertEqual(count, 468)

    def test_bounded_and_disabled_caches(self):
        runs = (Run(1, 2), Run(2, -2), Run(1, 2), Run(2, -1))
        for entries in (0, 1, 2):
            budget = StreamBudget(max_geometry_cache_entries=entries,
                                  max_map_cache_entries=entries,
                                  max_geometry_cache_vertices=100,
                                  max_map_cache_slots=20)
            result = self.assert_same_macro(3, runs, budget=budget)
            stats = result['stats']
            self.assertLessEqual(stats['geometry_cache_entries_peak'], entries)
            self.assertLessEqual(stats['map_cache_entries_peak'], entries)
            self.assertLessEqual(stats['geometry_cache_vertices_peak'], 100)
            self.assertLessEqual(stats['map_cache_slots_peak'], 20)
        result = homology(3, runs, budget=StreamBudget(
            max_geometry_cache_vertices=0, max_map_cache_slots=0))
        self.assertEqual(result['stats']['geometry_cache_entries_peak'], 0)
        self.assertEqual(result['stats']['map_cache_entries_peak'], 0)

    def test_peak_state_count_is_adjacent_layer_sum(self):
        runs = (Run(1, -3), Run(2, 4), Run(1, -2))
        caps = tuple(abs(r.exponent) for r in runs)
        counts = [len(list(bounded_compositions(caps, h))) for h in range(sum(caps) + 1)]
        expected = max(a + b for a, b in zip(counts, counts[1:]))
        for check in (False, True):
            result = homology(3, runs, check_d2=check)
            self.assertEqual(result['stats']['peak_live_states'], expected)


class DecisionsAndBudgets(unittest.TestCase):
    def test_early_decision_reports_only_finalized_lower_bound(self):
        for exponent in (1001, -1001):
            result = recognize(2, [Run(1, exponent)], check_d2=True)
            self.assertEqual(result['status'], 'KNOTTED')
            hom = result['homology']
            self.assertFalse(hom['homology_complete'])
            self.assertFalse(hom['d_squared_checked'])
            self.assertIsNone(hom['reduced_rank'])
            self.assertEqual(hom['reduced_rank_lower_bound'], 2)
            self.assertLessEqual(hom['stats']['enumerated_macro_states'], 4)
            self.assertEqual(sum(hom['by_degree'].values()), 2)
        full = recognize(2, [Run(1, 101)], early_exit=False)['homology']
        self.assertTrue(full['homology_complete'])
        self.assertEqual(full['reduced_rank'], 101)

    def test_unknot_requires_complete_computation(self):
        for strands, runs in (
            (1, ()), (2, (Run(1, -1),)),
            (3, (Run(1, 9), Run(2, 1), Run(1, -8))),
        ):
            result = recognize(strands, runs, check_d2=True)
            self.assertEqual(result['status'], 'UNKNOT')
            self.assertTrue(result['homology']['homology_complete'])
            self.assertTrue(result['homology']['d_squared_checked'])
            self.assertEqual(result['homology']['reduced_rank'], 1)

    def test_links_rejected(self):
        with self.assertRaises(ValueError):
            recognize(2, [Run(1, 2)])

    def test_resource_limits_never_become_verdicts(self):
        small = (
            {'max_states': 1}, {'max_basis': 1}, {'max_live_states': 1},
            {'max_layer_basis': 1}, {'max_live_matrix_bits': 0},
            {'max_live_columns': 0}, {'max_grid_vertices': 1},
            {'max_active_map_slots': 0}, {'seconds': 0},
        )
        for limits in small:
            result = recognize(2, [Run(1, 3)], budget=StreamBudget(**limits))
            self.assertEqual(result['status'], 'UNKNOWN', limits)
        result = recognize(3, runs_from_word(3, [1, -2, 1, -2]),
                           budget=StreamBudget(max_xors=0), check_d2=True)
        self.assertEqual(result['status'], 'UNKNOWN')

    def test_huge_encoded_inputs_refused_before_allocation_or_formatting(self):
        result = recognize(2, [Run(1, (1 << 20_000) + 1)],
                           budget=StreamBudget(max_states=10))
        self.assertEqual(result['status'], 'UNKNOWN')
        self.assertEqual(result['reason'], 'macro state limit exceeded')
        with self.assertRaisesRegex(ResourceLimit, 'grid vertex'):
            homology(10**100, [Run(1, 1)])
        with self.assertRaisesRegex(ResourceLimit, 'single-state basis'):
            homology(10000, [], budget=StreamBudget(max_grid_vertices=20000))

    def test_streaming_budget_permits_large_total_but_small_live_storage(self):
        result = homology(2, [Run(1, 1001)], budget=StreamBudget(
            max_live_states=2, max_layer_basis=2,
            max_live_matrix_bits=5, max_live_columns=5))
        self.assertEqual(result['reduced_rank'], 1001)
        self.assertEqual(result['stats']['peak_live_matrix_bit_upper_bound'], 5)
        self.assertGreater(result['stats']['matrix_bit_upper_bound'], 1000)

    def test_bad_budget_values(self):
        for limits in ({'max_live_states': -1}, {'max_map_cache_entries': True},
                       {'max_live_matrix_bits': 1.5}, {'seconds': float('nan')},
                       {'seconds': float('inf')}, {'seconds': True}):
            with self.assertRaises(ValueError):
                StreamBudget(**limits)

    def test_json_output(self):
        result = recognize(2, [Run(1, 3)])
        self.assertEqual(json.loads(json.dumps(result))['status'], 'KNOTTED')


if __name__ == '__main__':
    unittest.main()
