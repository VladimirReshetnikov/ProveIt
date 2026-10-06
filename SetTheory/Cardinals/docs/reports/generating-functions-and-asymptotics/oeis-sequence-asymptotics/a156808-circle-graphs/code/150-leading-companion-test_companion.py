"""Unit and adversarial tests. Run unchanged with python -O -m unittest -v."""
from copy import deepcopy
from fractions import Fraction
from itertools import combinations, permutations
from pathlib import Path
import json
import os
import tempfile
import unittest

import circle_companion as c
from safe_io import fresh_file, regular_bytes
from verify import VerificationError, compare, load_document, verify_document


class ExactCompanionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.evidence = c.build_evidence()

    def test_saved_evidence_is_reproducible(self):
        verify_document(load_document(c.ROOT/'evidence.json'))

    def test_matching_generation_has_no_duplicates(self):
        for n in range(1, 6):
            generated = list(c.matchings(tuple(range(2*n))))
            self.assertEqual(len(generated), c.matching_number(n))
            self.assertEqual(len(set(generated)), len(generated))

    def test_crossings_by_independent_four_endpoint_definition(self):
        for matching in c.matchings(tuple(range(8))):
            graph = c.adjacency(c.word_from_matching(matching))
            for i, j in combinations(range(4), 2):
                ordered = sorted([(p, 0) for p in matching[i]] + [(p, 1) for p in matching[j]])
                alternate = [tag for _, tag in ordered] in ([0, 1, 0, 1], [1, 0, 1, 0])
                self.assertEqual(bool(graph[i] >> j & 1), alternate)

    def test_split_partitions_include_empty_crossing_cuts(self):
        self.assertEqual(c.split_partitions((0, 0, 0, 0)), [[0, 1], [0, 2], [0, 3]])
        self.assertIn([0, 1], c.split_partitions((2, 1, 8, 4)))

    def test_core_automorphisms_without_degree_filter(self):
        graph = c.adjacency(c.PRIME_CORE)
        count = 0
        for p in permutations(range(6)):
            if all(((graph[a] >> b) & 1) == ((graph[p[a]] >> p[b]) & 1) for a, b in combinations(range(6), 2)):
                count += 1
        self.assertEqual(count, 1)
        self.assertEqual(c.automorphism_count(graph), count)

    def test_graph_key_invariant_under_all_core_relabelings(self):
        graph = c.adjacency(c.PRIME_CORE)
        wanted = c.canonical_graph(graph)
        for p in permutations(range(6)):
            renamed = [0] * 6
            for a, b in combinations(range(6), 2):
                if graph[a] >> b & 1:
                    renamed[p[a]] |= 1 << p[b]
                    renamed[p[b]] |= 1 << p[a]
            self.assertEqual(c.canonical_graph(tuple(renamed)), wanted)

    def test_endpoint_choices_not_merely_rotation_normalized(self):
        experiments = self.evidence['leaf_moves_and_graph_fibers']['independent_leaf_moves']
        for experiment in experiments:
            representatives = [tuple(x['word']) for x in experiment['moves']]
            for i, first in enumerate(representatives):
                orbit = set(c.dihedral_images(first))
                self.assertEqual(len(orbit), 4*(6+experiment['leaf_count']))
                for second in representatives[i+1:]:
                    self.assertNotIn(c.normalize(second), orbit)

    def test_graph_symmetry_is_not_geometric_symmetry(self):
        record = self.evidence['decorations_poisson_and_automorphisms']['geometric_asymmetry_does_not_imply_graph_asymmetry']
        self.assertEqual(record['dihedral_stabilizer_order'], 1)
        self.assertEqual(record['graph_automorphism_order'], 4)

    def test_exact_ceiling_threshold_counterexample(self):
        n = 20
        model = lambda j: Fraction(c.matching_number(j), j)
        sequence = lambda j: model(j)*Fraction(j-1, j)
        x = model(n)*Fraction(2*n-1, 2*n)
        actual = next(j for j in range(2, 30) if sequence(j) >= x)
        model_ceiling = next(j for j in range(2, 30) if model(j) >= x)
        self.assertEqual((model_ceiling, actual), (20, 21))

    def test_semantic_mutations_are_rejected(self):
        paths = [
            ('source_count_checks', 'sequence_ids', 'connected'),
            ('source_count_checks', 'connected_counts_through_12', 5),
            ('source_count_checks', 'all_counts_through_13', 12),
            ('source_count_checks', 'derived_connected_count_order_13', 'value'),
            ('source_count_checks', 'connectivity_correction_finite_counts', 5, 'disconnected_without_isolates'),
            ('small_graph_enumeration', 5, 'all_graphs'),
            ('small_graph_enumeration', 4, 'sum_matching_reciprocal_graph_fiber', 'numerator'),
            ('symmetry_formula_checks', 4, 'observed_fixed_counts', 3),
            ('long_leaf_formula_checks', 'fixed_chord_counts', 1, 'enumerated_count'),
            ('long_leaf_formula_checks', 'convolution_checks', 0, 'expected_nonshort_leaves_upper_bound', 'denominator'),
            ('leaf_moves_and_graph_fibers', 'core_nontrivial_split_count'),
            ('leaf_moves_and_graph_fibers', 'independent_leaf_moves', 1, 'moves', 0, 'choices', 0),
            ('leaf_moves_and_graph_fibers', 'independent_leaf_moves', 2, 'moves', 0, 'dihedral_orbit_size'),
            ('leaf_moves_and_graph_fibers', 'full_fiber_seven_chords', 'graph_fiber_size'),
            ('decorations_poisson_and_automorphisms', 'geometric_asymmetry_does_not_imply_graph_asymmetry', 'graph_automorphism_order'),
            ('decorations_poisson_and_automorphisms', 'explicit_decorations', 3, 'graph_automorphism_order'),
            ('decorations_poisson_and_automorphisms', 'poisson_deficit_coefficients', 2, 'sum_triple_coefficients', 'numerator'),
            ('inverse_model_checks', 'bounded_displacement', 0, 'coefficient', 'numerator'),
            ('inverse_model_checks', 'gamma_log_remainder_coefficients', 0, 'coefficient', 'numerator'),
            ('inverse_model_checks', 'ceiling_safety_example', 'actual_least_index'),
            ('inverse_model_checks', 'ceiling_safety_example', 'upper_safe_ceiling'),
            ('atomic_patterns_and_palm_forcing', 'distinct_Z_pattern_count'),
            ('atomic_patterns_and_palm_forcing', 'atomic_means', 'Z', 'exact_mean', 'numerator'),
            ('atomic_patterns_and_palm_forcing', 'forcing_witnesses', 2, 'preimages_per_target'),
        ]
        for path in paths:
            with self.subTest(path=path):
                mutant = deepcopy(self.evidence)
                node = mutant
                for key in path[:-1]:
                    node = node[key]
                original = node[path[-1]]
                node[path[-1]] = original + 1 if isinstance(original, int) else original + '-MUTATED'
                with self.assertRaises(VerificationError):
                    verify_document(mutant)

    def test_missing_extra_and_reordered_fields_rejected(self):
        for change in ('remove', 'add', 'reorder'):
            mutant = deepcopy(self.evidence)
            if change == 'remove':
                del mutant['inverse_model_checks']
            elif change == 'add':
                mutant['unsupported_claim'] = 'All-orders asymptotic proved'
            else:
                mutant['small_graph_enumeration'].reverse()
            with self.assertRaises(VerificationError):
                verify_document(mutant)

    def test_bool_float_not_accepted_as_integer(self):
        for impostor in (True, 1.0):
            with self.assertRaises(VerificationError):
                compare(impostor, 1)

    def test_duplicate_keys_and_nonfinite_json_rejected(self):
        for malformed in ('{"a":1,"a":2}', '{"a":NaN}', '{"a":Infinity}'):
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory)/'bad.json'
                path.write_text(malformed)
                with self.assertRaises(VerificationError):
                    load_document(path)

    def test_safe_io_rejects_overwrite_and_symlink_components(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            target = root/'target.json'
            fresh_file(target, b'original')
            with self.assertRaises(FileExistsError):
                fresh_file(target, b'changed')
            self.assertEqual(regular_bytes(target), b'original')
            (root/'link.json').symlink_to(target)
            with self.assertRaises(OSError):
                fresh_file(root/'link.json', b'changed')
            with self.assertRaises(OSError):
                regular_bytes(root/'link.json')
            (root/'subdir').mkdir()
            (root/'alias').symlink_to(root/'subdir', target_is_directory=True)
            with self.assertRaises(OSError):
                fresh_file(root/'alias'/'new.json', b'changed')
            self.assertFalse((root/'subdir'/'new.json').exists())
            with self.assertRaises(ValueError):
                fresh_file(str(root) + '/subdir/../forbidden.json', b'changed')

    def test_hypothesis_guards_remain_enabled(self):
        with self.assertRaises(ValueError):
            c.require(False, 'must fail even with optimization')
        with self.assertRaises(ValueError):
            c.matching_number(-1)
        with self.assertRaises(ValueError):
            c.expand_word(c.PRIME_CORE, [(0, 'L', 0), (0, 'L', 1)])


if __name__ == '__main__':
    unittest.main(verbosity=2)
