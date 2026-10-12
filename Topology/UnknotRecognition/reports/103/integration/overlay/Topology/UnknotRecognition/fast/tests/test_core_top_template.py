"""Universal source-tree specialization across changing normal supports."""

from copy import deepcopy
from itertools import product
import json
import unittest
from unittest.mock import patch

from fastunknot.core_top_reduction_verify import replay_core_top_reduction
from fastunknot.core_top_template import (
    compile_source_top_tree, specialize_source_top_tree, verify_source_top_tree,
)
from fastunknot.integer_codec import json_safe
from fastunknot.normal_parallelity import normal_cut_parallelity
from normal_orbit_research.fixtures import interior_vertex_torus, layered_torus


class SourceTopTreeTests(unittest.TestCase):
    def test_one_tree_all_64_compatible_vectors(self):
        raw, basis = interior_vertex_torus()
        template = compile_source_top_tree(raw)
        self.assertTrue(verify_source_top_tree(raw, template))
        selected = set()
        for coefficients in product(range(4), repeat=3):
            rows = [[sum(c * basis[name][t][j] for c, name in
                         zip(coefficients, ('sphere', 'boundary_disk', 'mobius')))
                     for j in range(7)] for t in range(4)]
            geometry = normal_cut_parallelity(raw, rows)['geometry']
            proof = specialize_source_top_tree(raw, rows, geometry, template)
            reduced = replay_core_top_reduction(raw, rows, geometry, proof)
            self.assertIsNotNone(reduced)
            self.assertEqual(reduced['core']['handles3'], [])
            self.assertEqual(reduced['ports'], geometry['ports'])
            self.assertEqual(len(proof['moves']), 1)
            selected.add(tuple(proof['moves'][0]))
        self.assertGreater(len(selected), 1)

    def test_large_coordinates_do_not_grow_top_certificate(self):
        raw, basis = interior_vertex_torus()
        template = compile_source_top_tree(raw)
        sizes = []
        for scale in (1, 1 << 64, 1 << 16384):
            rows = [[scale * n for n in row] for row in basis['boundary_disk']]
            geometry = normal_cut_parallelity(raw, rows)['geometry']
            proof = specialize_source_top_tree(raw, rows, geometry, template)
            self.assertIsNotNone(replay_core_top_reduction(raw, rows, geometry, proof))
            sizes.append(len(json.dumps(json_safe(proof), sort_keys=True)))
        self.assertEqual(len(set(sizes)), 1)

    def test_no_interior_vertices_and_bad_templates(self):
        raw, base = layered_torus(4)
        template = compile_source_top_tree(raw)
        self.assertEqual(template['parents'], [])
        geometry = normal_cut_parallelity(raw, base)['geometry']
        proof = specialize_source_top_tree(raw, base, geometry, template)
        self.assertEqual(proof['moves'], [])
        self.assertIsNotNone(replay_core_top_reduction(raw, base, geometry, proof))
        interior, _ = interior_vertex_torus()
        self.assertFalse(verify_source_top_tree(interior, template))
        good = compile_source_top_tree(interior)
        mutations = []
        for field, value in (('source_sha256', '0'*64), ('schema', 'wrong'),
                             ('parents', []), ('parents', None)):
            bad = deepcopy(good)
            bad[field] = value
            mutations.append(bad)
        for field, value in (('vertex', True), ('parent', -1), ('edge', -1)):
            bad = deepcopy(good)
            bad['parents'][0][field] = value
            mutations.append(bad)
        bad = deepcopy(good)
        bad['parents'].append(deepcopy(bad['parents'][0]))
        mutations.append(bad)
        for bad in mutations:
            self.assertFalse(verify_source_top_tree(interior, bad))

    def test_verifiers_do_not_use_compilers(self):
        raw, basis = interior_vertex_torus()
        rows = basis['mobius']
        geometry = normal_cut_parallelity(raw, rows)['geometry']
        template = compile_source_top_tree(raw)
        proof = specialize_source_top_tree(raw, rows, geometry, template)
        with patch('fastunknot.core_top_template.compile_source_top_tree',
                   side_effect=AssertionError('compiler used')):
            self.assertTrue(verify_source_top_tree(raw, template))
        with patch('fastunknot.core_top_reduction.source_core_top_incidence',
                   side_effect=AssertionError('producer used')):
            self.assertIsNotNone(replay_core_top_reduction(raw, rows, geometry, proof))

    def test_cancellation_propagates(self):
        class Stop:
            def __bool__(self):
                return False
            def __call__(self):
                raise RuntimeError('cancelled')
        raw, _ = interior_vertex_torus()
        with self.assertRaisesRegex(RuntimeError, 'cancelled'):
            compile_source_top_tree(raw, check=Stop())


if __name__ == '__main__':
    unittest.main()
