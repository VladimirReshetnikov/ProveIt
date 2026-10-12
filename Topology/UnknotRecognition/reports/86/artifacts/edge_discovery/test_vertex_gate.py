"""Focused independent arithmetic and topology-contract tests for vertex_gate."""

from copy import deepcopy
from itertools import permutations
import json
import random
import unittest
from unittest.mock import patch

import vertex_gate as gate
from fastunknot.normal_surface_geometry import _prepare, _coordinates, NormalOrbitError
from normal_orbit_research.fixtures import boundary_cap, layered_torus
from normal_orbit_research.weight_defect import DISC_ONE_EDGE, OBSTRUCTION


def determinant_by_permutations(matrix):
    n = len(matrix)
    total = 0
    for order in permutations(range(n)):
        sign = (-1)**sum(order[i] > order[j] for i in range(n) for j in range(i+1, n))
        product = sign
        for i, j in enumerate(order):
            product *= matrix[i][j]
        total += product
    return total


class VertexGateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        record = json.loads(OBSTRUCTION.read_text())
        cls.raw = record['moves'][-1]['triangulation']
        cls.disc = deepcopy(DISC_ONE_EDGE)
        cls.coherent = record['family_certificate']['coordinates']

    def test_fraction_free_determinants_against_permutation_formula(self):
        rng = random.Random(261012119)
        for size in range(6):
            for _ in range(20):
                matrix = [[rng.randrange(-3, 4) for _ in range(size)] for _ in range(size)]
                self.assertEqual(gate._minor_determinant(matrix),
                                 determinant_by_permutations(matrix))

    def test_new_vertex_meridian_replays_without_any_discovery(self):
        proof = gate.produce_vertex_disc_certificate(self.raw, self.disc)
        self.assertIsNotNone(proof)
        self.assertEqual(len(proof['minor_rows']), len(proof['support'])-1)
        with patch.object(gate, 'produce_vertex_disc_certificate', side_effect=AssertionError), \
             patch.object(gate, '_find_rank_minor', side_effect=AssertionError), \
             patch('fastunknot.normal_disk_kernel.normal_compressing_disk_count',
                   side_effect=AssertionError), \
             patch('fastunknot.normal_surface_orbits.normal_surface_topology',
                   side_effect=AssertionError):
            self.assertTrue(gate.verify_vertex_disc_certificate(self.raw, self.disc, proof))

    def test_coherent_nonprimitive_and_nonextreme_vectors_do_not_certify(self):
        self.assertIsNone(gate.produce_vertex_disc_certificate(self.raw, self.coherent))
        doubled = [[2*x for x in row] for row in self.disc]
        self.assertIsNone(gate.produce_vertex_disc_certificate(self.raw, doubled))
        vertex_link = [[1, 1, 1, 1, 0, 0, 0] for _ in self.disc]
        linked = [[x+y for x, y in zip(a, b)] for a, b in zip(self.disc, vertex_link)]
        self.assertIsNone(gate.produce_vertex_disc_certificate(self.raw, linked))
        # This compatible primitive vector has chi=1 and nonzero boundary
        # class, but its positive support has nullity greater than one.
        mixed = [[4*x+y for x, y in zip(a, b)] for a, b in zip(self.disc, self.coherent)]
        prepared = _prepare(self.raw, lambda: None)
        data = _coordinates(prepared, mixed, lambda: None)
        self.assertEqual(data['euler_characteristic'], 1)
        _, _, rank, augmented = gate._boundary_quotient(prepared, data)
        self.assertEqual(augmented, rank+1)
        self.assertIsNone(gate.produce_vertex_disc_certificate(self.raw, mixed))

    def test_multiple_boundary_vertices_use_the_cohomology_quotient(self):
        raw, disc = boundary_cap(*layered_torus(3))
        proof = gate.produce_vertex_disc_certificate(raw, disc)
        self.assertIsNotNone(proof)
        self.assertEqual(proof['coboundary_rank'], 1)
        self.assertEqual(proof['augmented_rank'], 2)
        self.assertTrue(gate.verify_vertex_disc_certificate(raw, disc, proof))
        prepared = _prepare(raw, lambda: None)
        newest = max(prepared['vertex_roots'])
        link = [[int(prepared['vertex_roots'][4*t+v] == newest) for v in range(4)]+[0]*3
                for t in range(len(raw['tetrahedra']))]
        data = _coordinates(prepared, link, lambda: None)
        self.assertEqual(data['euler_characteristic'], 1)
        edges, parity, rank, augmented = gate._boundary_quotient(prepared, data)
        self.assertTrue(any(parity))
        self.assertEqual(augmented, rank)
        self.assertIsNone(gate.produce_vertex_disc_certificate(raw, link))
        # Even a correct support-rank minor and a raw nonzero parity vector
        # cannot bypass the quotient by vertex coboundaries.
        support = [i for i, x in enumerate(x for row in link for x in row) if x]
        minor = gate._find_rank_minor(prepared['matching'], support) if len(support) > 1 else ([], [])
        rows, columns = minor
        determinant = gate._minor_determinant([
            [prepared['matching'][r].get(c, 0) for c in columns] for r in rows])
        forged = dict(schema='normal-vertex-disc-rank-v1',
            source_sha256=gate._binding(raw, link), support=support,
            minor_rows=rows, minor_columns=columns, minor_determinant=hex(determinant),
            boundary_edges=edges, boundary_parity=parity, coboundary_rank=rank,
            augmented_rank=rank+1, euler_characteristic=1, primitive_gcd=1)
        self.assertFalse(gate.verify_vertex_disc_certificate(raw, link, forged))

    def test_layered_binary_meridians(self):
        for size in (1, 8, 32):
            raw, disc = layered_torus(size)
            proof = gate.produce_vertex_disc_certificate(raw, disc)
            self.assertIsNotNone(proof)
            self.assertTrue(gate.verify_vertex_disc_certificate(raw, disc, proof))

    def test_malformed_certificates_and_wrong_sources_are_rejected(self):
        proof = gate.produce_vertex_disc_certificate(self.raw, self.disc)
        for field in proof:
            bad = deepcopy(proof)
            del bad[field]
            self.assertFalse(gate.verify_vertex_disc_certificate(self.raw, self.disc, bad))
        changes = [('extra', 0), ('schema', 'wrong'), ('source_sha256', '0'*64),
                   ('minor_determinant', '0x0'), ('primitive_gcd', True),
                   ('euler_characteristic', True), ('coboundary_rank', True),
                   ('augmented_rank', 0), ('support', []), ('minor_rows', []),
                   ('minor_columns', []), ('boundary_parity', [True]*len(proof['boundary_parity']))]
        for key, value in changes:
            bad = dict(proof, **{key: value})
            self.assertFalse(gate.verify_vertex_disc_certificate(self.raw, self.disc, bad))
        wrong = deepcopy(self.disc)
        wrong[0][0] += 1
        self.assertFalse(gate.verify_vertex_disc_certificate(self.raw, wrong, proof))
        raw, _ = layered_torus(8)
        self.assertFalse(gate.verify_vertex_disc_certificate(raw, self.disc, proof))

    def test_cancellation_and_input_immutability(self):
        raw, disc = deepcopy(self.raw), deepcopy(self.disc)
        proof = gate.produce_vertex_disc_certificate(raw, disc)
        for exception in (RuntimeError, NormalOrbitError):
            count = [0]

            def cancel():
                count[0] += 1
                if count[0] == 10:
                    raise exception('cancelled')

            with self.assertRaisesRegex(exception, 'cancelled'):
                gate.verify_vertex_disc_certificate(raw, disc, proof, check=cancel)
        self.assertEqual(raw, self.raw)
        self.assertEqual(disc, self.disc)


if __name__ == '__main__':
    unittest.main()
