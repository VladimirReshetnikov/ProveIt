"""Integration boundaries for source-authenticated v6 top cancellation."""

from contextlib import ExitStack
from copy import deepcopy
import json
import unittest
from unittest.mock import patch

from core_dual_fixtures import interior_loop_torus, vertex_link_coordinates
from fastunknot.integer_codec import json_safe
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from normal_orbit_research.fixtures import layered_torus


class NormalCutDualIntegrationTests(unittest.TestCase):
    def setUp(self):
        self.raw = interior_loop_torus()
        self.rows = vertex_link_coordinates(self.raw, boundary=1)
        self.result = normal_cut_handlebodies(
            self.raw, self.rows, dual_strategy='max_weight', record_certificate=True)
        self.assertEqual(self.result['status'], 'COMPLETE')
        self.proof = self.result['certificate']

    def test_v6_replays_without_any_producer(self):
        self.assertEqual(self.proof['schema'], 'normal-cut-handlebodies-v6')
        proof = json.loads(json.dumps(json_safe(self.proof)))
        names = (
            'fastunknot.normal_cut_handlebodies.normal_cut_handlebodies',
            'fastunknot.normal_cut_handlebodies.core_dual_forest',
            'fastunknot.normal_cut_handlebodies._census',
            'fastunknot.core_dual_forest.core_dual_forest',
            'fastunknot.core_dual_forest.dual_forest_plan',
            'fastunknot.core_dual_forest._source_sides',
            'fastunknot.normal_parallelity.normal_cut_parallelity',
            'fastunknot.parallelity_boundary_words.normal_parallelity_boundary_words',
            'fastunknot.core_handlebody.core_handlebody_certificate',
        )
        with ExitStack() as stack:
            for name in names:
                stack.enter_context(patch(name, side_effect=AssertionError('producer used')))
            self.assertTrue(verify_normal_cut_handlebodies(self.raw, self.rows, proof))

    def test_wrapper_is_required_and_cannot_be_nested_or_extended(self):
        mutants = [deepcopy(self.proof['downstream'])]
        bad = deepcopy(self.proof)
        bad['downstream'] = deepcopy(self.proof)
        mutants.append(bad)
        for key, value in [('schema', 'normal-cut-handlebodies-v5'),
                           ('dual', None), ('extra', []), ('downstream', None)]:
            bad = deepcopy(self.proof)
            bad[key] = value
            mutants.append(bad)
        for key in ('source_sides', 'cancellations', 'surviving_two_handles'):
            bad = deepcopy(self.proof)
            bad['dual'][key] = []
            mutants.append(bad)
        bad = deepcopy(self.proof)
        bad['dual']['cancellations'][0][0] = True
        mutants.append(bad)
        for bad in mutants:
            with self.subTest(certificate=bad.get('schema')):
                self.assertFalse(verify_normal_cut_handlebodies(self.raw, self.rows, bad))

    def test_original_source_is_authenticated_before_reduction(self):
        for kind in ('three_link', 'gap_rank', 'erase_three'):
            bad = deepcopy(self.proof)
            core = bad['downstream']['parallelity']['geometry']['core']
            if kind == 'three_link':
                core['handles3'][0]['link_triangles'][0][1] ^= 1
            elif kind == 'gap_rank':
                core['handles2'][0]['rank'] += 1
            else:
                core['handles3'] = []
            with self.subTest(mutation=kind):
                self.assertFalse(verify_normal_cut_handlebodies(self.raw, self.rows, bad))
        different = vertex_link_coordinates(self.raw, boundary=2)
        self.assertFalse(verify_normal_cut_handlebodies(self.raw, different, self.proof))

    def test_prior_no_three_certificate_is_identical_for_all_strategies(self):
        raw, rows = layered_torus(2)
        proofs = [normal_cut_handlebodies(raw, rows, dual_strategy=strategy,
                    record_certificate=True)['certificate']
                  for strategy in ('disabled', 'bfs', 'max_weight')]
        self.assertEqual(proofs[0], proofs[1])
        self.assertEqual(proofs[1], proofs[2])
        self.assertNotEqual(proofs[0]['schema'], 'normal-cut-handlebodies-v6')
        self.assertTrue(verify_normal_cut_handlebodies(raw, rows, proofs[0]))

    def test_disabled_reference_and_existing_orbit_allowance(self):
        reference = normal_cut_handlebodies(self.raw, self.rows, dual_strategy='disabled')
        self.assertEqual(reference['status'], 'INCONCLUSIVE')
        self.assertEqual(reference['reason'], 'core_has_three_handles')
        # One boundary link can need zero orbit operations; use two copies
        # to exercise the existing allowance through a v6 wrapper.
        rows = vertex_link_coordinates(self.raw, boundary=2)
        proof = normal_cut_handlebodies(self.raw, rows, dual_strategy='max_weight',
                                       record_certificate=True)['certificate']
        self.assertFalse(verify_normal_cut_handlebodies(
            self.raw, rows, proof, max_operations=0))
        self.assertEqual(normal_cut_handlebodies(
            self.raw, rows, dual_strategy='max_weight', max_cycles=0)['status'],
            'INCONCLUSIVE')
        self.assertTrue(verify_normal_cut_handlebodies(
            self.raw, rows, proof, max_operations=100000))

    def test_huge_source_cut_with_top_reduction_has_exact_census(self):
        n = 1 << 16384
        rows = [[n * entry for entry in row] for row in self.rows]
        result = normal_cut_handlebodies(self.raw, json_safe(rows),
            dual_strategy='max_weight', record_certificate=True)
        self.assertEqual(result['status'], 'COMPLETE')
        self.assertEqual(result['census']['histogram'],
                         [dict(genus=0, multiplicity=n), dict(genus=1, multiplicity=1)])
        self.assertTrue(verify_normal_cut_handlebodies(self.raw, json_safe(rows),
            json.loads(json.dumps(json_safe(result['certificate'])))))


if __name__ == '__main__':
    unittest.main()
