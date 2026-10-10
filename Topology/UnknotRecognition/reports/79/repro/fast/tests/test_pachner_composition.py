"""Source-bound composition tests on genuine disjoint descent traces."""
from copy import deepcopy
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from commitment_research.fixtures import canonical_cochain_key
from fastunknot.normal_cocycle import CocycleLimit, local_coordinates
from fastunknot.pachner_causality import compose_disjoint_traces
from fastunknot.pachner_commitments_verify import (
    inspect_pachner_endpoint, verify_pachner_endpoint,
)


FAST = Path(__file__).resolve().parents[1]


def _fixture():
    path = FAST/'shared_cover_research/results/exhaustion.json'
    case = json.loads(path.read_text())['cases'][1]
    source = case['source']
    return (source['triangulation'], source['heights'],
            [case['retained_shared_endpoints'][i] for i in (5, 32)])


def _identity(heights):
    return dict(schema='pachner-cochain-endpoint-v1', max_upward=0,
        active_initial_tetrahedra=[], moves=[],
        coordinates=[local_coordinates(row) for row in heights], disc_certificate=None)


class PachnerCompositionTests(unittest.TestCase):
    def test_two_disjoint_gadgets_compose_with_additive_cost_and_loss(self):
        raw, heights, proofs = _fixture()
        before = deepcopy((raw, heights, proofs))
        result = compose_disjoint_traces(raw, heights, proofs)
        self.assertEqual(result['schema'], 'pachner-disjoint-composition-v1')
        summary = result['summary']
        self.assertEqual((summary['initial_tetrahedra'], summary['final_tetrahedra']), (13, 11))
        self.assertEqual((summary['upward_moves'], summary['downward_moves'], summary['loss']),
                         (2, 4, 2))
        self.assertEqual(summary['consumed_initial_tetrahedra'], list(range(1, 13)))
        self.assertEqual(result['replayed_events'], [[0, i] for i in range(3)] +
                         [[1, i] for i in range(3)])
        self.assertEqual(result['certificate']['max_upward'], 2)
        self.assertEqual(len(result['certificate']['moves']), 6)
        self.assertIsNone(result['certificate']['disc_certificate'])
        self.assertEqual((raw, heights, proofs), before)
        # The standard endpoint checker must succeed with all producers disabled.
        with patch('fastunknot.pachner_causality.compose_disjoint_traces',
                   side_effect=AssertionError), \
             patch('fastunknot.pachner23.pachner_23', side_effect=AssertionError), \
             patch('fastunknot.pachner32.pachner_32', side_effect=AssertionError), \
             patch('fastunknot.cocycle_transport.transport_cocycle', side_effect=AssertionError):
            self.assertTrue(verify_pachner_endpoint(raw, heights, result['certificate']))

    def test_actual_supports_are_used_even_when_all_supplied_covers_overlap(self):
        raw, heights, proofs = _fixture()
        for proof in proofs:
            proof['active_initial_tetrahedra'] = list(range(13))
            proof['max_upward'] = 9
        result = compose_disjoint_traces(raw, heights, proofs)
        self.assertEqual(result['certificate']['active_initial_tetrahedra'], list(range(1, 13)))
        self.assertEqual(result['certificate']['max_upward'], 2)
        self.assertEqual(result['inputs'][0]['consumed_initial_tetrahedra'], list(range(1, 7)))
        self.assertEqual(result['inputs'][1]['consumed_initial_tetrahedra'], list(range(7, 13)))

    def test_overlapping_actual_footprints_and_forged_input_are_rejected(self):
        raw, heights, proofs = _fixture()
        with self.assertRaisesRegex(ValueError, 'overlapping actual initial footprints'):
            compose_disjoint_traces(raw, heights, [proofs[0], deepcopy(proofs[0])])
        forged = deepcopy(proofs[1])
        forged['coordinates'][0][0] += 1
        with self.assertRaisesRegex(ValueError, 'invalid source-bound'):
            compose_disjoint_traces(raw, heights, [proofs[0], forged])
        with self.assertRaises(ValueError):
            compose_disjoint_traces(raw, heights, {'trace': proofs[0]})

    def test_order_changes_only_the_exact_cochain_isomorphism_representative(self):
        raw, heights, proofs = _fixture()
        forward = compose_disjoint_traces(raw, heights, proofs)
        backward = compose_disjoint_traces(raw, heights, proofs[::-1])
        ends = [inspect_pachner_endpoint(raw, heights, result['certificate'])
                for result in (forward, backward)]
        self.assertEqual(canonical_cochain_key(ends[0]['triangulation'], ends[0]['heights']),
                         canonical_cochain_key(ends[1]['triangulation'], ends[1]['heights']))
        self.assertEqual(forward['summary'], backward['summary'])

    def test_noncanonical_down_frames_survive_namespaced_composition(self):
        path = FAST/'tests/fixtures/causal_noncanonical.json'
        fixture = json.loads(path.read_text())
        raw, heights, proof = (fixture[name] for name in
                               ('triangulation', 'heights', 'certificate'))
        result = compose_disjoint_traces(raw, heights, [_identity(heights), proof])
        self.assertEqual(result['certificate']['moves'][-1]['triangulation'],
                         proof['moves'][-1]['triangulation'])
        self.assertTrue(verify_pachner_endpoint(raw, heights, result['certificate']))
        self.assertEqual(result['replayed_events'], [[1, i] for i in range(3)])

    def test_empty_composition_is_verified_identity(self):
        raw, heights, _ = _fixture()
        result = compose_disjoint_traces(raw, heights, [])
        self.assertEqual(result['summary']['loss'], 0)
        self.assertEqual(result['certificate']['moves'], [])
        self.assertEqual(result['certificate']['active_initial_tetrahedra'], [])
        self.assertTrue(verify_pachner_endpoint(raw, heights, result['certificate']))

    def test_caps_are_fail_closed_and_callback_exception_identity_is_preserved(self):
        raw, heights, proofs = _fixture()
        result = compose_disjoint_traces(raw, heights, proofs)
        exact = result['work']
        enough = compose_disjoint_traces(raw, heights, proofs, max_work=exact)
        self.assertEqual(enough['certificate'], result['certificate'])
        for allowance in (0, exact-1):
            with self.assertRaises(CocycleLimit):
                compose_disjoint_traces(raw, heights, proofs, max_work=allowance)
        marker = CocycleLimit('user stop')
        def stop():
            raise marker
        with self.assertRaises(CocycleLimit) as raised:
            compose_disjoint_traces(raw, heights, proofs, check=stop)
        self.assertIs(raised.exception, marker)


if __name__ == '__main__':
    unittest.main()
