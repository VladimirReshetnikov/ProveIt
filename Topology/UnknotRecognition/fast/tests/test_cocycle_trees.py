"""Alternative gauges, adaptive scheduling and unchanged source verification."""
from copy import deepcopy
import json
import unittest
from unittest.mock import patch

from fastunknot import Diagram, recognize
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.normal_cocycle import rank_one_cocycle_seed
from fastunknot.cocycle_trees import cocycle_tree_candidates
from fastunknot.normal_seed import normal_seed_decide
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from fastunknot.normal_cocycle_verify import inspect_cocycle_certificate
from fastunknot.normal_surface_geometry import NormalOrbitError
from tests.test_normal_seed import OPTIONS


EARLY_TWO = [[4, 0, 1, 5], [1, 0, 2, 3], [3, 2, 4, 5]]
EARLY_THREE = [[7, 0, 1, 5], [1, 0, 2, 3], [3, 2, 4, 5], [6, 6, 7, 4]]
LATE = [[9, 8, 0, 1], [0, 2, 3, 1], [3, 2, 4, 5], [4, 6, 7, 5], [6, 8, 9, 7]]


class CocycleTreeTests(unittest.TestCase):
    def test_early_success_preempts_flow_and_reuses_one_cohomology_solve(self):
        for pd, trial in ((EARLY_TWO, 2), (EARLY_THREE, 3)):
            diagram = Diagram.from_pd(pd)
            self.assertEqual(normal_seed_decide(diagram, tree_trials=0)['status'], 'INCONCLUSIVE')
            with patch('fastunknot.normal_seed.minimize_cocycle_span', side_effect=AssertionError), \
                 patch('fastunknot.normal_seed.rank_one_cocycle_seed', wraps=rank_one_cocycle_seed) as solve:
                result = normal_seed_decide(diagram)
            self.assertEqual(solve.call_count, 1)
            self.assertEqual(result['status'], 'UNKNOT')
            self.assertEqual(result['stages'][-1]['trial'], trial)
            self.assertIsNone(result['certificate']['span_certificate'])
            with patch('fastunknot.cocycle_trees.cocycle_tree_candidates', side_effect=AssertionError):
                self.assertTrue(verify_normal_seed_certificate(diagram, json.loads(json.dumps(result['certificate']))))

    def test_late_trials_follow_failed_optimization_and_stop_on_success(self):
        diagram = Diagram.from_pd(LATE)
        self.assertEqual(normal_seed_decide(diagram)['status'], 'INCONCLUSIVE')
        result = normal_seed_decide(diagram, tree_trials=24)
        self.assertEqual(result['status'], 'UNKNOT')
        self.assertEqual(result['stages'][-1]['trial'], 22)
        labels = [row['stage'] for row in result['stages']]
        position = labels.index('optimized')
        self.assertTrue(all(row['trial'] <= 4 for row in result['stages'][1:position]))
        self.assertTrue(all(row['trial'] > 4 for row in result['stages'][position+1:]))
        self.assertEqual(result['stats']['tree_search']['attempts'], 22)
        self.assertTrue(verify_normal_seed_certificate(diagram, result['certificate']))

    def test_existing_positive_paths_skip_later_search(self):
        with patch('fastunknot.normal_seed.cocycle_tree_candidates', side_effect=AssertionError):
            self.assertEqual(normal_seed_decide(Diagram.from_pd([]))['status'], 'UNKNOT')
        diagram = Diagram.from_braid(4, [-1, 2, 1, -2, 3])
        before = normal_seed_decide(diagram, tree_trials=0)
        after = normal_seed_decide(diagram, tree_trials=24)
        self.assertEqual(before['certificate'], after['certificate'])
        self.assertEqual(after['stages'][-1]['stage'], 'optimized')
        self.assertEqual(after['stats']['tree_search']['attempts'], 4)

    def test_candidate_determinism_duplicate_skipping_and_hypothesis_replay(self):
        diagram = Diagram.from_braid(2, [1, 1, 1])
        raw = diagram_exterior(diagram); seed = rank_one_cocycle_seed(raw)
        candidates = list(cocycle_tree_candidates(raw, seed['heights'], trials=12))
        self.assertEqual(candidates, list(cocycle_tree_candidates(raw, seed['heights'], trials=12)))
        self.assertEqual(len(candidates), 12)
        self.assertTrue(any(c['duplicate'] for c in candidates))
        self.assertTrue(any(not c['duplicate'] for c in candidates))
        for c in candidates:
            if c['duplicate']:
                self.assertNotIn('coordinates', c)
                continue
            proof = dict(schema='diagram-cocycle-disc-v1', input_pd=[list(r) for r in diagram.pd],
                         triangulation=raw, heights=c['heights'], coordinates=c['coordinates'], span_certificate=None)
            summary = inspect_cocycle_certificate(diagram, proof)
            self.assertEqual(summary['components'], 1)
            self.assertEqual(summary['euler_characteristic'], c['euler_characteristic'])
            self.assertEqual(summary['compressing_discs'], 0)

    def test_caps_cancellation_and_exact_option_types(self):
        diagram = Diagram.from_pd(LATE)
        full = normal_seed_decide(diagram, tree_trials=24)
        limited = normal_seed_decide(diagram, tree_trials=24, max_work=full['work']-1)
        self.assertEqual(limited['status'], 'INCONCLUSIVE')
        self.assertNotIn('certificate', limited)
        calls = [0]
        def stop():
            calls[0] += 1
            if calls[0] == 10000: raise RuntimeError('cancelled')
        with self.assertRaisesRegex(RuntimeError, 'cancelled'):
            normal_seed_decide(diagram, tree_trials=24, check=stop)
        for value in (True, -1, 1.0, None):
            with self.assertRaises(ValueError): normal_seed_decide(diagram, tree_trials=value)
            with self.assertRaises(ValueError): recognize(diagram, normal_seed_tree_trials=value)
        self.assertEqual(normal_seed_decide(Diagram.from_pd(EARLY_TWO), optimize=False)['status'], 'UNKNOT')
        result = recognize(Diagram.from_pd(EARLY_TWO), **OPTIONS)
        self.assertEqual(result.method, 'native-normal-cocycle')
        self.assertTrue(verify_normal_seed_certificate(Diagram.from_pd(EARLY_TWO), result.evidence['normal_seed']['certificate']))

    def test_malformed_public_cocycles_and_empty_trial_allowance(self):
        diagram = Diagram.from_pd([]); raw = diagram_exterior(diagram)
        seed = rank_one_cocycle_seed(raw)
        self.assertEqual(list(cocycle_tree_candidates(raw, seed['heights'], trials=0)), [])
        for value in (True, -1, None):
            with self.assertRaises(ValueError): list(cocycle_tree_candidates(raw, seed['heights'], trials=value))
        for heights in ([], [False]*len(seed['heights'])):
            with self.assertRaises(ValueError): list(cocycle_tree_candidates(raw, heights))
        bad = deepcopy(seed['heights']); bad[0][0] += 1
        with self.assertRaises(NormalOrbitError): list(cocycle_tree_candidates(raw, bad))


if __name__ == '__main__':
    unittest.main()
