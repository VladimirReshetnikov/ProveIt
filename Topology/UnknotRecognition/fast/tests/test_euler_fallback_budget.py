"""Fallback allowances across actual source queries, retries, and crushes."""
import unittest
from unittest.mock import patch

from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_chain import make_crushing_chain, verify_crushing_chain
from fastunknot.normal_crushing_search import recognize_by_crushing, verify_crushing_recognition
from fastunknot.normal_euler import decide_sector_euler
from fastunknot.normal_euler_verify import verify_sector_euler_certificate
from fastunknot.normal_euler_transversal import search_euler_transversal
from fastunknot.normal_euler_tree_verify import verify_euler_branch_tree
from normal_orbit_research.fixtures import layered_torus
from tests.test_normal_crushing_search import REDUCTION_RAY


class EulerFallbackBudgetTests(unittest.TestCase):
    def test_forced_one_dimensional_source_recovery_uses_shared_decisions(self):
        circle = Diagram.from_pd([])
        original = recognize_by_crushing(circle, sector_method='lp', reduce_vertices=False)
        chain = make_crushing_chain(circle, [REDUCTION_RAY],
                    shelling=original['certificate']['chain']['shelling'])
        source = chain['triangulation']
        for cap in range(4):
            answer = decide_sector_euler(source, [[0, 2]], lp_fast_path_pivots=0,
                                        max_feasibility_calls=cap)
            self.assertEqual(answer['stats']['lp_feasibility_calls'], cap)
            self.assertEqual(answer['stats']['lp_pivots'], 0)
            self.assertEqual(answer['stats']['lp_fallbacks'], 1)
            if cap == 3:
                self.assertEqual(answer['status'], 'POSITIVE_EULER')
                self.assertTrue(verify_sector_euler_certificate(source, answer['certificate']))
            else:
                self.assertEqual(answer['status'], 'INCONCLUSIVE')
                self.assertNotIn('certificate', answer)

    def test_transversal_restarts_share_real_ellipsoid_and_recovery_work(self):
        source = layered_torus(2)[0]
        mask = [(0, 0), (1, 0), (1, 2)]
        options = dict(lp_fast_path_pivots=0)
        full = search_euler_transversal(source, mask, **options)
        self.assertEqual(full['status'], 'NO_POSITIVE_EULER')
        self.assertTrue(verify_euler_branch_tree(source, full['certificate']))
        self.assertGreater(full['stats']['transversal_restarts'], 0)
        self.assertGreater(full['stats']['lp_fallbacks'], 1)
        for option, counter in (('max_ellipsoid_iterations', 'lp_ellipsoid_iterations'),
                                ('max_feasibility_calls', 'lp_feasibility_calls')):
            cap = full['stats'][counter] - 1
            capped = search_euler_transversal(source, mask, **options, **{option: cap})
            self.assertEqual(capped['status'], 'INCONCLUSIVE')
            self.assertEqual(capped['stats'][counter], cap)
            self.assertNotIn('certificate', capped)

    def test_fair_source_retries_share_real_cut_allowance(self):
        circle = Diagram.from_pd([])
        answer = recognize_by_crushing(circle, sector_method='lp', reduce_vertices=False,
                    lp_fast_path_pivots=0, max_ellipsoid_iterations=20, sector_quantum=1)
        self.assertEqual(answer['status'], 'INCONCLUSIVE')
        self.assertEqual(answer['stats']['lp_ellipsoid_iterations'], 20)
        self.assertGreater(answer['stats']['sector_restarts'], 0)
        self.assertGreater(answer['stats']['sectors_attempted'], 1)
        self.assertNotIn('certificate', answer)
        self.assertTrue(verify_crushing_chain(circle, answer['partial_chain']))

    def test_zero_unused_fallback_caps_preserve_complete_fast_paths(self):
        circle = Diagram.from_pd([])
        for method in ('lp', 'tree', 'transversal'):
            for policy in ('polynomial', 'bland'):
                answer = recognize_by_crushing(circle, sector_method=method,
                    lp_policy=policy, reduce_vertices=False,
                    max_ellipsoid_iterations=0, max_feasibility_calls=0)
                self.assertEqual(answer['status'], 'UNKNOT', (method, policy))
                self.assertEqual(answer['stats']['lp_fallbacks'], 0)
                self.assertTrue(verify_crushing_recognition(circle, answer['certificate']))

    def test_successor_accounting_with_controlled_discovery_costs(self):
        # Isolate budget forwarding across genuine native search/crush steps.
        # The charged costs are synthetic; no fallback discovery is claimed.
        circle = Diagram.from_pd([])
        counters = (('max_ellipsoid_iterations', 'lp_ellipsoid_iterations',
                     'shared ellipsoid iteration allowance exhausted'),
                    ('max_feasibility_calls', 'lp_feasibility_calls',
                     'shared feasibility decision allowance exhausted'))
        for option, counter, reason in counters:
            seen = []
            def charged(source, **kwargs):
                allowance = kwargs[option]
                seen.append(allowance)
                allowed = [[t, 2] for t in range(5)] if len(source['tetrahedra']) == 5 else None
                answer = search_euler_transversal(source, allowed, **kwargs)
                self.assertEqual(answer['stats'][counter], 0)
                if allowance == 0:
                    return dict(status='INCONCLUSIVE', reason=reason, stats=answer['stats'])
                answer['stats'][counter] = 1
                return answer
            with patch('fastunknot.normal_euler_transversal.search_euler_transversal', charged):
                for cap in (1, 2, 3):
                    seen.clear()
                    answer = recognize_by_crushing(circle, sector_method='transversal',
                        reduce_vertices=False, lp_strategy='anchors', **{option: cap})
                    self.assertEqual(answer['stats'][counter], cap)
                    self.assertEqual(answer['stats']['crushing_steps'], cap)
                    self.assertEqual(seen, list(range(cap, -1, -1)) if cap < 3 else [3, 2, 1])
                    if cap < 3:
                        self.assertEqual(answer['status'], 'INCONCLUSIVE')
                        self.assertTrue(verify_crushing_chain(circle, answer['partial_chain']))
                    else:
                        self.assertEqual(answer['status'], 'UNKNOT')
                        self.assertTrue(verify_crushing_recognition(circle, answer['certificate']))

    def test_strict_fallback_controls_at_source_and_diagram_boundaries(self):
        circle, source = Diagram.from_pd([]), layered_torus(1)[0]
        for option in ('lp_fast_path_pivots', 'max_ellipsoid_iterations', 'max_feasibility_calls'):
            for bad in (True, -1, 1.0, '1'):
                with self.assertRaises(ValueError):
                    decide_sector_euler(source, [[0, 0]], **{option: bad})
                with self.assertRaises(ValueError):
                    recognize_by_crushing(circle, sector_method='transversal', **{option: bad})


if __name__ == '__main__':
    unittest.main()
