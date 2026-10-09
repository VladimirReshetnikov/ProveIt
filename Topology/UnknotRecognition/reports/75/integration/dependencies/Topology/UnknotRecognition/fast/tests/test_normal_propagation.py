"""Exact propagation, finite coverage proofs, and bounded-search controls."""

from copy import deepcopy
import importlib.util
import json
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from fastunknot.normal_propagation import build_standard_model, search_positive_euler
from fastunknot.normal_propagation_verify import verify_normal_propagation_certificate
from fastunknot.normal_surface_geometry import _coordinates
from normal_orbit_research.fixtures import (layered_torus, interior_vertex_torus,
                                          boundary_cap, export_triangulation)


def _raw(specifications):
    return {'tetrahedra': [[None if item is None else
                           dict(tetrahedron=item[0], permutation=list(item[1]))
                           for item in row] for row in specifications]}


def finite_trefoil():
    """Fixed finite five-tetrahedron trefoil exterior, fLHPccdeeeqcieh.

    Exported once from Regina's ideal trefoil after truncation and simplification;
    the tests and certificate replay need no Regina installation.
    """
    return _raw([
        [(3,[0,3,2,1]),None,(1,[0,1,3,2]),(2,[0,1,3,2])],
        [(2,[0,2,1,3]),(4,[0,1,3,2]),(4,[1,0,2,3]),(0,[0,1,3,2])],
        [(1,[0,2,1,3]),None,(0,[0,1,3,2]),(3,[1,0,2,3])],
        [(0,[0,3,2,1]),(4,[1,0,2,3]),(4,[0,1,3,2]),(2,[1,0,2,3])],
        [(3,[1,0,2,3]),(1,[0,1,3,2]),(1,[1,0,2,3]),(3,[0,1,3,2])],
    ])


def branching_torus():
    """Five-tetrahedron torus requiring a guess for this deterministic policy.

    Obtained from layered_torus(2) by three 2-3 Pachner moves; its isomorphism
    signature is fLHgkacdeenkavj.  This fixture measures this policy, not an
    intrinsic lower bound on all possible propagation/search strategies.
    """
    return _raw([
        [(0,[2,0,3,1]),(1,[0,2,1,3]),(0,[1,3,0,2]),(3,[0,1,3,2])],
        [None,(3,[1,0,2,3]),(0,[0,2,1,3]),(4,[0,3,2,1])],
        [(2,[3,2,0,1]),(4,[0,3,2,1]),(3,[0,1,3,2]),(2,[2,3,1,0])],
        [(1,[1,0,2,3]),(4,[0,2,1,3]),(0,[0,1,3,2]),(2,[0,1,3,2])],
        [None,(1,[0,3,2,1]),(3,[0,2,1,3]),(2,[0,3,2,1])],
    ])


class NormalPropagationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.trefoil = finite_trefoil()
        cls.negative = search_positive_euler(cls.trefoil)

    def test_source_euler_and_anchor_model(self):
        cases = [layered_torus(t) for t in range(1, 5)]
        cases.append(boundary_cap(*layered_torus(2)))
        raw, basis = interior_vertex_torus()
        cases.extend((raw, vector) for vector in basis.values())
        for raw, vector in cases:
            model = build_standard_model(raw)
            flat = [x for row in vector for x in row]
            self.assertTrue(all(sum(a*x for a, x in zip(row, flat)) == 0
                                for row in model['matrix']))
            expected = _coordinates(model['prepared'], vector, lambda: None)['euler_characteristic']
            self.assertEqual(sum(a*x for a, x in zip(model['euler'], flat)), expected)
            self.assertEqual(sorted(x for group in model['anchor_groups'] for x in group),
                             [7*t+v for t in range(len(vector)) for v in range(4)])

    def test_fibonacci_meridians_need_no_branch_tetrahedra(self):
        for t in range(1, 9):
            raw, expected = layered_torus(t)
            answer = search_positive_euler(raw, max_branch_depth=0,
                                          allowed_branch_tetrahedra=[])
            self.assertEqual(answer['status'], 'POSITIVE_EULER', answer)
            self.assertEqual(answer['coordinates'], expected)
            self.assertEqual(answer['stats']['branches'], 0)
            self.assertEqual(answer['stats']['propagations'], t-1)
            self.assertEqual(answer['stats']['lp_calls'], 4*t-1)
            self.assertTrue(verify_normal_propagation_certificate(raw, answer['certificate']))

    def test_negative_all_anchor_coverage_and_solver_independence(self):
        answer = self.negative
        self.assertEqual(answer['status'], 'NO_POSITIVE_EULER', answer)
        self.assertEqual(answer['stats']['anchors_completed'], 20)
        proof = json.loads(json.dumps(json_safe(answer['certificate'])))
        with patch('fastunknot.normal_propagation.build_standard_model', side_effect=AssertionError), \
             patch('fastunknot.normal_propagation.solve_nonnegative_kernel', side_effect=AssertionError), \
             patch('fastunknot.exact_lp.solve_nonnegative_kernel', side_effect=AssertionError):
            self.assertTrue(verify_normal_propagation_certificate(self.trefoil, proof))
        for mutate in (lambda p: p['anchor_trees'].pop(),
                       lambda p: p['anchor_trees'][0]['anchors'].__setitem__(0, 1),
                       lambda p: p.__setitem__('source_sha256', '0'*64),
                       lambda p: p.__setitem__('status', 'KNOTTED')):
            bad = deepcopy(proof)
            mutate(bad)
            self.assertFalse(verify_normal_propagation_certificate(self.trefoil, bad))

    def test_dual_mutations_and_sound_forced_zero_steps(self):
        proof = deepcopy(self.negative['certificate'])
        first = proof['anchor_trees'][0]['tree']
        y = deepcopy(first['terminal']['y'])
        # A valid full-cone dual also proves every coordinate-deletion subcase.
        # This redundant implication is a useful independent checker control.
        first['propagations'].append(dict(tetrahedron=0, type=0, y=deepcopy(y)))
        self.assertTrue(verify_normal_propagation_certificate(self.trefoil, proof))
        mutations = [
            lambda p: p['anchor_trees'][0]['tree']['propagations'][0].__setitem__('type', True),
            lambda p: p['anchor_trees'][0]['tree']['propagations'][0].__setitem__('type', 3),
            lambda p: p['anchor_trees'][0]['tree']['propagations'][0]['y'][0].__setitem__(1, 0),
            lambda p: p['anchor_trees'][0]['tree']['propagations'][0]['y'].pop(),
            lambda p: p['anchor_trees'][0]['tree']['terminal']['y'][0].__setitem__(0, True),
            lambda p: p['anchor_trees'][0]['tree']['propagations'].append(
                dict(tetrahedron=0, type=1, y=deepcopy(y))),
        ]
        for mutate in mutations:
            bad = deepcopy(proof)
            mutate(bad)
            self.assertFalse(verify_normal_propagation_certificate(self.trefoil, bad))
        bad = deepcopy(self.negative['certificate'])
        bad['anchor_trees'][0]['tree']['terminal']['y'] = [[0, 1] for _ in y]
        self.assertFalse(verify_normal_propagation_certificate(self.trefoil, bad))

    def test_complete_branch_replay_and_omitted_branch_rejection(self):
        proof = deepcopy(self.negative['certificate'])
        first = proof['anchor_trees'][0]['tree']
        y = first['terminal']['y']
        first['terminal'] = dict(kind='BRANCH', tetrahedron=0, children=[
            dict(type=q, tree=dict(propagations=[], terminal=dict(kind='NONPOSITIVE', y=deepcopy(y))))
            for q in range(3)])
        self.assertTrue(verify_normal_propagation_certificate(self.trefoil, proof))
        for mutate in (lambda p: p['anchor_trees'][0]['tree']['terminal']['children'].pop(),
                       lambda p: p['anchor_trees'][0]['tree']['terminal']['children'][0].__setitem__('type', 1),
                       lambda p: p['anchor_trees'][0]['tree']['terminal'].__setitem__('tetrahedron', 5)):
            bad = deepcopy(proof)
            mutate(bad)
            self.assertFalse(verify_normal_propagation_certificate(self.trefoil, bad))

    def test_actual_branching_and_fixed_backdoor_scope(self):
        raw = branching_torus()
        stopped = search_positive_euler(raw, max_branch_depth=0)
        self.assertEqual(stopped['status'], 'INCONCLUSIVE')
        self.assertEqual(stopped['reason'], 'branch depth allowance exhausted')
        stopped = search_positive_euler(raw, allowed_branch_tetrahedra=[])
        self.assertEqual(stopped['status'], 'INCONCLUSIVE')
        self.assertEqual(stopped['reason'], 'allowed branch tetrahedra exhausted')
        answer = search_positive_euler(raw)
        self.assertEqual(answer['status'], 'POSITIVE_EULER', answer)
        self.assertGreater(answer['stats']['branches'], 0)
        self.assertTrue(verify_normal_propagation_certificate(raw, answer['certificate']))
        selected = answer['stats']['branched_tetrahedra']
        restricted = search_positive_euler(raw, allowed_branch_tetrahedra=selected)
        self.assertEqual(restricted['status'], 'POSITIVE_EULER', restricted)
        self.assertTrue(set(restricted['stats']['branched_tetrahedra']) <= set(selected))
        # The initial conflicting witness need not conflict inside a supplied
        # backdoor.  An unresolved allowed tetrahedron must still be explored.
        fallback = search_positive_euler(raw, allowed_branch_tetrahedra=[1])
        self.assertEqual(fallback['status'], 'POSITIVE_EULER', fallback)
        self.assertEqual(fallback['stats']['branched_tetrahedra'], [1])

    def test_aggregate_budgets_never_issue_negative_certificates(self):
        raw, _ = layered_torus(1)
        for limits in (dict(max_nodes=0), dict(max_nodes=2),
                       dict(max_pivots=0), dict(max_pivots=6)):
            answer = search_positive_euler(raw, **limits)
            self.assertEqual(answer['status'], 'INCONCLUSIVE', answer)
            self.assertNotIn('certificate', answer)
            if 'max_pivots' in limits:
                self.assertLessEqual(answer['stats']['lp_pivots'], limits['max_pivots'])
            if 'max_nodes' in limits:
                self.assertLessEqual(answer['stats']['nodes'], limits['max_nodes'])
        for name in ('max_nodes', 'max_pivots', 'max_branch_depth'):
            for value in (-1, True, 1.5):
                with self.assertRaises(ValueError):
                    search_positive_euler(raw, **{name: value})
        for value in ([True], [0, 0], [1], [-1], (), 'all'):
            with self.assertRaises(ValueError):
                search_positive_euler(raw, allowed_branch_tetrahedra=value)

    def test_multiple_global_vertices_and_positive_witness_mutations(self):
        cases = [boundary_cap(*layered_torus(2))[0], interior_vertex_torus()[0]]
        for raw in cases:
            answer = search_positive_euler(raw, max_pivots=20000)
            self.assertEqual(answer['status'], 'POSITIVE_EULER', answer)
            self.assertGreater(answer['stats']['vertices'], 1)
            self.assertTrue(verify_normal_propagation_certificate(raw, answer['certificate']))
        raw, _ = layered_torus(1)
        proof = search_positive_euler(raw)['certificate']
        for mutate in (lambda p: p.__setitem__('anchors', [0]),
                       lambda p: p['coordinates'][0].__setitem__(0, -1),
                       lambda p: p.__setitem__('coordinates', [[2*x for x in row] for row in p['coordinates']])):
            bad = deepcopy(proof)
            mutate(bad)
            self.assertFalse(verify_normal_propagation_certificate(raw, bad))

    def test_cancellation_propagates_in_search_and_replay(self):
        class Cancelled(ValueError):
            pass
        for operation in (lambda cb: search_positive_euler(self.trefoil, check=cb),
                          lambda cb: verify_normal_propagation_certificate(
                              self.trefoil, self.negative['certificate'], check=cb)):
            calls = 0
            def cancel():
                nonlocal calls
                calls += 1
                if calls == 12:
                    raise Cancelled('caller stopped')
            with self.assertRaises(Cancelled):
                operation(cancel)

    @unittest.skipUnless(importlib.util.find_spec('regina'), 'optional Regina fixture cross-check')
    def test_optional_native_fixture_topology(self):
        import regina
        from normal_orbit_research.fixtures import regina_triangulation
        torus = regina_triangulation(branching_torus())
        trefoil = regina_triangulation(self.trefoil)
        self.assertEqual(torus.isoSig(), 'fLHgkacdeenkavj')
        self.assertTrue(torus.isSolidTorus())
        self.assertEqual(trefoil.isoSig(), 'fLHPccdeeeqcieh')
        self.assertFalse(trefoil.isSolidTorus())
        # Reimport/export does not alter any source face pairing.
        self.assertEqual(export_triangulation(trefoil), self.trefoil)


if __name__ == '__main__':
    unittest.main()
