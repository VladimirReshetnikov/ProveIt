"""Whole LP crushing: source authentication, budgets, coverage and replay."""
from copy import deepcopy
from fractions import Fraction
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from fastunknot.diagram import Diagram
from fastunknot import normal_crushing_search as search_module
from fastunknot.normal_crushing_search import recognize_by_crushing, verify_crushing_recognition
from fastunknot.normal_crushing_chain import make_crushing_chain, verify_crushing_chain
from fastunknot.normal_euler import decide_sector_euler
from fastunknot.normal_euler_verify import verify_sector_euler_certificate
from fastunknot.normal_sector import build_sector_kernel, sector_rays, SearchLimit, _source_hash
from fastunknot.normal_sector_verify import verify_sector_exhaustion
from fastunknot.normal_surface_geometry import _coordinates, NormalOrbitError
from tests.test_normal_crushing_search import REDUCTION_RAY


def empty_lp_stats(**updates):
    result = dict(lp_calls=0, lp_pivots=0, anchors_tested=0, reused_anchors=0,
                  envelope_calls=0, lp_tableau_updates=0, maximum_tableau_bits=0)
    result.update(updates)
    return result


class CrushingEulerLPTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.diagram = Diagram.from_pd([])
        cls.results = {strategy: recognize_by_crushing(cls.diagram, sector_method='lp',
                           lp_strategy=strategy, max_bases=0)
                       for strategy in ('anchors', 'envelope')}
        shelling = cls.results['anchors']['certificate']['chain']['shelling']
        cls.partial = make_crushing_chain(cls.diagram, [REDUCTION_RAY], shelling=shelling)
        cls.one_tet = cls.partial['triangulation']
        cls.sector_results = [decide_sector_euler(cls.one_tet, [[0, q]]) for q in range(3)]
        kernel = build_sector_kernel(cls.one_tet, [[0, 0]])
        cls.corner_negative = dict(schema='normal-sector-exhaustion-v1',
            source_sha256=_source_hash(cls.one_tet), allowed_types=[[0, 0]],
            phase='quadrilateral', status='NO_POSITIVE_EULER', rays=[
                dict(quadrilaterals=[rows[0][4]], euler_characteristic=
                     _coordinates(kernel.prepared, rows, lambda: None)['euler_characteristic'])
                for rows in sector_rays(kernel, phase='quadrilateral')])
        cls.false_last = dict(schema='normal-sector-euler-lp-v1',
            status='NO_POSITIVE_EULER', source_sha256=_source_hash(cls.one_tet),
            allowed_types=[[0, 2]], proof_kind='envelope', multipliers=[])
        cls.false_negative = dict(schema='diagram-crushing-recognition-v1',
            status='KNOTTED', chain=cls.partial, exhaustion=[cls.corner_negative,
                cls.sector_results[1]['certificate'], cls.false_last])

    def test_actual_circle_both_strategies_replay_with_no_corner_budget(self):
        for strategy, result in self.results.items():
            self.assertEqual(result['status'], 'UNKNOT')
            self.assertEqual(result['stats']['bases_attempted'], 0)
            self.assertEqual(result['stats']['lp_pivots'], 2)
            self.assertEqual(result['stats']['crushing_steps'], 2)
            self.assertEqual([None if step['successor'] is None else
                              len(step['successor']['tetrahedra'])
                              for step in result['certificate']['chain']['steps']], [4, None])
            self.assertTrue(verify_crushing_recognition(self.diagram, result['certificate']))
        self.assertEqual(self.results['anchors']['stats']['anchors_tested'], 2)
        self.assertEqual(self.results['envelope']['stats']['anchors_tested'], 0)
        self.assertEqual(self.results['envelope']['stats']['envelope_calls'], 2)

    def test_pivot_and_anchor_caps_are_shared_across_actual_crushes(self):
        for cap, metric in (('max_pivots', 'lp_pivots'), ('max_anchors', 'anchors_tested')):
            for limit in (0, 1, 2):
                result = recognize_by_crushing(self.diagram, sector_method='lp',
                    lp_strategy='anchors', max_bases=0, **{cap: limit})
                self.assertEqual(result['stats'][metric], limit)
                if limit == 2:
                    self.assertEqual(result['status'], 'UNKNOT')
                    self.assertTrue(verify_crushing_recognition(self.diagram, result['certificate']))
                else:
                    self.assertEqual(result['status'], 'INCONCLUSIVE')
                    self.assertNotIn('certificate', result)
                    self.assertEqual(result['stats']['crushing_steps'], limit)
                    self.assertTrue(verify_crushing_chain(self.diagram, result['partial_chain']))
                    self.assertEqual(len(result['partial_chain']['triangulation']['tetrahedra']),
                                     5 if limit == 0 else 4)
        envelope = recognize_by_crushing(self.diagram, sector_method='lp',
                                        max_anchors=0, max_bases=0)
        self.assertEqual(envelope['status'], 'UNKNOT')
        self.assertEqual(envelope['stats']['anchors_tested'], 0)
        exhausted = recognize_by_crushing(self.diagram, sector_method='lp',
                                         max_pivots=0, max_bases=None)
        self.assertEqual(exhausted['status'], 'INCONCLUSIVE')
        self.assertEqual(exhausted['stats']['crushing_steps'], 0)
        # LP-only caps are unused by the retained corner backend.
        corners = recognize_by_crushing(self.diagram, max_pivots=0, max_anchors=0)
        self.assertEqual(corners['status'], 'UNKNOT')

    def test_strict_lp_api_validation(self):
        for name in ('max_pivots', 'max_anchors'):
            for value in (True, False, -1, 1.0, '1', [], {}):
                with self.subTest(name=name, value=value), self.assertRaises(ValueError):
                    recognize_by_crushing(self.diagram, sector_method='lp', **{name: value})
        for name in ('sector_method', 'lp_strategy'):
            for value in (None, True, 0, [], {}, 'unknown'):
                with self.subTest(name=name, value=value), self.assertRaises(ValueError):
                    recognize_by_crushing(self.diagram, **{name: value})
        for value in (True, 0, -1, 1.0, '1'):
            with self.assertRaises(ValueError):
                recognize_by_crushing(self.diagram, sector_method='lp', sector_quantum=value)

    def test_real_mixed_negative_sectors_cannot_hide_the_positive_sector(self):
        self.assertTrue(verify_crushing_chain(self.diagram, self.partial))
        self.assertEqual([r['status'] for r in self.sector_results],
                         ['NO_POSITIVE_EULER', 'NO_POSITIVE_EULER', 'POSITIVE_EULER'])
        self.assertTrue(verify_sector_exhaustion(self.one_tet, self.corner_negative))
        for result in self.sector_results:
            self.assertTrue(verify_sector_euler_certificate(self.one_tet, result['certificate']))
        self.assertFalse(verify_sector_euler_certificate(self.one_tet, self.false_last))
        self.assertFalse(verify_crushing_recognition(self.diagram, self.false_negative))
        actual_positive = deepcopy(self.false_negative)
        actual_positive['exhaustion'][-1] = self.sector_results[-1]['certificate']
        self.assertFalse(verify_crushing_recognition(self.diagram, actual_positive))

    def test_global_coverage_dispatches_all_schemas_without_weakening_full_assignment(self):
        # Isolate outer coverage and dispatch. This deliberately forged
        # wrapper is *not* mathematical recognition evidence; native replay
        # rejects its claim that the nonzero one-tet Q type is forced zero.
        proof = deepcopy(self.false_negative)
        inner = dict(schema='normal-sector-euler-lp-v1', status='NO_POSITIVE_EULER',
            source_sha256=_source_hash(self.one_tet), allowed_types=[],
            proof_kind='envelope', multipliers=[])
        wrapper = dict(schema='normal-sector-euler-reduction-v1', status='NO_POSITIVE_EULER',
            source_sha256=_source_hash(self.one_tet), allowed_types=[[0, 1]],
            matching_support_certificate=dict(schema='normal-sector-matching-support-v1',
                source_sha256=_source_hash(self.one_tet), allowed_types=[[0, 1]],
                steps=[dict(row_combination=[[0, 1, 1]], forced_indices=[0])]),
            euler_certificate=inner)
        proof['exhaustion'][1] = wrapper
        self.assertFalse(verify_crushing_recognition(self.diagram, proof))
        with patch.object(search_module, 'verify_sector_euler_certificate', return_value=True) as replay:
            self.assertTrue(verify_crushing_recognition(self.diagram, proof))
            self.assertEqual(replay.call_count, 2)
            self.assertEqual([call.args[1]['schema'] for call in replay.call_args_list],
                             ['normal-sector-euler-reduction-v1', 'normal-sector-euler-lp-v1'])
            for mutation in ('missing', 'duplicate', 'order', 'partial', 'bool', 'extra', 'positive'):
                bad = deepcopy(proof)
                packets = bad['exhaustion']
                if mutation == 'missing': packets.pop()
                elif mutation == 'duplicate': packets[-1] = deepcopy(packets[0])
                elif mutation == 'order': packets.reverse()
                elif mutation == 'partial': packets[1]['allowed_types'] = []
                elif mutation == 'bool': packets[1]['allowed_types'][0][0] = False
                elif mutation == 'extra': packets.append(deepcopy(packets[-1]))
                else: packets[-1] = self.sector_results[-1]['certificate']
                self.assertFalse(verify_crushing_recognition(self.diagram, bad), mutation)

    def test_sabotaged_false_lp_negative_fails_local_and_final_independent_replay(self):
        def false_negative(source, allowed, **kwargs):
            return dict(status='NO_POSITIVE_EULER', stats=empty_lp_stats(),
                certificate=dict(schema='normal-sector-euler-lp-v1', status='NO_POSITIVE_EULER',
                    source_sha256=_source_hash(source), allowed_types=[list(p) for p in allowed],
                    proof_kind='envelope', multipliers=[]))
        with patch('fastunknot.normal_euler.decide_sector_euler', false_negative):
            with self.assertRaisesRegex(ArithmeticError, 'independent Euler-LP replay failed'):
                recognize_by_crushing(self.diagram, sector_method='lp', sector_order='canonical')
        # Deliberately bypass the first gate only; the ordinary final checker
        # must still reject the complete collection of fabricated negatives.
        final = [False]
        final_calls = []
        def per_sector(source, packet, *, check):
            return (verify_sector_euler_certificate(source, packet, check=check)
                    if final[0] else True)
        def final_replay(diagram, packet, *, check):
            final_calls.append(packet)
            final[0] = True
            try:
                return verify_crushing_recognition(diagram, packet, check=check)
            finally:
                final[0] = False
        with patch('fastunknot.normal_euler.decide_sector_euler', false_negative), \
             patch.object(search_module, 'verify_sector_euler_certificate', per_sector), \
             patch.object(search_module, 'verify_crushing_recognition', final_replay):
            with self.assertRaisesRegex(ArithmeticError, 'independent crushing recognition replay failed'):
                recognize_by_crushing(self.diagram, sector_method='lp', max_sectors=None,
                                     sector_quantum=None, max_pivots=None, max_anchors=None)
        self.assertEqual(len(final_calls), 1)
        self.assertEqual(len(final_calls[0]['exhaustion']), 3**5)

    def test_matching_reduction_wrapper_on_the_actual_first_trefoil_sector(self):
        diagram = Diagram.from_braid(2, [1, 1, 1])
        observed = []
        def replay(source, packet, *, check):
            observed.append(deepcopy(packet))
            return verify_sector_euler_certificate(source, packet, check=check)
        with patch.object(search_module, 'verify_sector_euler_certificate', replay):
            result = recognize_by_crushing(diagram, sector_method='lp', max_sectors=1,
                                          max_bases=0, max_pivots=64, max_anchors=64)
        self.assertEqual(result['status'], 'INCONCLUSIVE')
        self.assertEqual(result['stats']['bases_attempted'], 0)
        self.assertEqual(result['stats']['matching_support_reductions'], 1)
        self.assertEqual(result['stats']['forced_zero_types'], 40)
        self.assertEqual(result['stats']['crushing_steps'], 1)
        self.assertEqual(len(observed), 1)
        self.assertEqual(observed[0]['schema'], 'normal-sector-euler-reduction-v1')
        self.assertEqual(len(observed[0]['allowed_types']), 48)
        self.assertEqual(len(observed[0]['euler_certificate']['allowed_types']), 8)
        self.assertTrue(verify_crushing_chain(diagram, result['partial_chain']))

    def test_fair_lp_restarts_charge_all_synthetic_work_before_a_real_positive(self):
        # Synthetic unfinished jobs isolate scheduling/accounting. The final
        # witness and all geometry still come from actual native LP/replay.
        calls = []
        def delayed(source, allowed, *, strategy, max_pivots, max_anchors, check):
            calls.append((max_pivots, max_anchors))
            if min(max_pivots, max_anchors) < 2:
                used = min(1, max_pivots, max_anchors)
                return dict(status='INCONCLUSIVE', reason='synthetic per-attempt allowance',
                            stats=empty_lp_stats(lp_calls=1, lp_pivots=used, anchors_tested=used))
            return decide_sector_euler(source, allowed, strategy=strategy,
                max_pivots=max_pivots, max_anchors=max_anchors, check=check)
        with patch('fastunknot.normal_euler.decide_sector_euler', delayed):
            for cap in (16, 18):
                calls.clear()
                result = recognize_by_crushing(self.diagram, sector_method='lp',
                    lp_strategy='anchors', sector_order='canonical', sector_quantum=1,
                    max_bases=0, max_sectors=16, max_pivots=cap, max_anchors=cap)
                if cap == 16:
                    self.assertEqual(result['status'], 'INCONCLUSIVE')
                    self.assertEqual(result['stats']['crushing_steps'], 0)
                    self.assertEqual(result['stats']['lp_pivots'], 16)
                    self.assertTrue(verify_crushing_chain(self.diagram, result['partial_chain']))
                else:
                    self.assertEqual(result['status'], 'UNKNOT')
                    self.assertEqual(result['stats']['sector_restarts'], 1)
                    self.assertEqual(result['stats']['sector_quantum_exhaustions'], 16)
                    self.assertEqual(result['stats']['lp_pivots'], 17)
                    self.assertEqual(result['stats']['anchors_tested'], 17)
                    self.assertEqual(calls[-1], (2, 2))
                    self.assertTrue(verify_crushing_recognition(self.diagram, result['certificate']))

    def test_nested_matching_euler_and_support_descent_preserve_callback_identity(self):
        from fastunknot.sector_matching_support import matching_support
        from fastunknot.source_kernel import SourceKernel
        stages = [('fastunknot.sector_matching_support.matching_support', matching_support),
                  ('fastunknot.normal_crushing_search.verify_sector_euler_certificate',
                   verify_sector_euler_certificate),
                  ('fastunknot.source_kernel.SourceKernel.extreme_witness', SourceKernel.extreme_witness)]
        for target, original in stages:
            for kind in (ValueError, NormalOrbitError, SearchLimit):
                active = [False]
                error = kind('caller cancellation inside nested LP work')
                def watched(*args, **kwargs):
                    active[0] = True
                    try:
                        return original(*args, **kwargs)
                    finally:
                        active[0] = False
                def check():
                    if active[0]:
                        raise error
                with patch(target, watched), self.assertRaises(kind) as caught:
                    recognize_by_crushing(self.diagram, sector_method='lp', check=check)
                self.assertIs(caught.exception, error)

    def test_256_entry_dual_cache_eviction_preserves_every_anchor_inequality(self):
        # An abstract cone q>=0, Iq=0 has no nonzero vector. The 300 objectives
        # (a,299-a) form an antichain; repeating the first after eviction must
        # solve it again. This tests the cache policy, not a triangulation.
        objectives = [(a, 299-a) for a in range(300)]+[(0, 299)]
        kernel = SimpleNamespace(support=((0, 0), (1, 0)), cycle_rows=((1, 0), (0, 1)),
            groups=(tuple(range(len(objectives))),), stats={},
            potentials={i: tuple(-x for x in objective) for i, objective in enumerate(objectives)})
        with patch('fastunknot.normal_euler.build_sector_kernel', return_value=kernel), \
             patch('fastunknot.normal_euler._euler_model', return_value=((0, 0), (1,))):
            result = decide_sector_euler({}, [], strategy='anchors')
        self.assertEqual(result['status'], 'NO_POSITIVE_EULER')
        self.assertEqual(result['stats']['anchors_tested'], 301)
        self.assertEqual(result['stats']['lp_calls'], 301)
        self.assertEqual(result['stats']['reused_anchors'], 0)
        for index, (record, objective) in enumerate(zip(result['certificate']['duals'], objectives)):
            self.assertEqual(record['anchors'], [index])
            self.assertTrue(all(Fraction(*dual) >= target
                                for dual, target in zip(record['multipliers'], objective)))


if __name__ == '__main__':
    unittest.main()
