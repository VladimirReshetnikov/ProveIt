"""Factorwise accounting controls and genuine complete recognition proofs."""
from copy import deepcopy
from inspect import signature
from unittest import TestCase, main
from unittest.mock import patch

from fastunknot.diagram import Diagram
from fastunknot import factored_crushing as producer


class FactorAccountingTests(TestCase):
    def setUp(self):
        self.diagram = Diagram.from_braid(3, [1, 1, 1, 2, 2, 2])

    def synthetic(self, outcomes, **options):
        """Explicitly synthetic child costs; proves accounting, not topology."""
        calls = []
        def child(diagram, *, check, **kwargs):
            check()
            calls.append(kwargs)
            return deepcopy(outcomes[len(calls)-1])
        with patch.object(producer, 'recognize_by_crushing', child), patch(
                'fastunknot.factored_crushing_verify.verify_factored_crushing_recognition',
                return_value=True):
            result = producer.recognize_factored_by_crushing(self.diagram, **options)
        return result, calls

    def test_all_nine_caps_charge_failed_work_and_mixed_reductions(self):
        first = {field: 1 for fields in producer.CAP_STATS.values() for field in fields}
        first['crushing_steps'] = 2
        first.update(maximum_tableau_bits=7, peak_cached_conflicts=4,
                     maximum_ellipsoid_dimension=5)
        second = {field: 2 for fields in producer.CAP_STATS.values() for field in fields}
        second.update(crushing_steps=1, boundary_unlayerings=0,
                      maximum_tableau_bits=3, peak_cached_conflicts=6,
                      maximum_ellipsoid_dimension=2)
        caps = {cap: 3 for cap in producer.CAP_STATS}
        caps['max_crushes'] = 4
        result, calls = self.synthetic([
            dict(status='INCONCLUSIVE', stats=first, partial_chain={'test':'first'}),
            dict(status='KNOTTED', stats=second, certificate={'test':'second'})], **caps)
        self.assertEqual(result['status'], 'KNOTTED')
        self.assertEqual(len(result['factor_results']), 2)
        self.assertEqual(result['stats']['factors_inconclusive'], 1)
        self.assertEqual(result['stats']['factors_knotted'], 1)
        self.assertEqual(result['certificate']['proofs'], [dict(factor_index=1, certificate={'test':'second'})])
        for cap, fields in producer.CAP_STATS.items():
            self.assertEqual(calls[1][cap], caps[cap]-sum(first[f] for f in fields))
            self.assertEqual(sum(result['stats'][f] for f in fields), caps[cap])
        self.assertEqual(result['stats']['maximum_tableau_bits'], 7)
        self.assertEqual(result['stats']['peak_cached_conflicts'], 6)
        self.assertEqual(result['stats']['maximum_ellipsoid_dimension'], 5)

    def test_all_positive_quorum_and_partial_results(self):
        positive = dict(status='UNKNOT', stats={}, certificate={'test':'positive'})
        partial = dict(status='INCONCLUSIVE', stats={}, partial_chain={'test':'partial'})
        result, _ = self.synthetic([positive, partial])
        self.assertEqual(result['status'], 'INCONCLUSIVE')
        self.assertNotIn('certificate', result)
        self.assertEqual(len(result['factor_results']), 2)
        complete, _ = self.synthetic([positive, positive])
        self.assertEqual(complete['status'], 'UNKNOT')
        self.assertEqual([p['factor_index'] for p in complete['certificate']['proofs']], [0, 1])

    def test_negative_stops_after_needed_child_but_preserves_prior_work(self):
        result, calls = self.synthetic([dict(status='KNOTTED', stats={}, certificate={})])
        self.assertEqual(len(calls), 1)
        self.assertEqual(result['stats']['factors_total'], 2)
        self.assertEqual(result['stats']['factors_attempted'], 1)

    def test_none_remains_unbounded_and_unused_zero_caps_remain_zero(self):
        outcomes = [dict(status='INCONCLUSIVE', stats={}), dict(status='INCONCLUSIVE', stats={})]
        caps = {cap: None for cap in producer.CAP_STATS}
        _, calls = self.synthetic(outcomes, **caps)
        self.assertTrue(all(c[cap] is None for c in calls for cap in caps))
        caps = dict.fromkeys(producer.CAP_STATS, 0)
        _, calls = self.synthetic(outcomes, **caps)
        self.assertTrue(all(c[cap] == 0 for c in calls for cap in caps))

    def test_overreported_child_budget_rejected(self):
        with self.assertRaisesRegex(ArithmeticError, 'max_crushes'):
            self.synthetic([dict(status='INCONCLUSIVE', stats=dict(
                crushing_steps=1, boundary_unlayerings=1))], max_crushes=1)

    def test_defaults_and_option_coverage_track_raw_driver(self):
        expected = signature(producer.recognize_by_crushing).bind(self.diagram)
        expected.apply_defaults()
        values = {k:v for k,v in expected.arguments.items() if k not in ('diagram', 'check')}
        self.assertEqual(producer._options(self.diagram, lambda: None, {}), values)
        self.assertEqual(set(values), set(producer.CAP_STATS)|producer.POLICY_OPTIONS)
        self.assertEqual(len(producer.CAP_STATS), 9)

    def test_invalid_even_unused_controls_before_child_work(self):
        cases = [{cap: value} for cap in producer.CAP_STATS for value in (True, -1, 1.0)]
        cases += [dict(sector_quantum=0), dict(sector_method='bad'),
                  dict(reduce_vertices=1), dict(unlayer_boundary=0),
                  dict(transversal_candidate_policy='bad'),
                  dict(sector_method='transversal', tree_model='restricted'),
                  dict(lp_policy='bland', lp_fast_path_pivots=0)]
        with patch.object(producer, 'recognize_by_crushing') as child:
            for options in cases:
                with self.subTest(options=options), self.assertRaises(ValueError):
                    producer.recognize_factored_by_crushing(Diagram.from_pd([]), **options)
            child.assert_not_called()
        with self.assertRaises(TypeError):
            producer.recognize_factored_by_crushing(self.diagram, no_such_option=1)

    def test_caller_exception_identity_during_factorization_or_child(self):
        class Stop(ValueError):
            pass
        error = Stop('caller cancellation')
        def check():
            raise error
        with self.assertRaises(Stop) as caught:
            producer.recognize_factored_by_crushing(self.diagram, check=check)
        self.assertIs(caught.exception, error)
        def child(*args, **kwargs):
            raise error
        with patch.object(producer, 'recognize_by_crushing', child), self.assertRaises(Stop) as caught:
            producer.recognize_factored_by_crushing(self.diagram)
        self.assertIs(caught.exception, error)


class GenuineFactorTests(TestCase):
    def controls(self):
        options = dict.fromkeys(producer.CAP_STATS, 0)
        options.update(max_crushes=None, sector_method='transversal',
                       transversal_candidate_policy='conflicts', unlayer_boundary=True)
        return options

    def test_genuine_circle_and_two_curls_with_zero_unused_caps(self):
        from fastunknot.factored_crushing_verify import verify_factored_crushing_recognition
        for diagram, count in ((Diagram.from_pd([]), 1),
                               (Diagram.from_braid(3, [1, 2]), 2)):
            with self.subTest(count=count):
                result = producer.recognize_factored_by_crushing(diagram, **self.controls())
                self.assertEqual(result['status'], 'UNKNOT')
                self.assertTrue(verify_factored_crushing_recognition(diagram, result['certificate']))
                self.assertEqual(result['stats']['factors_attempted'], count)
                self.assertEqual(result['stats']['initial_tetrahedra'], 20*count)
                self.assertEqual(result['stats']['shelled_tetrahedra'], 5*count)
                self.assertEqual(result['stats']['crushing_steps'], count)
                self.assertEqual(result['stats']['lp_calls'], 0)
                self.assertEqual(len(result['certificate']['proofs']), count)

    def test_genuine_crushing_allowance_shared_across_positive_and_partial_child(self):
        from fastunknot.normal_crushing_chain import verify_crushing_chain
        from fastunknot.normal_crushing_search import verify_crushing_recognition
        diagram = Diagram.from_braid(3, [1, 2])
        result = producer.recognize_factored_by_crushing(
            diagram, **dict(self.controls(), max_crushes=1))
        self.assertEqual(result['status'], 'INCONCLUSIVE')
        self.assertNotIn('certificate', result)
        self.assertEqual(result['stats']['factors_attempted'], 2)
        self.assertEqual(result['stats']['crushing_steps'], 1)
        self.assertEqual(result['stats']['factors_unknot'], 1)
        self.assertEqual(result['stats']['factors_inconclusive'], 1)
        for attempted in result['factor_results']:
            child = attempted['result']
            factor = Diagram.from_pd(result['factor_pds'][attempted['factor_index']])
            if child['status'] == 'UNKNOT':
                self.assertTrue(verify_crushing_recognition(factor, child['certificate']))
            else:
                self.assertEqual(child['status'], 'INCONCLUSIVE')
                self.assertTrue(verify_crushing_chain(factor, child['partial_chain']))
                self.assertEqual(child['stats']['crushing_steps'], 0)


if __name__ == '__main__':
    main()
