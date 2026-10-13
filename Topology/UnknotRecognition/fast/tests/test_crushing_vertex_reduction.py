"""Authenticated one-vertex preprocessing and its shared crushing allowance."""
from copy import deepcopy
import unittest
from unittest.mock import patch

from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_chain import verify_crushing_chain
from fastunknot.normal_crushing_search import recognize_by_crushing, verify_crushing_recognition
from fastunknot.normal_sector import SearchLimit
from fastunknot.normal_surface_geometry import _prepare


class CrushingVertexReductionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.circle = Diagram.from_pd([])
        cls.trefoil = Diagram.from_braid(2, [1, 1, 1])
        cls.result = recognize_by_crushing(cls.trefoil, max_sectors=0)

    def test_preprocessing_reaches_one_vertex_without_any_sector_search(self):
        result = self.result
        self.assertEqual(result['status'], 'INCONCLUSIVE')
        self.assertEqual(result['reason'], 'shared maximal-sector allowance exhausted')
        chain, stats = result['partial_chain'], result['stats']
        self.assertEqual(stats['sectors_attempted'], 0)
        self.assertEqual(stats['bases_attempted'], 0)
        self.assertEqual(stats['vertex_reduction_crushes'], 12)
        self.assertEqual(stats['crushing_steps'], 12)
        self.assertEqual(len(chain['triangulation']['tetrahedra']), 10)
        self.assertEqual(_prepare(chain['triangulation'], lambda: None)['vertices'], 1)
        self.assertTrue(verify_crushing_chain(self.trefoil, chain))
        counts = [stats['shelled_tetrahedra']] + [len(s['successor']['tetrahedra'])
                                               for s in chain['steps']]
        self.assertTrue(all(a > b for a, b in zip(counts, counts[1:])))

    def test_unknot_preprocessing_can_finish_with_all_search_allowances_zero(self):
        proofs = []
        for method in ('corners', 'lp'):
            result = recognize_by_crushing(self.circle, sector_method=method,
                max_sectors=0, max_bases=0, max_pivots=0, max_anchors=0)
            self.assertEqual(result['status'], 'UNKNOT')
            self.assertEqual(result['stats']['vertex_reduction_crushes'], 1)
            self.assertEqual(result['stats']['sectors_attempted'], 0)
            self.assertTrue(verify_crushing_recognition(self.circle, result['certificate']))
            proofs.append(result['certificate'])
        self.assertEqual(*proofs)
        with patch('fastunknot.normal_vertex_reduction.vertex_reduction_ray',
                   side_effect=AssertionError('producer must not run during replay')):
            self.assertTrue(verify_crushing_recognition(self.circle, proofs[0]))
            self.assertTrue(verify_crushing_chain(self.trefoil, self.result['partial_chain']))

    def test_preprocessing_obeys_shared_crush_cap_and_returns_authenticated_progress(self):
        for cap in (0, 1):
            result = recognize_by_crushing(self.trefoil, max_sectors=0, max_crushes=cap)
            self.assertEqual(result['status'], 'INCONCLUSIVE')
            self.assertEqual(result['reason'], 'shared crushing-step allowance exhausted')
            self.assertEqual(result['stats']['crushing_steps'], cap)
            self.assertEqual(result['stats']['vertex_reduction_crushes'], cap)
            self.assertEqual(len(result['partial_chain']['steps']), cap)
            self.assertEqual(result['stats']['sectors_attempted'], 0)
            self.assertTrue(verify_crushing_chain(self.trefoil, result['partial_chain']))
        exact = recognize_by_crushing(self.trefoil, max_sectors=0, max_crushes=12)
        self.assertEqual(exact['partial_chain'], self.result['partial_chain'])
        self.assertEqual(exact['reason'], 'shared maximal-sector allowance exhausted')

    def test_opt_out_retains_search_only_policy_and_flag_is_strict(self):
        result = recognize_by_crushing(self.trefoil, max_sectors=0, reduce_vertices=False)
        self.assertEqual(result['status'], 'INCONCLUSIVE')
        self.assertEqual(result['partial_chain']['steps'], [])
        self.assertEqual(len(result['partial_chain']['triangulation']['tetrahedra']), 48)
        self.assertNotIn('vertex_reduction_calls', result['stats'])
        for value in (None, 0, 1, 'yes', [], {}):
            with self.subTest(value=value), self.assertRaises(ValueError):
                recognize_by_crushing(self.circle, reduce_vertices=value)

    def test_preprocessing_and_later_sector_search_share_one_crush_allowance(self):
        from fastunknot.normal_vertex_reduction import vertex_reduction_ray
        from tests.test_normal_crushing_search import REDUCTION_RAY

        def select_real_ray(source, *, check):
            if len(source['tetrahedra']) == 5:
                return dict(status='POSITIVE_EULER', coordinates=REDUCTION_RAY)
            return vertex_reduction_ray(source, check=check)

        # Alter only witness discovery: the real source ray, quotient, sector
        # search, and every independent certificate check remain native.
        with patch('fastunknot.normal_vertex_reduction.vertex_reduction_ray', select_real_ray):
            partial = recognize_by_crushing(self.circle, max_crushes=1)
            complete = recognize_by_crushing(self.circle, max_crushes=2)
        self.assertEqual(partial['status'], 'INCONCLUSIVE')
        self.assertEqual(partial['reason'], 'shared crushing-step allowance exhausted')
        self.assertEqual(partial['stats']['vertex_reduction_crushes'], 1)
        self.assertGreater(partial['stats']['sectors_attempted'], 0)
        self.assertEqual(partial['stats']['crushing_steps'], 1)
        self.assertTrue(verify_crushing_chain(self.circle, partial['partial_chain']))
        self.assertEqual(complete['status'], 'UNKNOT')
        self.assertEqual(complete['stats']['crushing_steps'], 2)
        self.assertEqual(complete['stats']['vertex_reduction_crushes'], 1)
        self.assertTrue(verify_crushing_recognition(self.circle, complete['certificate']))

    def test_forged_preprocessing_ray_cannot_bypass_existing_crushing_checks(self):
        forged = dict(status='POSITIVE_EULER', coordinates=[[0]*7 for _ in range(5)])
        with patch('fastunknot.normal_vertex_reduction.vertex_reduction_ray', return_value=forged):
            with self.assertRaises((ValueError, ArithmeticError)):
                recognize_by_crushing(self.circle)
        chain = deepcopy(self.result['partial_chain'])
        chain['steps'][0]['coordinates'][0][0] += 1
        self.assertFalse(verify_crushing_chain(self.trefoil, chain))

    def test_caller_exceptions_inside_preprocessing_escape_unchanged(self):
        class StopNow(BaseException):
            pass
        for error in (SearchLimit('caller'), ValueError('caller'), StopNow('caller')):
            entered = False

            def producer(source, *, check):
                nonlocal entered
                entered = True
                check()
                raise AssertionError('callback must interrupt')

            def callback():
                if entered:
                    raise error

            with patch('fastunknot.normal_vertex_reduction.vertex_reduction_ray', producer):
                with self.assertRaises(type(error)) as caught:
                    recognize_by_crushing(self.circle, check=callback)
                self.assertIs(caught.exception, error)


if __name__ == '__main__':
    unittest.main()
