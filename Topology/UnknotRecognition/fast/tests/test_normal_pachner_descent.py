from copy import deepcopy
import gzip
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from fastunknot.diagram import Diagram
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.normal_cocycle import CocycleLimit
from fastunknot.normal_pachner_descent import reduce_pachner_descent_once
from fastunknot.normal_pachner_descent_verify import verify_normal_pachner_descent
from fastunknot.normal_pachner32 import reduce_pachner32_once
from fastunknot.normal_surface_geometry import _prepare, NormalOrbitError
from fastunknot.pachner_cover_search import find_pachner_descent
from normal_orbit_research.fixtures import layered_torus
from tests.test_normal_pachner32_verify import selfattached_fixture


class NormalPachnerDescentTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        archive = Path(__file__).resolve().parents[1]/'strict_pachner32_research/data/generation/euler-queries.json.gz'
        with gzip.open(archive, 'rt') as stream:
            cls.sources = [row['source'] for row in json.load(stream)['records']]

    def test_three_genuine_strict32_terminal_sources_escape(self):
        for source, count in zip(self.sources, (8, 12, 17)):
            with self.subTest(tetrahedra=count):
                self.assertEqual(len(source['tetrahedra']), count)
                self.assertEqual(reduce_pachner32_once(source)['status'], 'UNCHANGED')
                result = reduce_pachner_descent_once(source)
                self.assertEqual(result['status'], 'REDUCED')
                packet = result['certificate']
                self.assertTrue(verify_normal_pachner_descent(source, packet))
                self.assertEqual(result['stats']['initial_tetrahedra'], count)
                self.assertEqual(result['stats']['remaining_tetrahedra'], count-1)
                self.assertEqual(result['stats']['upward_moves'], 1)
                self.assertEqual(result['stats']['downward_moves'], 2)
                self.assertEqual(result['stats']['macros'], 1)
                self.assertFalse(result['stats']['search_complete'])
                moves = packet['certificate']['moves']
                self.assertEqual([len(step['triangulation']['tetrahedra']) for step in moves],
                                 [count+1, count, count-1])
                self.assertTrue(all(all(value == 0 for row in step['transport']['heights']
                                        for value in row) for step in moves))

    def test_direct_downward_selfattached_region(self):
        source, old = selfattached_fixture()
        result = reduce_pachner_descent_once(source)
        self.assertEqual(result['status'], 'REDUCED')
        self.assertEqual(result['stats']['upward_moves'], 0)
        self.assertEqual(result['stats']['downward_moves'], 1)
        self.assertEqual(result['certificate']['successor'], old['successor'])
        self.assertTrue(verify_normal_pachner_descent(source, result['certificate']))

    def test_full_exhaustion_at_small_valid_source(self):
        source = layered_torus(1)[0]
        result = reduce_pachner_descent_once(source)
        self.assertEqual(result['status'], 'UNCHANGED')
        self.assertNotIn('certificate', result)
        stats = result['stats']
        self.assertTrue(stats['search_complete'])
        self.assertEqual(stats['initial_tetrahedra'], stats['remaining_tetrahedra'])
        self.assertEqual(stats['macros'], 0)
        self.assertEqual(stats['upward_moves'], 0)
        self.assertEqual(stats['downward_moves'], 0)
        self.assertGreater(stats['search_nodes'], 0)
        self.assertGreater(stats['search_work'], 0)

    def test_fixed_policy_has_zero_heights_and_no_resource_caps(self):
        source, _ = selfattached_fixture()
        with patch('fastunknot.normal_pachner_descent.find_pachner_descent',
                   wraps=find_pachner_descent) as call:
            result = reduce_pachner_descent_once(source)
        args, options = call.call_args
        self.assertEqual(args, (source, [[0]*4 for _ in source['tetrahedra']]))
        self.assertEqual({k: v for k, v in options.items() if k != 'check'},
            dict(max_upward=1, max_region_size=None, method='sleep', max_nodes=None,
                 max_regions=None, max_work=None, cover_backend='oracle', max_oracle_states=None))
        self.assertEqual(result['status'], 'REDUCED')

    def test_any_vertex_count_is_supported(self):
        source = diagram_exterior(Diagram.from_pd([]))
        before = _prepare(source, lambda: None)['vertices']
        self.assertEqual(before, 6)
        result = reduce_pachner_descent_once(source)
        self.assertEqual(result['status'], 'REDUCED')
        self.assertEqual(_prepare(result['certificate']['successor'], lambda: None)['vertices'], before)
        self.assertTrue(verify_normal_pachner_descent(source, result['certificate']))

    def test_partial_search_cannot_claim_complete_unchanged(self):
        source = layered_torus(1)[0]
        for status in ('INCONCLUSIVE', 'COMPLETE_BOUNDED_LOCAL_DESCENT', 'ENDPOINT_SELECTED'):
            with self.subTest(status=status), patch(
                    'fastunknot.normal_pachner_descent.find_pachner_descent',
                    return_value=dict(status=status, reason='incomplete')):
                with self.assertRaisesRegex(ArithmeticError, 'did not complete'):
                    reduce_pachner_descent_once(source)

    def test_independent_rejection_and_unexpected_search_error(self):
        source, _ = selfattached_fixture()
        with patch('fastunknot.normal_pachner_descent.verify_normal_pachner_descent', return_value=False):
            with self.assertRaisesRegex(ArithmeticError, 'independent replay'):
                reduce_pachner_descent_once(source)
        error = RuntimeError('search implementation failed')
        with patch('fastunknot.normal_pachner_descent.find_pachner_descent', side_effect=error):
            with self.assertRaises(RuntimeError) as caught:
                reduce_pachner_descent_once(source)
        self.assertIs(caught.exception, error)

    def test_invalid_source_and_flagless_signature(self):
        source, _ = selfattached_fixture()
        malformed = deepcopy(source)
        next(r for row in malformed['tetrahedra'] for r in row if r is not None)['tetrahedron'] = True
        for bad in (None, {}, {'tetrahedra': []}, malformed):
            with self.assertRaises(NormalOrbitError):
                reduce_pachner_descent_once(bad)
        for options in ({'max_upward': 2}, {'max_nodes': 0}, {'max_work': 0}):
            with self.assertRaises(TypeError):
                reduce_pachner_descent_once(source, **options)

    def test_determinism_no_aliases_and_producer_free_replay(self):
        source, _ = selfattached_fixture();saved = deepcopy(source)
        result = reduce_pachner_descent_once(source)
        self.assertEqual(reduce_pachner_descent_once(deepcopy(source)), result)
        with patch('fastunknot.pachner_cover_search.find_pachner_descent', side_effect=AssertionError), \
             patch('fastunknot.normal_pachner_descent.reduce_pachner_descent_once', side_effect=AssertionError), \
             patch('fastunknot.pachner32.pachner_32', side_effect=AssertionError), \
             patch('fastunknot.pachner23.pachner_23', side_effect=AssertionError):
            self.assertTrue(verify_normal_pachner_descent(source, result['certificate']))
        result['certificate']['certificate']['moves'][0]['transport']['heights'][0][0] = 99
        row = next(r for tet in result['certificate']['successor']['tetrahedra'] for r in tet if r is not None)
        row['permutation'][0] = 99
        self.assertEqual(source, saved)

    def test_callback_identity_in_each_nested_phase(self):
        source, _ = selfattached_fixture()
        for phase in ('prepare', 'search', 'verifier'):
            for error in (NormalOrbitError('cancel'), CocycleLimit('cancel'),
                          ValueError('cancel'), RuntimeError('cancel'), KeyboardInterrupt('cancel')):
                with self.subTest(phase=phase, error=type(error)):
                    active = [phase == 'prepare']

                    def callback():
                        if active[0]:
                            raise error

                    def search(*args, **kwargs):
                        active[0] = phase == 'search'
                        return find_pachner_descent(*args, **kwargs)

                    def verifier(triangulation, packet, *, check):
                        active[0] = phase == 'verifier'
                        return verify_normal_pachner_descent(triangulation, packet, check=check)

                    with patch('fastunknot.normal_pachner_descent.find_pachner_descent', side_effect=search), \
                         patch('fastunknot.normal_pachner_descent.verify_normal_pachner_descent', side_effect=verifier):
                        with self.assertRaises(type(error)) as caught:
                            reduce_pachner_descent_once(source, check=callback)
                    self.assertIs(caught.exception, error)

    def test_late_callback_is_not_relabelled_as_a_search_miss(self):
        for source in (selfattached_fixture()[0], layered_torus(1)[0]):
            count = [0]

            def tick():
                count[0] += 1

            reduce_pachner_descent_once(source, check=tick)
            total = count[0]
            for stop in (total//2, total):
                count[0] = 0;error = CocycleLimit('caller cancellation')

                def callback():
                    tick()
                    if count[0] == stop:
                        raise error

                with self.assertRaises(CocycleLimit) as caught:
                    reduce_pachner_descent_once(source, check=callback)
                self.assertIs(caught.exception, error)


if __name__ == '__main__':
    unittest.main()
