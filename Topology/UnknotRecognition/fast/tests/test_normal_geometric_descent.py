"""Geometry-only first descent: real branches, exhaustive controls and replay."""
from copy import deepcopy
import gzip
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from fastunknot.diagram import Diagram
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.normal_cocycle import CocycleLimit
from fastunknot.normal_geometric_descent import (
    reduce_geometric_descent_once, _downward_candidates,
)
from fastunknot.normal_geometric_descent_verify import verify_normal_geometric_descent
from fastunknot.normal_surface_geometry import _prepare, NormalOrbitError
from fastunknot.pachner23 import pachner_23
from fastunknot.pachner32 import pachner_32
from fastunknot.pachner23_verify import verify_pachner_23
from fastunknot.pachner32_verify import verify_pachner_32
from normal_orbit_research.fixtures import layered_torus
from tests.test_normal_pachner32_verify import selfattached_fixture


MODULE = 'fastunknot.normal_geometric_descent.'


class NormalGeometricDescentTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        archive = Path(__file__).resolve().parents[1]/'strict_pachner32_research/data/generation/euler-queries.json.gz'
        with gzip.open(archive, 'rt') as stream:
            cls.trefoil = json.load(stream)['records'][0]['source']

    def test_genuine_trefoil_escape_and_frame_accounting(self):
        source = self.trefoil
        self.assertEqual(_downward_candidates(source, lambda: None), [])
        result = reduce_geometric_descent_once(source)
        self.assertEqual(result['status'], 'REDUCED')
        packet, stats = result['certificate'], result['stats']
        self.assertTrue(verify_normal_geometric_descent(source, packet))
        self.assertEqual([len(s['triangulation']['tetrahedra']) for s in packet['steps']], [9, 8, 7])
        self.assertEqual((stats['initial_tetrahedra'], stats['remaining_tetrahedra']), (8, 7))
        self.assertEqual((stats['macros'], stats['upward_moves'], stats['downward_moves']), (1, 1, 2))
        self.assertEqual(stats['search_nodes'], 1+stats['verified_upward_candidates']+
                         stats['verified_downward_candidates']-1)
        self.assertFalse(stats['search_complete'])

    def test_later_first_contraction_must_be_explored(self):
        source = self.trefoil
        up = pachner_23(source, 0, 2)['triangulation']
        ports = _downward_candidates(up, lambda: None)
        self.assertEqual((ports[0], ports[-1]), ((0, 0, 3), (6, 0, 1)))
        # The inverse expansion is valid but provides no final D. Put it first:
        # a greedy first-D-only implementation would lose this real UDD path.
        inverse = pachner_32(up, ports[-1][0], list(ports[-1][1:]))
        self.assertTrue(verify_pachner_32(up, inverse['triangulation'], inverse['certificate']))
        self.assertEqual(_downward_candidates(inverse['triangulation'], lambda: None), [])

        def inverse_first(raw, check):
            candidates = _downward_candidates(raw, check)
            return candidates[-1:]+candidates[:-1] if len(raw['tetrahedra']) == 9 else candidates

        with patch(MODULE+'_downward_candidates', side_effect=inverse_first):
            result = reduce_geometric_descent_once(source)
        self.assertEqual(result['status'], 'REDUCED')
        self.assertTrue(verify_normal_geometric_descent(source, result['certificate']))
        self.assertEqual(result['certificate']['steps'][0]['certificate']['face'], 2)
        self.assertEqual(result['stats']['verified_downward_candidates'], 7)

    def test_direct_contraction_with_all_region_selfattachments(self):
        source, old = selfattached_fixture()
        result = reduce_geometric_descent_once(source)
        self.assertEqual(result['status'], 'REDUCED')
        self.assertEqual(result['certificate']['successor'], old['successor'])
        self.assertEqual(len(result['certificate']['steps']), 1)
        self.assertEqual(result['stats']['search_nodes'], 1)
        self.assertEqual((result['stats']['upward_moves'], result['stats']['downward_moves']), (0, 1))
        self.assertTrue(verify_normal_geometric_descent(source, result['certificate']))

    def test_complete_small_source_exhaustion_and_flagless_api(self):
        source = layered_torus(1)[0]
        with patch(MODULE+'pachner_23', side_effect=AssertionError), \
             patch(MODULE+'pachner_32', side_effect=AssertionError):
            result = reduce_geometric_descent_once(source)
        self.assertEqual(result['status'], 'UNCHANGED')
        self.assertTrue(result['stats']['search_complete'])
        self.assertEqual(result['stats']['search_nodes'], 1)
        self.assertEqual(result['stats']['macros'], 0)
        self.assertNotIn('certificate', result)
        for option in ('max_checks', 'max_work', 'max_nodes', 'max_upward'):
            with self.assertRaises(TypeError):
                reduce_geometric_descent_once(source, **{option: 0})

    def test_multiple_vertices_are_preserved(self):
        source = diagram_exterior(Diagram.from_pd([]))
        self.assertEqual(_prepare(source, lambda: None)['vertices'], 6)
        result = reduce_geometric_descent_once(source)
        self.assertEqual(result['status'], 'REDUCED')
        self.assertEqual(_prepare(result['certificate']['successor'], lambda: None)['vertices'], 6)
        self.assertTrue(verify_normal_geometric_descent(source, result['certificate']))

    def test_constructed_replay_failures_never_claim_exhaustion(self):
        for source, verifier in ((self.trefoil, 'verify_pachner_23'),
                                 (selfattached_fixture()[0], 'verify_pachner_32'),
                                 (selfattached_fixture()[0], 'verify_normal_geometric_descent')):
            with self.subTest(verifier=verifier), patch(MODULE+verifier, return_value=False):
                with self.assertRaisesRegex(ArithmeticError, 'independent'):
                    reduce_geometric_descent_once(source)

    def test_expected_candidate_rejection_does_not_skip_later_expansions(self):
        seen = []

        def reject_first(raw, t, face, *, check):
            seen.append((t, face))
            if len(seen) == 1:
                raise NormalOrbitError('expected local candidate rejection')
            return pachner_23(raw, t, face, check=check)

        with patch(MODULE+'pachner_23', side_effect=reject_first):
            result = reduce_geometric_descent_once(self.trefoil)
        self.assertEqual(seen, [(0, 0), (0, 1), (0, 2)])
        self.assertEqual(result['stats']['upward_rejections'], 1)
        self.assertTrue(verify_normal_geometric_descent(self.trefoil, result['certificate']))

    def test_no_cochain_cover_or_normal_discovery_and_producer_free_replay(self):
        with patch('fastunknot.cocycle_transport.transport_cocycle', side_effect=AssertionError), \
             patch('fastunknot.pachner_cover_search.find_pachner_descent', side_effect=AssertionError), \
             patch('fastunknot.normal_disk_kernel.normal_compressing_disk_count', side_effect=AssertionError):
            result = reduce_geometric_descent_once(self.trefoil)
        with patch(MODULE+'reduce_geometric_descent_once', side_effect=AssertionError), \
             patch('fastunknot.pachner23.pachner_23', side_effect=AssertionError), \
             patch('fastunknot.pachner32.pachner_32', side_effect=AssertionError):
            self.assertTrue(verify_normal_geometric_descent(self.trefoil, result['certificate']))
        self.assertEqual(set(result), {'status', 'certificate', 'stats'})
        self.assertNotIn('attempts', result)

    def test_work_counts_callbacks_and_input_is_not_aliased(self):
        source, _ = selfattached_fixture()
        saved = deepcopy(source)
        calls = [0]
        def tick():
            calls[0] += 1
        result = reduce_geometric_descent_once(source, check=tick)
        self.assertEqual(result['stats']['search_work'], calls[0])
        self.assertEqual(result, reduce_geometric_descent_once(deepcopy(source)))
        record = next(r for row in result['certificate']['successor']['tetrahedra'] for r in row if r)
        record['permutation'][0] = 99
        self.assertEqual(source, saved)

    def test_callback_identity_across_all_nested_operations(self):
        operations = (('prepare', None, None),
            ('up_constructor', 'pachner_23', pachner_23),
            ('down_constructor', 'pachner_32', pachner_32),
            ('up_verifier', 'verify_pachner_23', verify_pachner_23),
            ('down_verifier', 'verify_pachner_32', verify_pachner_32),
            ('packet_verifier', 'verify_normal_geometric_descent', verify_normal_geometric_descent))
        for phase, name, original in operations:
            for error in (NormalOrbitError('cancel'), CocycleLimit('cancel'),
                          ValueError('cancel'), KeyboardInterrupt('cancel')):
                with self.subTest(phase=phase, error=type(error)):
                    active = [phase == 'prepare']
                    def callback():
                        if active[0]:
                            raise error
                    def wrapped(*args, **kwargs):
                        active[0] = True
                        return original(*args, **kwargs)
                    if name is None:
                        with self.assertRaises(type(error)) as caught:
                            reduce_geometric_descent_once(self.trefoil, check=callback)
                    else:
                        with patch(MODULE+name, side_effect=wrapped):
                            with self.assertRaises(type(error)) as caught:
                                reduce_geometric_descent_once(self.trefoil, check=callback)
                    self.assertIs(caught.exception, error)

    def test_late_cancellation_and_invalid_source_do_not_return_unchanged(self):
        source = layered_torus(1)[0]
        calls = [0]
        def count():
            calls[0] += 1
        reduce_geometric_descent_once(source, check=count)
        total = calls[0]
        error = NormalOrbitError('last checkpoint')
        calls[0] = 0
        def stop():
            count()
            if calls[0] == total:
                raise error
        with self.assertRaises(NormalOrbitError) as caught:
            reduce_geometric_descent_once(source, check=stop)
        self.assertIs(caught.exception, error)
        for bad in (None, {}, {'tetrahedra': []}):
            with self.assertRaises(NormalOrbitError):
                reduce_geometric_descent_once(bad)


if __name__ == '__main__':
    unittest.main()
