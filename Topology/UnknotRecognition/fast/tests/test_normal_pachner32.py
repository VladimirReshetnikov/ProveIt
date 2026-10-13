from copy import deepcopy
import gzip
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from fastunknot.diagram import Diagram
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.normal_pachner32 import reduce_pachner32_once
from fastunknot.normal_pachner32_verify import verify_normal_pachner32
from fastunknot.normal_surface_geometry import _prepare, NormalOrbitError
from fastunknot.pachner32 import pachner_32
from normal_orbit_research.fixtures import layered_torus
from tests.test_normal_pachner32_verify import selfattached_fixture


class NormalPachner32Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        root = Path(__file__).resolve().parents[2]
        audit = json.loads((root / 'synthesis/data/boundary-unlayer-audit.json').read_text())
        cls.sources = {
            row['id']: row['arms']['baseline']['result']['certificate']['chain']['triangulation']
            for row in audit['diagrams'] if row['id'] in ('trefoil', 'figure_eight')}
        path = root / 'fast/conflict_composition_research/data/generation/tt-state.json.gz'
        with gzip.open(path, 'rt') as stream:
            cls.sources['two_trefoils'] = json.load(stream)['chain']['triangulation']

    def test_genuine_terminal_traces_and_independent_packets(self):
        for name, expected in (('trefoil', [10, 9, 8]),
                               ('figure_eight', [13, 12]),
                               ('two_trefoils', [23, 22, 21, 20, 19, 18, 17])):
            with self.subTest(name=name):
                source = deepcopy(self.sources[name])
                trace = [len(source['tetrahedra'])]
                for _ in range(len(expected)):
                    result = reduce_pachner32_once(source)
                    if result['status'] == 'UNCHANGED':
                        self.assertTrue(result['stats']['scan_complete'])
                        self.assertEqual(result['stats']['moves'], 0)
                        self.assertEqual(result['stats']['candidate_tests'], 0)
                        self.assertNotIn('certificate', result)
                        break
                    self.assertEqual(result['status'], 'REDUCED')
                    packet = result['certificate']
                    self.assertTrue(verify_normal_pachner32(source, packet))
                    self.assertEqual(result['stats']['initial_tetrahedra'], trace[-1])
                    self.assertEqual(result['stats']['remaining_tetrahedra'], trace[-1]-1)
                    self.assertEqual(result['stats']['moves'], 1)
                    self.assertFalse(result['stats']['scan_complete'])
                    source = packet['successor']
                    trace.append(len(source['tetrahedra']))
                else:
                    self.fail('strict scan did not terminate at the retained endpoint')
                self.assertEqual(trace, expected)

    def test_scan_continues_after_expected_invalid_first_candidate(self):
        source = self.sources['figure_eight']
        sites = []

        def first_invalid(triangulation, tetrahedron, vertices, *, check):
            sites.append((tetrahedron, vertices))
            if len(sites) == 1:
                raise NormalOrbitError('candidate does not have the required formal region')
            return pachner_32(triangulation, tetrahedron, vertices, check=check)

        with patch('fastunknot.normal_pachner32.pachner_32', side_effect=first_invalid):
            result = reduce_pachner32_once(source)
        self.assertEqual(sites, [(4, [0, 2]), (10, [1, 3])])
        self.assertEqual(result['status'], 'REDUCED')
        self.assertEqual(result['stats']['candidate_tests'], 2)
        self.assertTrue(verify_normal_pachner32(source, result['certificate']))

    def test_all_expected_rejections_complete_scan(self):
        with patch('fastunknot.normal_pachner32.pachner_32',
                   side_effect=NormalOrbitError('invalid candidate')) as constructor:
            result = reduce_pachner32_once(self.sources['figure_eight'])
        self.assertEqual(constructor.call_count, 2)
        self.assertEqual(result['status'], 'UNCHANGED')
        self.assertEqual(result['stats'], dict(initial_tetrahedra=13,
            remaining_tetrahedra=13, candidate_tests=2, moves=0, scan_complete=True))
        self.assertNotIn('certificate', result)

    def test_independent_rejection_is_never_returned_as_reduction(self):
        source = self.sources['figure_eight']
        calls = []

        def reject_first(triangulation, packet, *, check):
            calls.append(packet)
            return len(calls) > 1 and verify_normal_pachner32(triangulation, packet, check=check)

        with patch('fastunknot.normal_pachner32.verify_normal_pachner32', side_effect=reject_first):
            result = reduce_pachner32_once(source)
        self.assertEqual(result['stats']['candidate_tests'], 2)
        self.assertEqual(result['certificate'], calls[1])
        self.assertTrue(verify_normal_pachner32(source, result['certificate']))
        with patch('fastunknot.normal_pachner32.verify_normal_pachner32', return_value=False) as verifier:
            result = reduce_pachner32_once(source)
        self.assertEqual(verifier.call_count, 2)
        self.assertEqual(result['status'], 'UNCHANGED')
        self.assertTrue(result['stats']['scan_complete'])

    def test_no_eligible_edge_does_not_call_constructor(self):
        source = layered_torus(1)[0]
        with patch('fastunknot.normal_pachner32.pachner_32', side_effect=AssertionError):
            result = reduce_pachner32_once(source)
        self.assertEqual(result['status'], 'UNCHANGED')
        self.assertEqual(result['stats']['candidate_tests'], 0)
        self.assertTrue(result['stats']['scan_complete'])

    def test_multiple_vertices_and_all_region_selfattachments(self):
        source = diagram_exterior(Diagram.from_pd([]))
        self.assertEqual(_prepare(source, lambda: None)['vertices'], 6)
        result = reduce_pachner32_once(source)
        self.assertEqual(result['status'], 'REDUCED')
        self.assertTrue(verify_normal_pachner32(source, result['certificate']))
        self.assertEqual(_prepare(result['certificate']['successor'], lambda: None)['vertices'], 6)
        source, expected = selfattached_fixture()
        result = reduce_pachner32_once(source)
        self.assertEqual(result['certificate'], expected)
        self.assertEqual({r['tetrahedron'] for r in expected['certificate']['region']}, {0, 1, 2})
        self.assertTrue(verify_normal_pachner32(source, expected))

    def test_determinism_no_input_aliases_and_producer_free_replay(self):
        source, _ = selfattached_fixture()
        saved = deepcopy(source)
        result = reduce_pachner32_once(source)
        self.assertEqual(reduce_pachner32_once(deepcopy(source)), result)
        with patch('fastunknot.pachner32.pachner_32', side_effect=AssertionError), \
             patch('fastunknot.normal_pachner32.reduce_pachner32_once', side_effect=AssertionError):
            self.assertTrue(verify_normal_pachner32(source, result['certificate']))
        record = next(r for row in result['certificate']['successor']['tetrahedra']
                      for r in row if r is not None)
        record['permutation'][0] = 99
        result['certificate']['certificate']['region'][0]['vertices'][0] = 99
        self.assertEqual(source, saved)

    def test_invalid_sources_and_unexpected_failures_propagate(self):
        bad = deepcopy(self.sources['trefoil'])
        next(r for row in bad['tetrahedra'] for r in row if r is not None)['tetrahedron'] = True
        for source in (None, {}, {'tetrahedra': []}, {'tetrahedra': ()}, bad):
            with self.subTest(source_type=type(source)), self.assertRaises(NormalOrbitError):
                reduce_pachner32_once(source)
        error = ArithmeticError('unexpected implementation failure')
        with patch('fastunknot.normal_pachner32.pachner_32', side_effect=error):
            with self.assertRaises(ArithmeticError) as caught:
                reduce_pachner32_once(self.sources['figure_eight'])
        self.assertIs(caught.exception, error)

    def test_callback_identity_in_preparation_constructor_and_verifier(self):
        source, _ = selfattached_fixture()
        for phase in ('prepare', 'constructor', 'verifier'):
            for error in (NormalOrbitError('cancel'), ValueError('cancel'),
                          RuntimeError('cancel'), KeyboardInterrupt('cancel')):
                with self.subTest(phase=phase, error=type(error)):
                    active = [phase == 'prepare']

                    def callback():
                        if active[0]:
                            raise error

                    def constructor(triangulation, tetrahedron, vertices, *, check):
                        active[0] = phase == 'constructor'
                        return pachner_32(triangulation, tetrahedron, vertices, check=check)

                    def verifier(triangulation, packet, *, check):
                        active[0] = phase == 'verifier'
                        return verify_normal_pachner32(triangulation, packet, check=check)

                    with patch('fastunknot.normal_pachner32.pachner_32', side_effect=constructor), \
                         patch('fastunknot.normal_pachner32.verify_normal_pachner32', side_effect=verifier):
                        with self.assertRaises(type(error)) as caught:
                            reduce_pachner32_once(source, check=callback)
                    self.assertIs(caught.exception, error)

    def test_late_callback_cancellation_and_complete_scan_cancellation(self):
        for source in (selfattached_fixture()[0], layered_torus(1)[0]):
            calls = [0]

            def count():
                calls[0] += 1

            reduce_pachner32_once(source, check=count)
            total = calls[0]
            for stop in (total//2, total):
                calls[0] = 0
                error = NormalOrbitError('late cancellation')

                def callback():
                    count()
                    if calls[0] == stop:
                        raise error

                with self.assertRaises(NormalOrbitError) as caught:
                    reduce_pachner32_once(source, check=callback)
                self.assertIs(caught.exception, error)


if __name__ == '__main__':
    unittest.main()
