"""Authentication and certificate parity for invocation-local source reuse."""

from contextlib import ExitStack
from copy import deepcopy
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from fastunknot.normal_parallelity import normal_cut_parallelity
from fastunknot.normal_parallelity_verify import verify_normal_cut_parallelity
from fastunknot.parallelity_boundary_words import normal_parallelity_boundary_words
from fastunknot.parallelity_boundary_words_verify import verify_parallelity_boundary_words
from fastunknot.normal_surface_geometry import NormalOrbitError
from normal_orbit_research.fixtures import layered_torus
import fastunknot.normal_parallelity_geometry as producer_geometry
import fastunknot.normal_parallelity_reference as reference_geometry


class ComposedSourceReuseTests(unittest.TestCase):
    def setUp(self):
        self.raw, self.rows = layered_torus(4)
        self.result = normal_cut_handlebodies(
            self.raw, self.rows, record_certificate=True)
        self.assertEqual(self.result['status'], 'COMPLETE')
        self.proof = self.result['certificate']

    def verify(self, raw=None, rows=None, proof=None, **kwargs):
        return verify_normal_cut_handlebodies(
            self.raw if raw is None else raw,
            self.rows if rows is None else rows,
            self.proof if proof is None else proof, **kwargs)

    def test_composed_producer_uses_its_own_geometry_once(self):
        with patch('fastunknot.normal_parallelity._parallelity_geometry',
                   wraps=producer_geometry._parallelity_geometry) as calls:
            with patch('fastunknot.parallelity_boundary_words._parallelity_geometry',
                       side_effect=AssertionError('duplicate source construction')):
                actual = normal_cut_handlebodies(
                    self.raw, self.rows, record_certificate=True)
        self.assertEqual(calls.call_count, 1)
        self.assertEqual(actual, self.result)

    def test_composed_checker_uses_independent_reference_once(self):
        with ExitStack() as stack:
            calls = stack.enter_context(patch(
                'fastunknot.normal_parallelity_verify._reference_parallelity',
                wraps=reference_geometry._reference_parallelity))
            forbidden = (
                'fastunknot.parallelity_boundary_words_verify._reference_parallelity',
                'fastunknot.normal_parallelity._parallelity_geometry',
                'fastunknot.parallelity_boundary_words._boundary_words_from_geometry',
                'fastunknot.normal_cut_handlebodies.normal_cut_handlebodies',
            )
            for name in forbidden:
                stack.enter_context(patch(name, side_effect=AssertionError(name)))
            self.assertTrue(self.verify())
        self.assertEqual(calls.call_count, 1)

    def test_standalone_public_apis_keep_source_authentication(self):
        base = normal_cut_parallelity(self.raw, self.rows, record_certificate=True)
        boundary = normal_parallelity_boundary_words(
            self.raw, self.rows, record_certificate=True)
        self.assertEqual(base['certificate'], self.proof['parallelity'])
        self.assertEqual(boundary['certificate'], self.proof['boundary'])
        self.assertTrue(verify_normal_cut_parallelity(
            self.raw, self.rows, base['certificate']))
        self.assertTrue(verify_parallelity_boundary_words(
            self.raw, self.rows, boundary['certificate']))
        for func, proof in ((verify_normal_cut_parallelity, base['certificate']),
                            (verify_parallelity_boundary_words, boundary['certificate']),
                            (verify_normal_cut_handlebodies, self.proof)):
            for name in ('prepared', 'geometry', 'source', 'cache'):
                with self.assertRaises(TypeError):
                    func(self.raw, self.rows, proof, **{name: {}})

    def test_no_cross_call_state_or_input_alias_cache(self):
        self.assertTrue(self.verify())
        rows = deepcopy(self.rows)
        for row in rows:
            row[:] = [2 * value for value in row]
        self.assertFalse(self.verify(rows=rows))
        new = normal_cut_handlebodies(self.raw, rows, record_certificate=True)
        self.assertTrue(self.verify(rows=rows, proof=new['certificate']))
        self.assertFalse(self.verify(proof=new['certificate']))
        self.assertTrue(self.verify())
        broken = deepcopy(self.raw)
        next(face for tet in broken['tetrahedra'] for face in tet
             if face is not None)['tetrahedron'] = len(broken['tetrahedra'])
        with self.assertRaises(NormalOrbitError):
            self.verify(raw=broken)
        self.assertTrue(self.verify())

    def test_equal_hash_strings_do_not_authenticate_wrong_inputs(self):
        changed = deepcopy(self.proof)
        changed['parallelity']['input_sha256'] = '0' * 64
        changed['boundary']['input_sha256'] = '0' * 64
        self.assertFalse(self.verify(proof=changed))
        changed['parallelity']['input_sha256'] = self.proof['parallelity']['input_sha256']
        self.assertFalse(self.verify(proof=changed))

    def test_source_and_nested_chart_mutations_are_rejected(self):
        altered = deepcopy(self.proof)
        altered['parallelity']['geometry']['core']['handles1'][0]['ends'][0] += 1
        self.assertFalse(self.verify(proof=altered))
        altered = deepcopy(self.proof)
        altered['parallelity']['summary']['core_euler_characteristic'] += 1
        self.assertFalse(self.verify(proof=altered))
        altered = deepcopy(self.proof)
        altered['boundary']['skeleton']['ports'][0]['core_handle'] += 1
        self.assertFalse(self.verify(proof=altered))
        rows = deepcopy(self.rows)
        rows[0][0] = True
        with self.assertRaises(NormalOrbitError):
            self.verify(rows=rows)
        self.assertTrue(self.verify())

    def test_shared_budget_still_covers_all_six_traces(self):
        p, b = self.proof['parallelity'], self.proof['boundary']
        count = 0
        for name in ('vertex_selector', 'boundary_selector', 'polygon_weights', 'fibre_cover'):
            trace = p[name]
            if name.endswith('selector'):
                trace = trace['weighted_certificate']
            count += len(trace['orbit_proof']['operations'])
        count += sum(len(b[name]['orbit_proof']['operations'])
                     for name in ('vertex_partition', 'gap_cover') if b[name] is not None)
        self.assertGreater(count, 0)
        with patch('fastunknot.normal_parallelity_verify._reference_parallelity',
                   side_effect=AssertionError('budget should refuse first')):
            self.assertFalse(self.verify(max_operations=count - 1))
        self.assertTrue(self.verify(max_operations=count))
        self.assertEqual(normal_cut_handlebodies(
            self.raw, self.rows, max_cycles=0)['status'], 'INCONCLUSIVE')

    def test_cancelled_replay_cannot_create_later_trust(self):
        class Cancel(Exception):
            pass
        def stop():
            raise Cancel('cancelled')
        with self.assertRaises(Cancel):
            self.verify(check=stop)
        self.assertTrue(self.verify())

    def test_huge_hexadecimal_source_and_certificate(self):
        raw, base = layered_torus(1)
        n = 1 << 16384
        rows = [[n * x for x in row] for row in base]
        result = normal_cut_handlebodies(raw, rows, record_certificate=True)
        proof = json.loads(json.dumps(json_safe(result['certificate'])))
        self.assertTrue(self.verify(raw=raw, rows=json_safe(rows), proof=proof))
        self.assertEqual(result['census']['ball_components'], n)


if __name__ == '__main__':
    unittest.main()
