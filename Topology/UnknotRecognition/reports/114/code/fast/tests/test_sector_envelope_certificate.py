"""Source-independent completeness proofs, malformed proofs, and cancellation."""

from contextlib import ExitStack
from copy import deepcopy
from fractions import Fraction
from itertools import product
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from fastunknot.normal_sector import SearchLimit, build_sector_kernel
from fastunknot.normal_sector_verify import dense_sector_model, dense_reference_rays
from fastunknot.normal_surface_geometry import NormalOrbitError
from fastunknot.sector_envelope_certificate import certify_sector_enumeration
from fastunknot.sector_envelope_verify import (
    _cover_group, independent_sector_model, verify_sector_envelope_certificate,
)
from normal_orbit_research.fixtures import layered_torus


def attach_ball(raw):
    result = deepcopy(raw)
    tetrahedra = result['tetrahedra']
    source, face = next((i, f) for i, faces in enumerate(tetrahedra)
                        for f, gluing in enumerate(faces) if gluing is None)
    target = len(tetrahedra)
    tetrahedra.append([None] * 4)
    tetrahedra[source][face] = dict(tetrahedron=target, permutation=[0, 1, 2, 3])
    tetrahedra[target][face] = dict(tetrahedron=source, permutation=[0, 1, 2, 3])
    return result


def vector_set(surfaces):
    return {tuple(x for row in surface for x in row) for surface in surfaces}


def dot(left, right):
    return sum(a * b for a, b in zip(left, right))


class SectorEnvelopeCertificateTests(unittest.TestCase):
    def setUp(self):
        self.tri, _ = layered_torus(3)
        self.allowed = [(0, 0), (1, 2), (2, 1)]
        self.answer = certify_sector_enumeration(self.tri, self.allowed)
        self.proof = self.answer['certificate']

    def test_real_interior_breakpoint_round_trip(self):
        stats = {}
        self.assertEqual(self.answer['status'], 'COMPLETE')
        self.assertEqual(self.proof['matching_dimension'], 2)
        self.assertEqual(self.proof['section_dimension'], 1)
        self.assertEqual(len(self.proof['rays']), 3)
        self.assertTrue(verify_sector_envelope_certificate(
            self.tri, self.proof, stats=stats))
        self.assertEqual(stats['rays_checked'], 3)
        self.assertEqual(stats['dominance_tests'], 12)
        self.assertEqual(stats['envelope_pieces'], 2)
        dense = dense_reference_rays(dense_sector_model(self.tri, self.allowed),
                                    'standard')
        self.assertEqual(vector_set(self.proof['rays']),
                         vector_set(record[0] for record in dense.values()))

    def test_small_real_sectors_and_independent_graph_model(self):
        tri, _ = layered_torus(1)
        checked = 0
        dimensions = set()
        sections = set()
        for count in (1, 2, 3):
            for choices in product((-1, 0, 1, 2), repeat=count):
                allowed = [(i, typ) for i, typ in enumerate(choices) if typ >= 0]
                sparse = build_sector_kernel(tri, allowed)
                independent = independent_sector_model(tri, allowed)
                dense = dense_sector_model(tri, allowed)
                self.assertEqual(len(independent['basis']), len(dense['basis']))
                self.assertEqual(len(independent['basis']), len(sparse.basis))
                for vector in independent['basis']:
                    self.assertTrue(all(dot(row, vector) == 0
                                        for row in dense['constraints']))
                for vector in dense['basis']:
                    self.assertTrue(all(dot(row, vector) == 0
                                        for row in independent['constraints']))
                # Corner potentials may differ by a vertex-wide linear gauge.
                for vector in independent['basis']:
                    for group in independent['groups'].values():
                        first = group[0]
                        for corner in group:
                            delta = [a - b for a, b in zip(
                                independent['potentials'][corner],
                                independent['potentials'][first])]
                            reference = [a - b for a, b in zip(
                                dense['potentials'][corner],
                                dense['potentials'][first])]
                            self.assertEqual(dot(delta, vector), dot(reference, vector))
                if len(sparse.basis) > 2:
                    continue
                result = certify_sector_enumeration(tri, allowed)
                with self.subTest(count=count, allowed=allowed):
                    self.assertTrue(verify_sector_envelope_certificate(
                        tri, result['certificate']))
                    expected = dense_reference_rays(dense, 'standard')
                    self.assertEqual(vector_set(result['coordinates']),
                                     vector_set(row[0] for row in expected.values()))
                checked += 1
                dimensions.add(result['certificate']['matching_dimension'])
                sections.add(result['certificate']['section_dimension'])
            tri = attach_ball(tri)
        self.assertGreaterEqual(checked, 50)
        self.assertEqual(dimensions, {0, 1, 2})
        self.assertEqual(sections, {-1, 0, 1})

    def test_empty_and_point_proofs_reject_false_claims(self):
        tri, _ = layered_torus(1)
        empty = certify_sector_enumeration(tri, [])['certificate']
        self.assertTrue(verify_sector_envelope_certificate(tri, empty))
        self.assertEqual(empty['section_dimension'], -1)
        point = certify_sector_enumeration(tri, [(0, 2)])['certificate']
        self.assertEqual(point['section_dimension'], 0)
        self.assertTrue(verify_sector_envelope_certificate(tri, point))
        fake_empty = deepcopy(point)
        fake_empty.update(section_dimension=-1, rays=[], envelopes=[],
                          q_origin=None, q_direction=None, lower=None, upper=None)
        self.assertFalse(verify_sector_envelope_certificate(tri, fake_empty))
        wrong = deepcopy(empty)
        wrong['rays'] = deepcopy(point['rays'])
        self.assertFalse(verify_sector_envelope_certificate(tri, wrong))
        wrong = deepcopy(point)
        wrong['envelopes'] = [dict(vertex=0, corners=[0], brackets=[0])]
        self.assertFalse(verify_sector_envelope_certificate(tri, wrong))

    def test_missing_extra_reordered_and_corrupted_rays(self):
        changes = []
        for i in range(len(self.proof['rays'])):
            bad = deepcopy(self.proof)
            del bad['rays'][i]
            changes.append(bad)
        bad = deepcopy(self.proof)
        bad['rays'].append(deepcopy(bad['rays'][0]))
        changes.append(bad)
        bad = deepcopy(self.proof)
        bad['rays'].reverse()
        changes.append(bad)
        bad = deepcopy(self.proof)
        bad['rays'][0][0][0] += 1
        changes.append(bad)
        bad = deepcopy(self.proof)
        bad['rays'][0][0][0] = False
        changes.append(bad)
        for bad in changes:
            with self.subTest(rays=bad['rays']):
                self.assertFalse(verify_sector_envelope_certificate(self.tri, bad))

    def test_false_source_dimension_and_interval(self):
        mutations = [
            ('schema', 'normal-sector-envelope-v999'),
            ('source_sha256', '0' * 64),
            ('matching_dimension', 1), ('matching_dimension', True),
            ('section_dimension', 0), ('section_dimension', True),
            ('lower', [1, 4]), ('upper', [1, 3]),
            ('q_direction', [[0, 1]] * 3),
            ('q_origin', [[0, 1]] * 3),
            ('allowed_types', [[0, 0], [0, 1], [2, 1]]),
            ('allowed_types', [[0, True], [1, 2], [2, 1]]),
            ('allowed_types', [[2, 1], [1, 2], [0, 0]]),
        ]
        for key, value in mutations:
            bad = deepcopy(self.proof)
            bad[key] = value
            with self.subTest(key=key, value=value):
                self.assertFalse(verify_sector_envelope_certificate(self.tri, bad))

    def test_bad_envelope_coverage_corner_and_bracket(self):
        mutations = []
        bad = deepcopy(self.proof)
        bad['envelopes'].clear()
        mutations.append(bad)
        bad = deepcopy(self.proof)
        bad['envelopes'].append(deepcopy(bad['envelopes'][0]))
        mutations.append(bad)
        for key, value in [('vertex', -1), ('vertex', True),
                           ('corners', []), ('corners', [0, 0]),
                           ('corners', [0, 12]), ('corners', [True, 2]),
                           ('corners', [2, 0]), ('corners', [0]),
                           ('brackets', []), ('brackets', [100] * 12),
                           ('brackets', [False] * 12)]:
            bad = deepcopy(self.proof)
            bad['envelopes'][0][key] = value
            mutations.append(bad)
        # A valid-index but false slope bracket: line 0 has the first slope.
        bad = deepcopy(self.proof)
        bad['envelopes'][0]['brackets'][0] = 2
        mutations.append(bad)
        for index, bad in enumerate(mutations):
            with self.subTest(mutation=index):
                self.assertFalse(verify_sector_envelope_certificate(self.tri, bad))

    def test_rationals_are_canonical_and_exact_hex_transport_is_accepted(self):
        for value in ([2, 2], [1, 0], [-1, -1], [1.0, 1], [True, 1],
                      ['1', 1], [1], {'numerator': 1, 'denominator': 1}):
            bad = deepcopy(self.proof)
            bad['q_origin'][0] = value
            with self.subTest(value=value):
                self.assertFalse(verify_sector_envelope_certificate(self.tri, bad))
        good = deepcopy(self.proof)
        for key in ('q_origin', 'q_direction'):
            good[key] = [[hex(a), hex(b)] for a, b in good[key]]
        for key in ('lower', 'upper'):
            good[key] = [hex(x) for x in good[key]]
        good['rays'] = [[[hex(x) for x in row] for row in surface]
                        for surface in good['rays']]
        self.assertTrue(verify_sector_envelope_certificate(self.tri, good))

    def test_producer_disabled_replay(self):
        blocked = [
            'fastunknot.normal_sector.build_sector_kernel',
            'fastunknot.normal_sector.sector_rays',
            'fastunknot.normal_sector._nullspace',
            'fastunknot.normal_sector._hyperplanes',
            'fastunknot.normal_sector.SectorKernel.is_standard_ray',
            'fastunknot.normal_sector.SectorKernel.lift',
            'fastunknot.sector_envelope._lower_envelope',
            'fastunknot.sector_envelope.sector_envelope_plan',
            'fastunknot.sector_envelope.sector_envelope_rays',
            'fastunknot.sector_envelope_certificate.certify_sector_enumeration',
            'fastunknot.normal_sector_verify.dense_sector_model',
            'fastunknot.normal_sector_verify.dense_reference_rays',
        ]
        with ExitStack() as stack:
            for target in blocked:
                stack.enter_context(patch(target, side_effect=AssertionError(target)))
            self.assertTrue(verify_sector_envelope_certificate(self.tri, self.proof))

    def test_complete_ray_cap_and_invalid_caps(self):
        for cap in (0, 1, 2):
            result = certify_sector_enumeration(self.tri, self.allowed, max_rays=cap)
            self.assertEqual(result['status'], 'INCONCLUSIVE')
            self.assertNotIn('certificate', result)
        self.assertEqual(certify_sector_enumeration(
            self.tri, self.allowed, max_rays=3)['status'], 'COMPLETE')
        tri, _ = layered_torus(1)
        self.assertEqual(certify_sector_enumeration(tri, [], max_rays=0)['status'],
                         'COMPLETE')
        for cap in (-1, True, 1.0):
            with self.assertRaises(ValueError):
                certify_sector_enumeration(self.tri, self.allowed, max_rays=cap)

    def test_false_valued_callback_exceptions_preserve_identity(self):
        class Cancel:
            def __init__(self, exception, after):
                self.exception = exception
                self.after = after
                self.calls = 0

            def __bool__(self):
                return False

            def __call__(self):
                self.calls += 1
                if self.calls == self.after:
                    raise self.exception

        for kind in (ValueError, RuntimeError, NormalOrbitError, SearchLimit):
            for after in (2, 7):
                exception = kind('stop complete envelope replay')
                with self.subTest(kind=kind, after=after):
                    with self.assertRaises(kind) as raised:
                        verify_sector_envelope_certificate(
                            self.tri, self.proof, check=Cancel(exception, after))
                    self.assertIs(raised.exception, exception)
        exception = SearchLimit('user cancellation inside ray production')
        from fastunknot import sector_envelope_certificate as maker
        actual = maker.sector_envelope_rays
        state = {'inside': False}

        def wrapped(*args, **kwargs):
            state['inside'] = True
            yield from actual(*args, **kwargs)

        class RayCancel:
            def __bool__(self):
                return False

            def __call__(self):
                if state['inside']:
                    raise exception

        with patch.object(maker, 'sector_envelope_rays', wrapped):
            with self.assertRaises(SearchLimit) as raised:
                certify_sector_enumeration(self.tri, self.allowed, check=RayCancel())
        self.assertIs(raised.exception, exception)

    def test_slope_bracket_certificate_rejects_hidden_undercut(self):
        # Proposed E=min(s,-s) with switch 0; the hidden constant -1
        # undercuts it at the switch despite being harmless at endpoints.
        lines = [(Fraction(0), Fraction(1)),
                 (Fraction(0), Fraction(-1)),
                 (Fraction(-1), Fraction(0))]
        stats = dict(dominance_tests=0)
        self.assertIsNone(_cover_group(lines, [0, 1, 2], [0, 1],
                          Fraction(-2), Fraction(2), [0, 1, 1],
                          lambda: None, stats))
        # Raising the hidden line to +1 makes the same bracket proof valid.
        lines[2] = (Fraction(1), Fraction(0))
        stats = dict(dominance_tests=0)
        self.assertEqual(_cover_group(lines, [0, 1, 2], [0, 1],
                         Fraction(-2), Fraction(2), [0, 1, 1],
                         lambda: None, stats), [Fraction(0)])
        self.assertEqual(stats['dominance_tests'], 3)


if __name__ == '__main__':
    unittest.main()
