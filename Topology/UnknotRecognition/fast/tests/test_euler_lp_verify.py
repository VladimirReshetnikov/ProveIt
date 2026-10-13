"""Independent Euler-certificate coverage, hostile packets and cancellation."""

from contextlib import ExitStack
from copy import deepcopy
from fractions import Fraction
from hashlib import sha256
from itertools import product
import json
import unittest
from unittest.mock import patch

from fastunknot.normal_euler_verify import verify_sector_euler_certificate
from fastunknot.normal_surface_geometry import NormalOrbitError
from normal_orbit_research.fixtures import layered_torus, boundary_cap, interior_vertex_torus


def base(source, support, status):
    digest = sha256(json.dumps(source, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    return dict(schema='normal-sector-euler-lp-v1', status=status,
                source_sha256=digest, allowed_types=[list(item) for item in support])


def positive():
    source, rows = layered_torus(3)
    proof = base(source, [(t, 2) for t in range(3)], 'POSITIVE_EULER')
    proof.update(quadrilaterals=[2, 1, 1], coordinates=rows, euler_characteristic=1)
    return source, proof


def negative(kind='anchors'):
    source, _ = layered_torus(3)
    proof = base(source, [(t, 0) for t in range(3)], 'NO_POSITIVE_EULER')
    proof['proof_kind'] = kind
    if kind == 'envelope':
        proof['multipliers'] = [[1, 1], [4, 1], [0, 1]]
    else:
        # Fixed certificates, not derived using either maintained constructor.
        proof['duals'] = [dict(anchors=[anchor], multipliers=[list(p) for p in dual])
                         for anchor, dual in zip((0, 1, 2, 3, 6, 7, 10),
                             (((0, 1), (2, 1), (0, 1)),
                              *(((0, 1), (4, 1), (0, 1)),)*5,
                              ((1, 1), (3, 1), (0, 1))))]
    return source, proof


def reduction(positive_result=False):
    if positive_result:
        source, _ = interior_vertex_torus()
        support = [(0, 0), (1, 2), (2, 2), (3, 0)]
        inner = base(source, [(1, 2), (2, 2)], 'POSITIVE_EULER')
        inner.update(quadrilaterals=[1, 1], euler_characteristic=1,
                     coordinates=[[2, 1, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 1],
                                  [1, 0, 0, 0, 0, 0, 1], [0, 1, 0, 1, 0, 0, 0]])
        steps = [dict(row_combination=[[0, 1, 1], [7, -1, 1], [9, -1, 1]],
                      forced_indices=[0]),
                 dict(row_combination=[[1, -1, 1], [4, 1, 1], [16, 1, 1]],
                      forced_indices=[3])]
    else:
        source, _ = layered_torus(2)
        support = [(0, 0), (1, 0)]
        inner = base(source, [(0, 0)], 'NO_POSITIVE_EULER')
        inner.update(proof_kind='anchors', duals=[dict(anchors=[a], multipliers=[])
                                                for a in (0, 1, 2)])
        steps = [dict(row_combination=[[1, -1, 4], [2, 1, 4], [4, 1, 4],
                                       [5, -1, 4], [6, 1, 4], [8, -1, 4]],
                      forced_indices=[1])]
    proof = base(source, support, inner['status'])
    proof.update(schema='normal-sector-euler-reduction-v1', euler_certificate=inner,
                 matching_support_certificate=dict(schema='normal-sector-matching-support-v1',
                     source_sha256=proof['source_sha256'], allowed_types=deepcopy(proof['allowed_types']),
                     steps=steps))
    return source, proof


class EulerCertificateReplayTests(unittest.TestCase):
    def test_frozen_positive_anchor_and_envelope_certificates(self):
        for source, proof in (positive(), negative(), negative('envelope')):
            original = deepcopy((source, proof))
            self.assertTrue(verify_sector_euler_certificate(source, proof))
            self.assertEqual((source, proof), original)
        source, proof = negative()
        del proof['proof_kind']  # v1's original implicit anchor spelling.
        self.assertTrue(verify_sector_euler_certificate(source, proof))

    def test_empty_support_requires_the_single_empty_anchor(self):
        source, _ = layered_torus(1)
        proof = base(source, [], 'NO_POSITIVE_EULER')
        proof['duals'] = [dict(anchors=[], multipliers=[])]
        self.assertTrue(verify_sector_euler_certificate(source, proof))
        proof['duals'] = []
        self.assertFalse(verify_sector_euler_certificate(source, proof))
        del proof['duals']
        proof.update(proof_kind='envelope', multipliers=[])
        self.assertTrue(verify_sector_euler_certificate(source, proof))

    def test_full_cartesian_anchor_cover_for_boundary_and_interior_vertices(self):
        source, _ = interior_vertex_torus()
        proof = base(source, [(1, 0), (2, 2), (3, 1)], 'NO_POSITIVE_EULER')
        proof.update(proof_kind='anchors', duals=[
            dict(anchors=list(anchors), multipliers=[[0, 1], [0, 1], [0, 1]])
            for anchors in product((0, 1, 2, 7, 13), (3, 6))])
        self.assertTrue(verify_sector_euler_certificate(source, proof))
        for index in range(len(proof['duals'])):
            bad = deepcopy(proof)
            bad['duals'].pop(index)
            self.assertFalse(verify_sector_euler_certificate(source, bad))
        bad = deepcopy(proof)
        bad['duals'][3] = deepcopy(bad['duals'][2])
        self.assertFalse(verify_sector_euler_certificate(source, bad))
        bad = deepcopy(proof)
        bad['duals'].reverse()
        self.assertFalse(verify_sector_euler_certificate(source, bad))

    def test_positive_certificate_proves_canonical_vector_without_extremality(self):
        source, rows = layered_torus(2)
        source, _ = boundary_cap(source, rows)
        # Sum of two compatible Q rays. It has primitive Q coordinates and
        # positive canonical Euler but is not a standard extreme ray.
        rows = [[1, 1, 2, 2, 1, 0, 0], [2, 2, 2, 2, 0, 0, 0],
                [1, 0, 3, 0, 0, 1, 0]]
        proof = base(source, [(0, 0), (2, 1)], 'POSITIVE_EULER')
        proof.update(quadrilaterals=[1, 1], coordinates=rows, euler_characteristic=1)
        self.assertTrue(verify_sector_euler_certificate(source, proof))
        from fastunknot.normal_crushing import crush_normal_ray
        with self.assertRaisesRegex(ValueError, 'extreme'):
            crush_normal_ray(source, rows)

    def test_positive_matching_canonical_primitive_and_support_constraints(self):
        source, original = positive()
        mutants = []
        for field, value in (('quadrilaterals', [0, 0, 0]),
                             ('quadrilaterals', [2, 1]),
                             ('quadrilaterals', [2, -1, 1]),
                             ('coordinates', None), ('coordinates', []),
                             ('euler_characteristic', 2),
                             ('allowed_types', [[0, 2], [1, 2]])):
            bad = deepcopy(original); bad[field] = value; mutants.append(bad)
        bad = deepcopy(original)
        bad['quadrilaterals'] = [2*x for x in bad['quadrilaterals']]
        bad['coordinates'] = [[2*x for x in row] for row in bad['coordinates']]
        bad['euler_characteristic'] = 2
        mutants.append(bad)
        bad = deepcopy(original)
        # A vertex-link summand preserves matching and positive Euler but
        # destroys the canonical zero minimum at the single global vertex.
        for row in bad['coordinates']:
            row[:4] = [x+1 for x in row[:4]]
        bad['euler_characteristic'] += 1
        mutants.append(bad)
        bad = deepcopy(original); bad['coordinates'][0][0] += 1; mutants.append(bad)
        bad = deepcopy(original); bad['coordinates'][0][4] = 1; mutants.append(bad)
        for bad in mutants:
            self.assertFalse(verify_sector_euler_certificate(source, bad), bad)

    def test_forged_duals_missing_anchors_and_wrong_proof_kind(self):
        for kind in ('anchors', 'envelope'):
            source, original = negative(kind)
            bad = deepcopy(original)
            if kind == 'anchors':
                for record in bad['duals']:
                    record['multipliers'] = [[0, 1]]*3
            else:
                bad['multipliers'] = [[0, 1]]*3
            self.assertFalse(verify_sector_euler_certificate(source, bad))
            for value in ('invalid', None, True, [], 0):
                bad = deepcopy(original); bad['proof_kind'] = value
                self.assertFalse(verify_sector_euler_certificate(source, bad))
        source, original = negative()
        for index in range(len(original['duals'])):
            bad = deepcopy(original); bad['duals'].pop(index)
            self.assertFalse(verify_sector_euler_certificate(source, bad))
        for field, value in (('anchors', [False]), ('anchors', ['0x0']),
                             ('anchors', []), ('multipliers', []),
                             ('extra', True)):
            bad = deepcopy(original); bad['duals'][0][field] = value
            self.assertFalse(verify_sector_euler_certificate(source, bad))
        bad = deepcopy(original); bad['duals'].append(deepcopy(bad['duals'][0]))
        self.assertFalse(verify_sector_euler_certificate(source, bad))

    def test_exact_numeric_transport_and_boolean_float_rejection(self):
        source, proof = positive()
        for key in ('quadrilaterals',):
            proof[key] = [hex(x) for x in proof[key]]
        proof['coordinates'] = [[hex(x) for x in row] for row in proof['coordinates']]
        proof['euler_characteristic'] = '+0x1'
        self.assertTrue(verify_sector_euler_certificate(source, proof))
        for value in (True, False, 1.0, Fraction(1), '1', '0xg', None, [1]):
            source, original = positive()
            for field in ('euler_characteristic', 'quadrilaterals', 'coordinates'):
                bad = deepcopy(original)
                if field == 'euler_characteristic': bad[field] = value
                elif field == 'quadrilaterals': bad[field][-1] = value
                else: bad[field][0][0] = value
                self.assertFalse(verify_sector_euler_certificate(source, bad))
        for kind in ('anchors', 'envelope'):
            source, original = negative(kind)
            for value in ((1, 1), [1], [1, 0], [1, -1], [True, 1],
                          [1, True], [1.0, 1], ['1', 1], None):
                bad = deepcopy(original)
                target = bad['duals'][0] if kind == 'anchors' else bad
                target['multipliers'][0] = value
                self.assertFalse(verify_sector_euler_certificate(source, bad))
            converted = deepcopy(original)
            targets = converted['duals'] if kind == 'anchors' else [converted]
            for target in targets:
                target['multipliers'] = [[hex(2*a), hex(2*b)]
                                          for a, b in target['multipliers']]
            self.assertTrue(verify_sector_euler_certificate(source, converted))

    def test_strict_packet_support_and_source_binding(self):
        foreign, _ = layered_torus(2)
        for source, original in (positive(), negative(), negative('envelope')):
            self.assertFalse(verify_sector_euler_certificate(foreign, original))
            for value in (None, [], 1, True, 'certificate'):
                self.assertFalse(verify_sector_euler_certificate(source, value))
                self.assertFalse(verify_sector_euler_certificate(value, original))
            for field, value in (('schema', None), ('status', 'UNKNOT'),
                                 ('source_sha256', 'f'*64), ('source_sha256', False),
                                 ('extra', 0), ('allowed_types', None),
                                 ('allowed_types', [[True, 0]]),
                                 ('allowed_types', [[0, False]]),
                                 ('allowed_types', [[0, 0], [0, 1]]),
                                 ('allowed_types', [[1, 0], [0, 0]]),
                                 ('allowed_types', [[0, 3]]),
                                 ('allowed_types', [[-1, 0]]),
                                 ('allowed_types', [(0, 0)])):
                bad = deepcopy(original); bad[field] = value
                self.assertFalse(verify_sector_euler_certificate(source, bad))
            for key in original:
                bad = deepcopy(original); del bad[key]
                if key != 'proof_kind':
                    self.assertFalse(verify_sector_euler_certificate(source, bad))
            bad_source = deepcopy(source)
            bad_source['tetrahedra'][0][0]['tetrahedron'] = False
            self.assertFalse(verify_sector_euler_certificate(bad_source, original))

    def test_replay_with_constructors_models_enumerators_and_lp_disabled(self):
        with ExitStack() as stack:
            for name in ('normal_euler.decide_sector_euler', 'normal_euler._euler_model',
                         'normal_euler.build_sector_kernel',
                         'normal_euler.solve_nonnegative_kernel',
                         'normal_sector.build_sector_kernel', 'normal_sector.sector_rays',
                         'sector_matching_support.matching_support',
                         'exact_lp.solve_nonnegative_kernel'):
                stack.enter_context(patch('fastunknot.'+name,
                                         side_effect=AssertionError('producer used')))
            for source, proof in (positive(), negative(), negative('envelope'),
                                  reduction(), reduction(True)):
                self.assertTrue(verify_sector_euler_certificate(source, proof))

    def test_matching_reduction_wrapper_replays_original_full_sector(self):
        for source, proof in (reduction(), reduction(True)):
            original = deepcopy((source, proof))
            self.assertTrue(verify_sector_euler_certificate(source, proof))
            self.assertEqual((source, proof), original)
            # A wrapper's inner certificate remains independently valid on
            # its smaller sector, but cannot silently change that sector.
            self.assertTrue(verify_sector_euler_certificate(source, proof['euler_certificate']))
        source, proof = reduction()
        proof['euler_certificate'].pop('duals')
        proof['euler_certificate'].update(proof_kind='envelope', multipliers=[])
        self.assertTrue(verify_sector_euler_certificate(source, proof))

    def test_reduction_source_schema_status_and_retained_type_tampering(self):
        for source, original in (reduction(), reduction(True)):
            for field in original:
                bad = deepcopy(original); del bad[field]
                self.assertFalse(verify_sector_euler_certificate(source, bad))
            for field, value in (('status', 'UNKNOT'), ('source_sha256', '0'*64),
                                 ('allowed_types', []), ('allowed_types', [[0, True]]),
                                 ('matching_support_certificate', None),
                                 ('euler_certificate', None), ('extra', 0)):
                bad = deepcopy(original); bad[field] = value
                self.assertFalse(verify_sector_euler_certificate(source, bad))
            for field, value in (('allowed_types', []), ('source_sha256', '0'*64),
                                 ('allowed_types', [[0, 1]]),
                                 ('schema', 'normal-sector-euler-reduction-v1')):
                bad = deepcopy(original); bad['euler_certificate'][field] = value
                self.assertFalse(verify_sector_euler_certificate(source, bad))
            bad = deepcopy(original)
            bad['status'] = ('POSITIVE_EULER' if bad['status'] == 'NO_POSITIVE_EULER'
                             else 'NO_POSITIVE_EULER')
            self.assertFalse(verify_sector_euler_certificate(source, bad))
            bad = deepcopy(original); bad['euler_certificate'] = deepcopy(original)
            self.assertFalse(verify_sector_euler_certificate(source, bad))
            foreign, _ = layered_torus(1)
            self.assertFalse(verify_sector_euler_certificate(foreign, original))

    def test_reduction_forced_zero_implications_must_replay_exactly(self):
        source, original = reduction()
        for field, value in (('schema', 'wrong'), ('source_sha256', '0'*64),
                             ('allowed_types', [[0, 1], [1, 0]]), ('steps', []),
                             ('steps', None), ('extra', 0)):
            bad = deepcopy(original); bad['matching_support_certificate'][field] = value
            self.assertFalse(verify_sector_euler_certificate(source, bad))
        for field, value in (('forced_indices', []), ('forced_indices', [0]),
                             ('forced_indices', [True]), ('forced_indices', [1, 1]),
                             ('row_combination', []), ('row_combination', [[1, 1, 1]]),
                             ('row_combination', [[True, -1, 4]]), ('extra', 0)):
            bad = deepcopy(original)
            bad['matching_support_certificate']['steps'][0][field] = value
            self.assertFalse(verify_sector_euler_certificate(source, bad))
        for position, value in ((0, -1), (0, 999), (1, 0), (1, True), (1, 1.0),
                                (2, 0), (2, -1), (2, True)):
            bad = deepcopy(original)
            bad['matching_support_certificate']['steps'][0]['row_combination'][0][position] = value
            self.assertFalse(verify_sector_euler_certificate(source, bad))
        bad = deepcopy(original)
        bad['matching_support_certificate']['steps'][0]['row_combination'].reverse()
        self.assertFalse(verify_sector_euler_certificate(source, bad))
        bad = deepcopy(original)
        bad['matching_support_certificate']['steps'].append(
            deepcopy(bad['matching_support_certificate']['steps'][0]))
        self.assertFalse(verify_sector_euler_certificate(source, bad))

    def test_caller_exceptions_survive_every_callback_location(self):
        class Stop(BaseException):
            pass
        class Cancel:
            def __init__(self, limit, error):
                self.calls, self.limit, self.error = 0, limit, error
            def __bool__(self):
                return False
            def __call__(self):
                self.calls += 1
                if self.calls == self.limit:
                    raise self.error
        for source, proof in (positive(), negative(), negative('envelope'),
                              reduction(), reduction(True)):
            count = Cancel(None, None)
            self.assertTrue(verify_sector_euler_certificate(source, proof, check=count))
            for stop in range(1, count.calls+1):
                # NormalOrbitError and ValueError previously disappeared in
                # nested malformed-input handling. Sweep every callback site.
                for error in (NormalOrbitError('cancel'), ValueError('cancel'), Stop('cancel')):
                    with self.assertRaises(type(error)) as caught:
                        verify_sector_euler_certificate(source, proof, check=Cancel(stop, error))
                    self.assertIs(caught.exception, error)
            for error in (TypeError('cancel'), KeyError('cancel'), IndexError('cancel'),
                          AttributeError('cancel'), OverflowError('cancel'),
                          ArithmeticError('cancel'), KeyboardInterrupt('cancel')):
                with self.assertRaises(type(error)) as caught:
                    verify_sector_euler_certificate(source, proof,
                                                    check=Cancel(count.calls//2, error))
                self.assertIs(caught.exception, error)


if __name__ == '__main__':
    unittest.main()
