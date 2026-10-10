"""Source-bound planar coverage, negative disc replay, and limit contracts."""

from copy import deepcopy
from itertools import product
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from fastunknot.sector_planar_certificate import (
    certify_planar_sector, discover_planar_in_sector,
)
from fastunknot.sector_planar_verify import (
    PlanarVerificationLimit, verify_planar_sector_certificate, verify_planar_exhaustion,
)
from fastunknot.normal_sector_verify import verify_sector_witness
from test_normal_sector_integration import solid_torus, capped_solid_torus


def double_cap():
    raw = capped_solid_torus()
    raw['tetrahedra'][0][3] = {'tetrahedron': 2, 'permutation': [0, 1, 2, 3]}
    raw['tetrahedra'].append([None, None, None,
        {'tetrahedron': 0, 'permutation': [0, 1, 2, 3]}])
    return raw


class PlanarCertificateTests(unittest.TestCase):
    def test_all_small_full_sectors_have_independent_replay(self):
        raw = double_cap()
        for types in product(range(3), repeat=3):
            support = list(enumerate(types))
            with self.subTest(types=types):
                answer = certify_planar_sector(raw, support)
                self.assertEqual(answer['status'], 'COMPLETE')
                self.assertTrue(verify_planar_sector_certificate(raw, answer['certificate']))

    def test_verification_does_not_call_the_producer(self):
        raw = double_cap()
        proof = certify_planar_sector(raw, [(0, 2), (1, 1), (2, 1)])['certificate']
        with patch('fastunknot.sector_planar._plan', side_effect=AssertionError('producer')):
            with patch('fastunknot.normal_sector.build_sector_kernel',
                       side_effect=AssertionError('producer')):
                self.assertTrue(verify_planar_sector_certificate(raw, proof))

    def test_missing_extra_scaled_or_malformed_ray_is_rejected(self):
        raw = double_cap()
        proof = certify_planar_sector(raw, [(0, 2), (1, 1), (2, 1)])['certificate']
        changes = []
        bad = deepcopy(proof); bad['quadrilateral_rays'].pop(); changes.append(bad)
        bad = deepcopy(proof); bad['quadrilateral_rays'].append([1, 17, 23]); changes.append(bad)
        bad = deepcopy(proof); bad['quadrilateral_rays'][0] = [2*x for x in bad['quadrilateral_rays'][0]]; changes.append(bad)
        bad = deepcopy(proof); bad['quadrilateral_rays'][0][0] = True; changes.append(bad)
        bad = deepcopy(proof); bad['allowed_types'][0][0] = False; changes.append(bad)
        bad = deepcopy(proof); bad['source_sha256'] = '0'*64; changes.append(bad)
        for changed in changes:
            self.assertFalse(verify_planar_sector_certificate(raw, changed))

    def test_whole_query_limits_include_kernel_construction(self):
        raw = double_cap()
        for api in (certify_planar_sector, discover_planar_in_sector):
            calls = []
            answer = api(raw, [(0, 2)], max_work=0, check=lambda: calls.append(1))
            self.assertEqual(answer['status'], 'INCONCLUSIVE')
            self.assertNotIn('certificate', answer)
            self.assertEqual(len(calls), 1)

    def test_exact_complete_producer_allowance(self):
        raw, support = double_cap(), [(0, 2), (1, 1), (2, 1)]
        total = certify_planar_sector(raw, support)['stats']['work_units']
        answer = certify_planar_sector(raw, support, max_work=total - 1)
        self.assertEqual(answer['status'], 'INCONCLUSIVE')
        self.assertNotIn('certificate', answer)
        answer = certify_planar_sector(raw, support, max_work=total)
        self.assertEqual(answer['status'], 'COMPLETE')
        self.assertTrue(verify_planar_sector_certificate(raw, answer['certificate']))

    def test_false_valued_callback_and_verifier_limit_propagate(self):
        class Cancel:
            def __bool__(self):
                return False
            def __call__(self):
                raise RuntimeError('caller cancelled')
        raw = double_cap()
        proof = certify_planar_sector(raw, [(0, 2), (1, 1), (2, 1)])['certificate']
        with self.assertRaisesRegex(RuntimeError, 'caller cancelled'):
            certify_planar_sector(raw, [], check=Cancel())
        with self.assertRaisesRegex(RuntimeError, 'caller cancelled'):
            verify_planar_sector_certificate(raw, proof, check=Cancel())
        with self.assertRaises(PlanarVerificationLimit):
            verify_planar_sector_certificate(raw, proof, max_work=0)

    def test_positive_and_negative_disc_certificates(self):
        raw = solid_torus()
        answer = discover_planar_in_sector(raw, [(0, 2)])
        self.assertEqual(answer['status'], 'DISC_FOUND')
        self.assertTrue(verify_sector_witness(raw, answer['certificate']))
        answer = discover_planar_in_sector(raw, [(0, 0)])
        self.assertEqual(answer['status'], 'NO_POSITIVE_EULER')
        self.assertTrue(verify_planar_exhaustion(raw, answer['certificate']))
        raw = capped_solid_torus()
        answer = discover_planar_in_sector(raw, [(1, 0)])
        self.assertEqual(answer['status'], 'NO_VERTEX_DISC_IN_SECTOR')
        self.assertTrue(verify_planar_exhaustion(raw, answer['certificate']))
        proof = deepcopy(answer['certificate'])
        proof['rays'][0]['euler_characteristic'] += 1
        self.assertFalse(verify_planar_exhaustion(raw, proof))

    def test_empty_sector_is_exact_and_source_bound(self):
        raw = solid_torus()
        proof = certify_planar_sector(raw, [])['certificate']
        self.assertEqual(proof['quadrilateral_rays'], [])
        self.assertTrue(verify_planar_sector_certificate(raw, proof))
        changed = deepcopy(raw); changed['metadata'] = 'different encoding'
        self.assertFalse(verify_planar_sector_certificate(changed, proof))


if __name__ == '__main__':
    unittest.main()
