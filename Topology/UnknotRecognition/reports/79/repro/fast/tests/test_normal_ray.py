import copy
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT/'scripts'), str(ROOT/'work/fast' if (ROOT/'work').exists() else ROOT/'fast')]
from fibonacci_fixture import fibonacci_torus
from fastunknot.normal_ray import certify_normal_ray_disc
from fastunknot.normal_ray_verify import verify_normal_ray_disc


class NormalRayTests(unittest.TestCase):
    def test_fibonacci_dense_binary(self):
        for t in (1, 4, 16, 64, 256):
            fixture = fibonacci_torus(t)
            answer = certify_normal_ray_disc(fixture['triangulation'], fixture['coordinates'])
            self.assertEqual(answer['status'], 'DISC_FOUND')
            self.assertTrue(verify_normal_ray_disc(fixture['triangulation'],
                           fixture['coordinates'], answer['certificate']))

    def test_nonprimitive_is_not_connected_certificate(self):
        fixture = fibonacci_torus(8)
        rows = [[2*x for x in row] for row in fixture['coordinates']]
        self.assertEqual(certify_normal_ray_disc(fixture['triangulation'], rows)['status'],
                         'NOT_CERTIFIED')

    def test_cap_and_callback(self):
        fixture = fibonacci_torus(8)
        self.assertEqual(certify_normal_ray_disc(fixture['triangulation'],
                         fixture['coordinates'], max_rank_operations=0)['status'], 'INCONCLUSIVE')
        def stop():
            raise ValueError('caller cancellation')
        with self.assertRaisesRegex(ValueError, 'caller cancellation'):
            certify_normal_ray_disc(fixture['triangulation'], fixture['coordinates'], check=stop)
        with self.assertRaisesRegex(ValueError, 'caller cancellation'):
            verify_normal_ray_disc(fixture['triangulation'], fixture['coordinates'], {}, check=stop)

    def test_source_and_rank_tampering(self):
        fixture = fibonacci_torus(8)
        answer = certify_normal_ray_disc(fixture['triangulation'], fixture['coordinates'])
        for key, value in [('prime', True), ('prime', 9), ('rank_rows', [0]*23),
                           ('input_sha256', 'x'), ('schema', 'normal-extreme-disc-v2')]:
            bad = copy.deepcopy(answer['certificate'])
            bad[key] = value
            self.assertFalse(verify_normal_ray_disc(fixture['triangulation'],
                             fixture['coordinates'], bad))

    def test_empty_and_link_controls(self):
        fixture = fibonacci_torus(4)
        for rows in ([[0]*7 for _ in range(4)], [[1,1,1,1,0,0,0] for _ in range(4)]):
            self.assertEqual(certify_normal_ray_disc(fixture['triangulation'], rows)['status'],
                             'NOT_CERTIFIED')

    def test_euler_and_boundary_parity_without_extremality_are_insufficient(self):
        # Vertex-link disc plus the type-1 Mobius band in a one-tetrahedron
        # solid torus: primitive, Euler one, essential total boundary class,
        # but its disc component is boundary-parallel. Rank must reject it.
        fixture = fibonacci_torus(1)
        rows = [[1,1,1,1,0,1,0]]
        answer = certify_normal_ray_disc(fixture['triangulation'], rows)
        self.assertEqual(answer['status'], 'NOT_CERTIFIED')
        self.assertIn('full-rank minor', answer['reason'])


if __name__ == '__main__':
    unittest.main()
