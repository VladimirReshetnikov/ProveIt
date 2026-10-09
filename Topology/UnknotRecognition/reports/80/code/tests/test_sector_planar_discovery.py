"""Composition of complete sector coverage with maintained disc certificates."""

from copy import deepcopy
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from fastunknot.normal_sector_verify import verify_sector_witness
from fastunknot.sector_planar import discover_in_planar_sector
from fastunknot.sector_planar_verify import verify_planar_disc_exhaustion
from planar_sector_research.fixtures import double_capped_fibonacci


class PlanarDiscoveryTests(unittest.TestCase):
    def setUp(self):
        self.fixture = double_capped_fibonacci(1)
        self.tri = self.fixture['triangulation']

    def test_positive_uses_maintained_independent_witness_replay(self):
        result = discover_in_planar_sector(self.tri, self.fixture['allowed_types'])
        self.assertEqual(result['status'], 'DISC_FOUND')
        certificate = json.loads(json.dumps(result['certificate']))
        self.assertTrue(verify_sector_witness(self.tri, certificate))
        self.assertFalse(verify_planar_disc_exhaustion(self.tri, certificate))

    def test_nonempty_and_empty_sector_exhaustion(self):
        for support, ray_count in (([], 0), ([(1, 1)], 1), ([(2, 1)], 1)):
            result = discover_in_planar_sector(self.tri, support)
            self.assertEqual(result['status'], 'NO_VERTEX_DISC_IN_SECTOR')
            proof = json.loads(json.dumps(result['certificate']))
            self.assertEqual(len(proof['checks']), ray_count)
            self.assertTrue(verify_planar_disc_exhaustion(self.tri, proof))
            wrong_source = deepcopy(proof)
            wrong_source['source_sha256'] = '0'*64
            self.assertFalse(verify_planar_disc_exhaustion(self.tri, wrong_source))
            if ray_count:
                missing = deepcopy(proof)
                missing['checks'].clear()
                self.assertFalse(verify_planar_disc_exhaustion(self.tri, missing))
                changed_count = deepcopy(proof)
                changed_count['checks'][0]['disk_certificate']['compressing_disk_components'] = 1
                self.assertFalse(verify_planar_disc_exhaustion(self.tri, changed_count))
                changed_ray = deepcopy(proof)
                changed_ray['checks'][0]['ray'] = True
                self.assertFalse(verify_planar_disc_exhaustion(self.tri, changed_ray))

    def test_partial_ray_allowance_is_inconclusive_without_exhaustion_proof(self):
        result = discover_in_planar_sector(self.tri, self.fixture['allowed_types'], max_rays=6)
        self.assertEqual(result['status'], 'INCONCLUSIVE')
        self.assertNotIn('certificate', result)
        with self.assertRaises(ValueError):
            discover_in_planar_sector(self.tri, [], max_orbit_cycles=True)

    def test_false_valued_interruptions_propagate(self):
        class Stop:
            def __bool__(self):
                return False

            def __call__(self):
                raise RuntimeError('deliberate stop')

        result = discover_in_planar_sector(self.tri, [(1, 1)])
        with self.assertRaisesRegex(RuntimeError, 'deliberate stop'):
            discover_in_planar_sector(self.tri, [], check=Stop())
        with self.assertRaisesRegex(RuntimeError, 'deliberate stop'):
            verify_planar_disc_exhaustion(self.tri, result['certificate'], check=Stop())


if __name__ == '__main__':
    unittest.main()
