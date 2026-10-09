"""Positive and negative source-binding tests for the additive ray interface."""

from copy import deepcopy
import unittest
from unittest.mock import patch

from fastunknot.diagram import Diagram
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.normal_cocycle import rank_one_cocycle_seed
from fastunknot.normal_support_diagram import (
    certify_diagram_ray_disks, verify_diagram_ray_disk_certificate,
)


class SourceRayDiscTests(unittest.TestCase):
    def test_canonical_exteriors_and_cocycle_candidates(self):
        for n in (1, 2, 4, 8):
            source = Diagram.from_braid(n+1, list(range(1, n+1)))
            raw = diagram_exterior(source)
            vector = rank_one_cocycle_seed(raw)['coordinates']
            answer = certify_diagram_ray_disks(source, vector, max_cycles=0)
            self.assertEqual(answer['status'], 'UNKNOT')
            self.assertEqual(answer['stats']['orbit_cycles'], 0)
            with patch('fastunknot.normal_ray_blocks.normal_ray_block_disk_count',
                       side_effect=AssertionError('producer invoked')):
                self.assertTrue(verify_diagram_ray_disk_certificate(source, answer['certificate']))

    def test_zero_count_is_inconclusive_and_rejects_positive_wrapper(self):
        source = Diagram.from_braid(2, [1])
        raw = diagram_exterior(source)
        zero = [[0]*7 for _ in raw['tetrahedra']]
        self.assertEqual(certify_diagram_ray_disks(source, zero)['status'], 'INCONCLUSIVE')
        from fastunknot.normal_ray_blocks import normal_ray_block_disk_count
        proof = dict(schema='diagram-ray-disks-v1', input_pd=[list(row) for row in source.pd],
            triangulation=raw, coordinates=zero,
            disc_certificate=normal_ray_block_disk_count(raw, zero, record_certificate=True)['certificate'])
        self.assertFalse(verify_diagram_ray_disk_certificate(source, proof))

    def test_cross_source_and_geometry_mutations(self):
        source = Diagram.from_braid(2, [1])
        raw = diagram_exterior(source)
        vector = rank_one_cocycle_seed(raw)['coordinates']
        proof = certify_diagram_ray_disks(source, vector)['certificate']
        trefoil = Diagram.from_braid(2, [1, 1, 1])
        self.assertFalse(verify_diagram_ray_disk_certificate(trefoil, proof))
        altered = deepcopy(proof)
        altered['input_pd'] = [list(row) for row in trefoil.pd]
        self.assertFalse(verify_diagram_ray_disk_certificate(trefoil, altered))
        altered = deepcopy(proof)
        record = next(record for row in altered['triangulation']['tetrahedra']
                      for record in row if record is not None)
        record['tetrahedron'] = -1
        self.assertFalse(verify_diagram_ray_disk_certificate(source, altered))


if __name__ == '__main__':
    unittest.main()
