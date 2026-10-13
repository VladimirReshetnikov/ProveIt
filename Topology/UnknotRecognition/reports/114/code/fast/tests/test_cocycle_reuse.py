"""Discovery prefilters cannot bypass independent positive verification."""
from copy import deepcopy
import unittest
from unittest.mock import patch
from fastunknot import Diagram
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.normal_cocycle import _rank_one_cocycle_seed_details,_height_summary
from fastunknot.normal_seed import normal_seed_decide
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from fastunknot.normal_surface_geometry import _coordinates
from fastunknot.cocycle_span import minimize_cocycle_span


class CocycleReuseTests(unittest.TestCase):
    def test_height_cell_count_matches_normal_geometry_under_large_gauges(self):
        for d in (Diagram.from_pd([]),Diagram.from_braid(2,[1,1,1]),Diagram.from_braid(4,[-1,2,1,-2,3])):
            seed,p=_rank_one_cocycle_seed_details(diagram_exterior(d))
            optimized=minimize_cocycle_span(seed['vertices'],seed['heights'])
            for coords,potential in ((seed['coordinates'],None),(optimized['coordinates'],dict(zip(optimized['certificate']['vertex_ids'],optimized['certificate']['potential'])))):
                a=_coordinates(p,coords,lambda:None);summary=_height_summary(p,seed['heights'],potential=potential)
                self.assertEqual(summary,dict(euler_characteristic=a['euler_characteristic'],normal_pieces=a['normal_disks']))
                heights=[[h+(t+1)*(1<<20000) for h in row] for t,row in enumerate(seed['heights'])]
                self.assertEqual(_height_summary(p,heights,potential=potential),summary)
                if potential is not None:
                    gauge={v:(v+1)*(1<<19000) for v in potential}
                    heights=[[h+gauge[v] for h,v in zip(row,vs)] for row,vs in zip(heights,seed['vertices'])]
                    self.assertEqual(_height_summary(p,heights,potential={v:x-gauge[v] for v,x in potential.items()}),summary)

    def test_misses_skip_positive_replay_but_every_success_requires_it(self):
        with patch('fastunknot.normal_seed.inspect_cocycle_certificate',side_effect=AssertionError):
            self.assertEqual(normal_seed_decide(Diagram.from_braid(2,[1,1,1]))['status'],'INCONCLUSIVE')
        for d in (Diagram.from_pd([]),Diagram.from_braid(4,[-1,2,1,-2,3])):
            with patch('fastunknot.normal_seed.inspect_cocycle_certificate',return_value=None) as verify:
                with self.assertRaisesRegex(ArithmeticError,'connectivity replay failed'):normal_seed_decide(d)
            self.assertEqual(verify.call_count,1)
        with patch('fastunknot.normal_planar_verify.inspect_planar_certificate',return_value=None):
            with self.assertRaisesRegex(ArithmeticError,'planar capping replay failed'):
                normal_seed_decide(Diagram.from_braid(4,[-1,2,1,-2,3]),planar=True)

    def test_corrupted_producer_vector_cannot_turn_prefilter_into_positive(self):
        d=Diagram.from_pd([]);seed,p=_rank_one_cocycle_seed_details(diagram_exterior(d))
        seed=deepcopy(seed);seed['coordinates'][0][0]+=1
        with patch('fastunknot.normal_seed._rank_one_cocycle_seed_details',return_value=(seed,p)):
            with self.assertRaisesRegex(ArithmeticError,'connectivity replay failed'):normal_seed_decide(d)

    def test_per_call_geometry_does_not_bypass_fresh_source_binding(self):
        d=Diagram.from_braid(4,[-1,2,1,-2,3]);first=normal_seed_decide(d,planar=True)
        proof=deepcopy(first['certificate']);proof['triangulation']['tetrahedra'][0][0]=None
        self.assertFalse(verify_normal_seed_certificate(d,proof))
        self.assertTrue(verify_normal_seed_certificate(d,first['certificate']))
        second=normal_seed_decide(Diagram.from_braid(2,[1,1,1]),planar=True)
        self.assertEqual(second['status'],'INCONCLUSIVE')
        self.assertEqual(normal_seed_decide(d,planar=True)['certificate'],first['certificate'])
