"""Primitive annulus caps, strict witness semantics and source authentication."""
from contextlib import ExitStack
from copy import deepcopy
import json
import unittest
from unittest.mock import patch
from fastunknot import Diagram, recognize
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.normal_cocycle import rank_one_cocycle_seed, local_coordinates
from fastunknot.normal_annulus_verify import inspect_annulus_certificate
from fastunknot.normal_cocycle_verify import inspect_cocycle_certificate, _primitive_cochain
from fastunknot.normal_seed import normal_seed_decide
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from fastunknot.normal_surface_geometry import _prepare, _coordinates
from fastunknot.normal_surface_components import normal_component_census
from fastunknot.integer_codec import json_safe
from tests.test_cocycle_trees import EARLY_TWO, EARLY_THREE
from tests.test_cocycle_face import NEW_DISC
from tests.test_normal_seed import OPTIONS

class NormalAnnulusTests(unittest.TestCase):
    def test_raw_annulus_preempts_trees_and_flow_and_replays_independently(self):
        for pd in (EARLY_TWO,EARLY_THREE):
            diagram=Diagram.from_pd(pd)
            with patch('fastunknot.normal_seed.cocycle_tree_candidates',side_effect=AssertionError), \
                 patch('fastunknot.normal_seed.minimize_cocycle_span',side_effect=AssertionError):
                result=normal_seed_decide(diagram)
            self.assertEqual(result['status'],'UNKNOT')
            self.assertEqual(result['stages'][-1]['stage'],'raw')
            self.assertEqual(result['stages'][-1]['compressing_discs'],0)
            self.assertEqual(result['stages'][-1]['unknot_witness'],'annulus-cap')
            self.assertNotIn('tree_search',result['stats'])
            proof=json.loads(json.dumps(result['certificate']))
            self.assertEqual(proof['schema'],'diagram-cocycle-annulus-v1')
            with ExitStack() as stack:
                for target in ('normal_seed.normal_seed_decide','normal_cocycle.rank_one_cocycle_seed',
                               'cocycle_span.minimize_cocycle_span','cocycle_trees.cocycle_tree_candidates',
                               'cocycle_face.cocycle_face_candidates','diagram_exterior.diagram_exterior',
                               'normal_surface_components.normal_component_census','interval_orbits.count_orbits'):
                    stack.enter_context(patch('fastunknot.'+target,side_effect=AssertionError))
                self.assertTrue(verify_normal_seed_certificate(diagram,proof))
            self.assertEqual(inspect_annulus_certificate(diagram,proof)['euler_characteristic'],0)

    def test_optimized_annulus_avoids_the_tied_disc_search(self):
        diagram=Diagram.from_pd(NEW_DISC)
        self.assertEqual(normal_seed_decide(diagram,annulus=False)['status'],'INCONCLUSIVE')
        with patch('fastunknot.normal_seed.cocycle_face_candidates',side_effect=AssertionError):
            result=normal_seed_decide(diagram,face_roots=4)
        self.assertEqual(result['status'],'UNKNOT')
        self.assertEqual(result['stages'][-1]['stage'],'optimized')
        self.assertEqual(result['stages'][-1]['normal_pieces'],122)
        self.assertEqual(result['stages'][-1]['compressing_discs'],0)
        self.assertNotIn('face_search',result['stats'])
        self.assertTrue(verify_normal_seed_certificate(diagram,result['certificate']))
        answer=recognize(diagram,**OPTIONS)
        self.assertEqual(answer.method,'native-normal-cocycle')
        self.assertEqual(answer.evidence['normal_seed']['certificate']['schema'],'diagram-cocycle-annulus-v1')

    def test_disc_annulus_tags_and_malformed_proofs_are_not_interchangeable(self):
        diagram=Diagram.from_pd(EARLY_TWO);proof=normal_seed_decide(diagram)['certificate']
        old=dict(proof,schema='diagram-cocycle-disc-v1')
        self.assertIsNotNone(inspect_cocycle_certificate(diagram,old))
        self.assertFalse(verify_normal_seed_certificate(diagram,old))
        circle=Diagram.from_pd([]);disc=normal_seed_decide(circle)['certificate']
        self.assertTrue(verify_normal_seed_certificate(circle,disc))
        self.assertFalse(verify_normal_seed_certificate(circle,dict(disc,schema='diagram-cocycle-annulus-v1')))
        for key in proof:
            bad=deepcopy(proof);del bad[key]
            self.assertFalse(verify_normal_seed_certificate(diagram,bad))
        for field,value in [('input_pd',[]),('heights',[]),('coordinates',[]),('span_certificate',{}),('schema',True)]:
            self.assertFalse(verify_normal_seed_certificate(diagram,dict(proof,**{field:value})))
        self.assertFalse(verify_normal_seed_certificate(diagram,dict(proof,extra=1)))
        bad=deepcopy(proof);bad['heights'][0][0]+=1
        self.assertFalse(verify_normal_seed_certificate(diagram,bad))
        bad=deepcopy(proof);bad['coordinates'][0][0]+=1
        self.assertFalse(verify_normal_seed_certificate(diagram,bad))
        self.assertFalse(verify_normal_seed_certificate(Diagram.from_braid(2,[1,1,1]),proof))

    def test_primitive_euler_zero_without_connectivity_is_not_an_annulus(self):
        diagram=Diagram.from_braid(2,[1,1,1]);raw=diagram_exterior(diagram)
        seed=rank_one_cocycle_seed(raw);prepared=_prepare(raw,lambda:None)
        heights=[[x-int(v==3) for x,v in zip(hs,vs)] for hs,vs in zip(seed['heights'],seed['vertices'])]
        coordinates=[local_coordinates(row) for row in heights]
        self.assertIsNotNone(_primitive_cochain(prepared,heights,False,lambda:None))
        self.assertIsNone(_primitive_cochain(prepared,heights,True,lambda:None))
        self.assertEqual(_coordinates(prepared,coordinates,lambda:None)['euler_characteristic'],0)
        census=normal_component_census(raw,coordinates)
        self.assertEqual(census['components'],2)
        self.assertEqual(census['compressing_disk_components'],0)
        proof=dict(schema='diagram-cocycle-annulus-v1',input_pd=[list(r) for r in diagram.pd],
                   triangulation=raw,heights=heights,coordinates=coordinates,span_certificate=None)
        self.assertIsNone(inspect_annulus_certificate(diagram,proof))
        self.assertFalse(verify_normal_seed_certificate(diagram,proof))

    def test_gauge_transport_zero_and_multiple_classes_and_huge_json(self):
        diagram=Diagram.from_pd(NEW_DISC);proof=normal_seed_decide(diagram)['certificate']
        prepared=_prepare(proof['triangulation'],lambda:None);span=proof['span_certificate']
        for t,row in enumerate(proof['heights']):
            for i in range(4):
                row[i]+=(t+1)*(1<<20001)+(prepared['vertex_roots'][4*t+i]+1)*(1<<20000)
        span['potential']=[x-(v+1)*(1<<20000) for v,x in zip(span['vertex_ids'],span['potential'])]
        self.assertTrue(verify_normal_seed_certificate(diagram,json.loads(json.dumps(json_safe(proof)))))
        from fastunknot.cocycle_span import minimize_cocycle_span
        raw=diagram_exterior(diagram);seed=rank_one_cocycle_seed(raw)
        for scale in (0,2):
            h=[[scale*x for x in row] for row in seed['heights']]
            optimum=minimize_cocycle_span(seed['vertices'],h)['certificate']
            candidate=dict(schema='diagram-cocycle-annulus-v1',input_pd=[list(r) for r in diagram.pd],
                           triangulation=raw,heights=h,coordinates=optimum['coordinates'],span_certificate=optimum)
            self.assertFalse(verify_normal_seed_certificate(diagram,candidate))

    def test_connected_null_class_annulus_in_a_trefoil_is_rejected(self):
        diagram=Diagram.from_braid(2,[1,1,1]);raw=diagram_exterior(diagram)
        seed=rank_one_cocycle_seed(raw);prepared=_prepare(raw,lambda:None)
        heights=[[int(v in (3,7)) for v in row] for row in seed['vertices']]
        coordinates=[local_coordinates(row) for row in heights]
        census=normal_component_census(raw,coordinates)
        self.assertEqual(census['components'],1)
        self.assertEqual(_coordinates(prepared,coordinates,lambda:None)['euler_characteristic'],0)
        self.assertEqual(sum(map(sum,coordinates)),20)
        self.assertEqual(census['compressing_disk_components'],0)
        self.assertIsNone(_primitive_cochain(prepared,heights,False,lambda:None))
        proof=dict(schema='diagram-cocycle-annulus-v1',input_pd=[list(r) for r in diagram.pd],
                   triangulation=raw,heights=heights,coordinates=coordinates,span_certificate=None)
        self.assertFalse(verify_normal_seed_certificate(diagram,proof))

    def test_exact_shared_caps_cancellation_and_switch_validation(self):
        diagram=Diagram.from_pd(EARLY_TWO);result=normal_seed_decide(diagram)
        self.assertEqual(normal_seed_decide(diagram,max_work=result['work'])['certificate'],result['certificate'])
        self.assertEqual(normal_seed_decide(diagram,max_work=result['work']-1)['status'],'INCONCLUSIVE')
        calls=[0]
        def tick():calls[0]+=1
        self.assertTrue(verify_normal_seed_certificate(diagram,result['certificate'],check=tick))
        total=calls[0]
        for limit in (1,total//2,total):
            calls[0]=0
            def stop():
                tick()
                if calls[0]==limit:raise RuntimeError('cancelled')
            with self.assertRaisesRegex(RuntimeError,'cancelled'):
                verify_normal_seed_certificate(diagram,result['certificate'],check=stop)
        for value in (0,1,None,'yes'):
            with self.assertRaises(ValueError):normal_seed_decide(diagram,annulus=value)
            with self.assertRaises(ValueError):recognize(diagram,normal_seed_annulus=value)

if __name__=='__main__':unittest.main()
