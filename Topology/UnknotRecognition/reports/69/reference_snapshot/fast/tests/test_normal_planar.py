from copy import deepcopy
import json
import unittest
from unittest.mock import patch
from fastunknot import Diagram, recognize
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.normal_cocycle import rank_one_cocycle_seed, local_coordinates
from fastunknot.normal_seed import normal_seed_decide
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from fastunknot.normal_planar import planar_cap_candidate
from fastunknot.normal_planar_verify import inspect_planar_certificate
from fastunknot.normal_boundary_geometry import boundary_weight_system
from fastunknot.normal_component_geometry import boundary_homology_basis
from fastunknot.normal_surface_geometry import _prepare, _coordinates
from fastunknot.weighted_orbits import weighted_orbit_histogram
from fastunknot.weighted_orbit_verify import verify_weighted_orbit_certificate
from fastunknot.integer_codec import json_safe


def example():
    return Diagram.from_braid(4, [-1,2,1,-2,3])


class PlanarCapTests(unittest.TestCase):
    def test_earlier_tree_with_seven_boundaries_and_producer_free_replay(self):
        d=example();old=normal_seed_decide(d);new=normal_seed_decide(d,planar=True)
        self.assertEqual(old['stages'][-1]['stage'],'optimized')
        self.assertEqual(new['stages'][-1]['trial'],2)
        self.assertEqual(new['stages'][-1]['euler_characteristic'],-5)
        self.assertEqual(new['stages'][-1]['boundary_components'],7)
        self.assertEqual(new['stages'][-1]['compressing_discs'],0)
        self.assertNotIn('optimization',new['stats'])
        with patch('fastunknot.normal_seed.normal_seed_decide',side_effect=AssertionError), \
             patch('fastunknot.normal_planar.planar_cap_candidate',side_effect=AssertionError), \
             patch('fastunknot.normal_planar.weighted_orbit_histogram',side_effect=AssertionError), \
             patch('fastunknot.interval_orbits.count_orbits',side_effect=AssertionError), \
             patch('fastunknot.normal_component_geometry.boundary_homology_basis',side_effect=AssertionError):
            self.assertTrue(verify_normal_seed_certificate(d,new['certificate']))
        from normal_orbit_research.seeds import FORCED
        answer=recognize(d,**FORCED,normal_seed_planar=True)
        self.assertEqual(answer.method,'native-normal-cocycle')
        self.assertEqual(answer.evidence['normal_seed']['certificate'],new['certificate'])

    def test_strict_schema_source_basis_and_weight_trace(self):
        d=example();proof=normal_seed_decide(d,planar=True)['certificate']
        for field in proof:
            bad=deepcopy(proof);del bad[field]
            self.assertFalse(verify_normal_seed_certificate(d,bad))
        for field,value in [('schema','diagram-cocycle-disc-v1'),('input_pd',[]),('heights',[]),
                            ('coordinates',[]),('span_certificate',{}),('boundary_homology_basis',[[0],[0]]),
                            ('boundary_orbits',{}),('extra',1)]:
            self.assertFalse(verify_normal_seed_certificate(d,dict(proof,**{field:value})))
        for field in ('orbits','weight'):
            bad=deepcopy(proof)
            if field=='orbits':bad['boundary_orbits']['histogram'][0][field]+=1
            else:bad['boundary_orbits']['histogram'][0][field][0]+=1
            self.assertFalse(verify_normal_seed_certificate(d,bad))
        self.assertFalse(verify_normal_seed_certificate(Diagram.from_braid(2,[1,1,1]),proof))

    def test_positive_genus_null_class_and_disconnected_trefoil_controls(self):
        d=Diagram.from_braid(2,[1,1,1]);raw=diagram_exterior(d);seed=rank_one_cocycle_seed(raw)
        for variant in ('primitive','null','disconnected'):
            h=seed['heights'] if variant=='primitive' else [[int(v in (3,7)) if variant=='null' else x-int(v==3)
                for x,v in zip(hs,vs)] for hs,vs in zip(seed['heights'],seed['vertices'])]
            coords=[local_coordinates(row) for row in h]
            base=dict(schema='diagram-cocycle-disc-v1',input_pd=[list(r) for r in d.pd],triangulation=raw,
                      heights=h,coordinates=coords,span_certificate=None)
            p=_prepare(raw,lambda:None);a=_coordinates(p,coords,lambda:None);basis=boundary_homology_basis(p)
            size,pairs,weights=boundary_weight_system(p,a,basis)
            query=weighted_orbit_histogram(size,pairs,weights,dimension=2,record_certificate=True)
            proof=dict(base,schema='diagram-cocycle-planar-v1',boundary_homology_basis=basis,boundary_orbits=query['certificate'])
            self.assertIsNone(inspect_planar_certificate(d,proof))

    def test_binary_boundary_multiplicity_and_gauge_json(self):
        d=example();proof=normal_seed_decide(d,planar=True)['certificate']
        p=_prepare(proof['triangulation'],lambda:None);basis=proof['boundary_homology_basis'];multiple=1<<2000
        coordinates=[[x*multiple for x in row] for row in proof['coordinates']]
        a=_coordinates(p,coordinates,lambda:None);size,pairs,weights=boundary_weight_system(p,a,basis)
        q=weighted_orbit_histogram(size,pairs,weights,dimension=2,record_certificate=True)
        self.assertEqual(q['orbit_count'],7*multiple)
        self.assertEqual(sum(r['orbits'] for r in q['histogram'] if any(x&1 for x in r['weight'])),multiple)
        self.assertTrue(verify_weighted_orbit_certificate(size,pairs,weights,q['certificate'],dimension=2))
        for t,row in enumerate(proof['heights']):proof['heights'][t]=[x+(t+1)*(1<<20000) for x in row]
        self.assertTrue(verify_normal_seed_certificate(d,json.loads(json.dumps(json_safe(proof)))))
        bad=deepcopy(proof);bad['heights']=[[2*x for x in row] for row in proof['heights']]
        bad['coordinates']=[[2*x for x in row] for row in proof['coordinates']]
        self.assertFalse(verify_normal_seed_certificate(d,bad))

    def test_shared_work_and_cycle_limits_and_legacy_default(self):
        d=example();kwargs=dict(planar=True,tree_trials=2,optimize=False);result=normal_seed_decide(d,**kwargs)
        self.assertEqual(result['status'],'UNKNOT')
        self.assertEqual(normal_seed_decide(d,**kwargs,max_work=result['work'])['certificate'],result['certificate'])
        self.assertEqual(normal_seed_decide(d,**kwargs,max_work=result['work']-1)['status'],'INCONCLUSIVE')
        self.assertEqual(normal_seed_decide(d,**kwargs,max_cycles=0)['status'],'INCONCLUSIVE')
        cycles=result['stats']['boundary_cycles']
        self.assertEqual(normal_seed_decide(d,**kwargs,max_cycles=cycles)['certificate'],result['certificate'])
        self.assertEqual(normal_seed_decide(d,**kwargs,max_cycles=cycles-1)['status'],'INCONCLUSIVE')
        self.assertEqual(normal_seed_decide(d),normal_seed_decide(d,planar=False))
        for value in (0,1,None,'true'):
            with self.assertRaises(ValueError):normal_seed_decide(d,planar=value)
            with self.assertRaises(ValueError):recognize(d,normal_seed_planar=value)

    def test_cancellation_during_boundary_discovery_and_replay(self):
        d=example();proof=normal_seed_decide(d,planar=True)['certificate']
        for operation in (lambda check:verify_normal_seed_certificate(d,proof,check=check),
                          lambda check:planar_cap_candidate(proof,check=check)):
            calls=[0]
            def tick():calls[0]+=1
            operation(tick);total=calls[0]
            for stop in (1,total//2,total):
                calls[0]=0
                def cancel():
                    tick()
                    if calls[0]==stop:raise RuntimeError('cancelled')
                with self.assertRaisesRegex(RuntimeError,'cancelled'):operation(cancel)
