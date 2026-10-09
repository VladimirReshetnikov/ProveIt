"""Finite double-cover trivializations, fallback and independent replay."""
from copy import deepcopy
import json
import random
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from fastunknot.normal_surface_orbits import normal_surface_topology
from fastunknot.normal_surface_verify import verify_normal_surface_certificate
from fastunknot.normal_surface_geometry import _prepare, _coordinates, _arc_system, _TOPOLOGY_FIELDS, _BOUNDARY_FIELDS
from fastunknot.normal_coorientation import _coorientation_graph
from normal_orbit_research.fixtures import layered_torus
from tests.test_normal_surface_orbits import relabel


def topology(result):
    return {k:result[k] for k in _TOPOLOGY_FIELDS+_BOUNDARY_FIELDS if k in result}


class NormalCoorientationTests(unittest.TestCase):
    def test_default_derivation_and_literal_doubled_arc_conjugacy(self):
        for n in (1,2,4,8):
            raw,coords=layered_torus(n)
            old=normal_surface_topology(raw,coords,coorientation=False,record_certificate=True)
            new=normal_surface_topology(raw,coords,record_certificate=True)
            self.assertEqual(topology(old),topology(new))
            self.assertEqual(new['cycles'],old['cycles']-old['queries']['double']['cycles'])
            self.assertEqual(new['certificate']['schema'],'normal-surface-topology-v4')
            self.assertEqual(new['queries']['double']['cycles'],0)
            self.assertEqual(new['certificate']['queries']['double']['operations'],[])
            for answer in (old,new):self.assertTrue(verify_normal_surface_certificate(raw,coords,answer['certificate']))
            p=_prepare(raw,lambda:None);a=_coordinates(p,coords,lambda:None)
            size,pairs=_arc_system(p,a);double,doubled=_arc_system(p,a,scale=2)
            self.assertEqual(double,2*size)
            graph=_coorientation_graph(a,pairs,lambda:None)
            colors=dict(new['certificate']['queries']['double']['coorientation']['vertex_values'])
            for (u,v,bit),pair,lift in zip(graph,pairs,doubled):
                self.assertEqual([lift.a,lift.b,lift.c,lift.d,lift.reverse],
                                 [2*pair.a,2*pair.b+1,2*pair.c,2*pair.d+1,pair.reverse])
                for i in range(pair.a,pair.b+1):
                    image=pair.d-(i-pair.a) if pair.reverse else pair.c+i-pair.a
                    for sheet in (0,1):
                        lifted_image=lift.d-(2*i+sheet-lift.a) if lift.reverse else lift.c+2*i+sheet-lift.a
                        self.assertEqual(lifted_image,2*image+(sheet^bit))
                        self.assertEqual(sheet^colors[u],(sheet^bit)^colors[v])

    def test_failure_is_inconclusive_for_orientability(self):
        raw,_=layered_torus(1)
        for vector in ([[0,0,0,0,0,1,0]],[[0,0,0,0,0,2,0]],[[1,1,1,1,0,0,0]]):
            old=normal_surface_topology(raw,vector,coorientation=False,record_certificate=True)
            new=normal_surface_topology(raw,vector,record_certificate=True)
            self.assertEqual(old,new)
            self.assertTrue(verify_normal_surface_certificate(raw,vector,new['certificate']))
        # The latter two examples are orientable despite failing the coarse test.
        for vector in ([[0,0,0,0,0,2,0]],[[1,1,1,1,0,0,0]]):
            self.assertEqual(normal_surface_topology(raw,vector)['nonorientable_components'],0)

    def test_classification_scaling_relabelling_and_empty_surface(self):
        rng=random.Random(261009516)
        raw,base=layered_torus(4)
        for _ in range(8):
            raw,base=relabel(raw,base,rng)
            for scale in (0,1,2,7):
                coords=[[scale*v for v in row] for row in base]
                for reduce in (False,True):
                    old=normal_surface_topology(raw,coords,coorientation=False,reduce_multiplicity=reduce,
                                                classify_boundary=True,record_certificate=True)
                    new=normal_surface_topology(raw,coords,reduce_multiplicity=reduce,
                                                classify_boundary=True,record_certificate=True)
                    self.assertEqual(topology(old),topology(new))
                    self.assertTrue(verify_normal_surface_certificate(raw,coords,new['certificate']))
        coords=[[((1<<20000)+1)*v for v in row] for row in base]
        result=normal_surface_topology(raw,coords,classify_boundary=True,record_certificate=True)
        proof=json.loads(json.dumps(json_safe(result['certificate'])))
        self.assertTrue(verify_normal_surface_certificate(raw,coords,proof))

    def test_no_search_in_replay_and_strict_derived_proof(self):
        raw,coords=layered_torus(8)
        result=normal_surface_topology(raw,coords,record_certificate=True);proof=result['certificate']
        with patch('fastunknot.normal_surface_orbits.count_orbits',side_effect=AssertionError), \
             patch('fastunknot.interval_orbits.count_orbits',side_effect=AssertionError), \
             patch('fastunknot.normal_surface_parity._parity_certificate',side_effect=AssertionError):
            self.assertTrue(verify_normal_surface_certificate(raw,coords,proof))
        for field in proof:
            bad=deepcopy(proof);del bad[field]
            self.assertFalse(verify_normal_surface_certificate(raw,coords,bad))
        for key,value in [('classify_boundary',0),('classify_boundary',True),('coordinate_divisor',2),
                          ('schema','normal-surface-topology-v3'),('extra',1)]:
            self.assertFalse(verify_normal_surface_certificate(raw,coords,dict(proof,**{key:value})))
        for key,value in [('schema','wrong'),('operations',[{}]),('orbit_count',3),('orbit_count',True),
                          ('coorientation',None),('extra',0)]:
            bad=deepcopy(proof);bad['queries']['double'][key]=value
            self.assertFalse(verify_normal_surface_certificate(raw,coords,bad))
        for action in ('flip','badbit','bool','missing','duplicate','cycle','extra'):
            bad=deepcopy(proof);p=bad['queries']['double']['coorientation'];values=p['vertex_values']
            if action=='flip':values[0][1]^=1
            elif action=='badbit':values[0][1]=2
            elif action=='bool':values[0][1]=True
            elif action=='missing':values.pop()
            elif action=='duplicate':values.append(values[0])
            elif action=='cycle':p.clear();p.update(nonzero=True,cycle_edges=[0])
            else:p['extra']=0
            self.assertFalse(verify_normal_surface_certificate(raw,coords,bad),action)
        # A simultaneous color reversal is a legitimate alternate trivialization.
        alternate=deepcopy(proof)
        for row in alternate['queries']['double']['coorientation']['vertex_values']:row[1]^=1
        self.assertTrue(verify_normal_surface_certificate(raw,coords,alternate))

    def test_cycle_operation_caps_and_cancellation(self):
        raw,coords=layered_torus(8)
        new=normal_surface_topology(raw,coords,record_certificate=True)
        self.assertEqual(normal_surface_topology(raw,coords,record_certificate=True,max_cycles=new['cycles']),new)
        for options in ({},{'coorientation':False}):
            partial=normal_surface_topology(raw,coords,record_certificate=True,max_cycles=new['cycles']-1,**options)
            self.assertEqual(partial['status'],'INCONCLUSIVE');self.assertNotIn('certificate',partial)
        proof=new['certificate'];events=sum(len(p['operations']) for p in proof['queries'].values())
        self.assertTrue(verify_normal_surface_certificate(raw,coords,proof,max_operations=events))
        self.assertFalse(verify_normal_surface_certificate(raw,coords,proof,max_operations=events-1))
        for operation in (lambda c:normal_surface_topology(raw,coords,check=c),
                          lambda c:verify_normal_surface_certificate(raw,coords,proof,check=c)):
            calls=[0]
            def tick():calls[0]+=1
            operation(tick);total=calls[0]
            for stop in (1,total//2,total):
                calls[0]=0
                def cancel():
                    tick()
                    if calls[0]==stop:raise RuntimeError('cancelled')
                with self.assertRaisesRegex(RuntimeError,'cancelled'):operation(cancel)
        for invalid in (0,1,None,'true'):
            with self.assertRaises(ValueError):normal_surface_topology(raw,coords,coorientation=invalid)
