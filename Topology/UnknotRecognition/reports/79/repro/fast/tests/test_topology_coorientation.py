"""Weighted double-cover trivialization, strict replay and complete fallback."""
from contextlib import ExitStack
from copy import deepcopy
import json
import random
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from fastunknot.normal_topology import normal_topology_spectrum
from fastunknot.normal_topology_verify import verify_normal_topology_spectrum
from fastunknot.normal_surface_geometry import _prepare,_coordinates,_arc_system
from fastunknot.normal_topology_geometry import topology_weight_system
from fastunknot.normal_coorientation import _coorientation_graph
from normal_orbit_research.fixtures import layered_torus
from tests.test_normal_surface_orbits import relabel


class TopologyCoorientationTests(unittest.TestCase):
    def test_literal_lift_preserves_each_point_weight_and_component_signature(self):
        for n in (1,2,4):
            raw,coords=layered_torus(n)
            old=normal_topology_spectrum(raw,coords,coorientation=False,record_certificate=True)
            new=normal_topology_spectrum(raw,coords,record_certificate=True)
            self.assertEqual(old['topology_spectrum'],new['topology_spectrum'])
            self.assertEqual(new['certificate']['schema'],'normal-topology-spectrum-v2')
            self.assertEqual(new['stats']['queries'],2)
            self.assertEqual(new['stats']['orbit_cycles'],old['stats']['orbit_cycles']-old['stats']['double']['orbit_cycles'])
            self.assertTrue(verify_normal_topology_spectrum(raw,coords,new['certificate']))
            prepared=_prepare(raw,lambda:None);analysed=_coordinates(prepared,coords,lambda:None)
            marks=new['certificate']['query']['boundary_transversal']['representative_intervals']
            base=topology_weight_system(prepared,analysed,marks)
            double=topology_weight_system(prepared,analysed,marks,scale=2)
            weights=[]
            for system in (base,double):
                values=[[0,0] for _ in range(system['size'])]
                for lo,hi,increment in system['weights']:
                    for point in range(lo,hi):
                        for j in range(2):values[point][j]+=increment[j]
                weights.append(values)
            self.assertEqual(weights[1],[value for row in weights[0] for value in (row,row)])
            colors=dict(new['certificate']['query']['double']['coorientation']['vertex_values'])
            graph=_coorientation_graph(analysed,base['pairings'],lambda:None)
            for (u,v,bit),pair,lift in zip(graph,base['pairings'],double['pairings']):
                for point in range(pair.a,pair.b+1):
                    image=pair.d-(point-pair.a) if pair.reverse else pair.c+point-pair.a
                    for sheet in (0,1):
                        target=lift.d-(2*point+sheet-lift.a) if lift.reverse else lift.c+2*point+sheet-lift.a
                        self.assertEqual(target,2*image+(sheet^bit))
                        self.assertEqual(sheet^colors[u],(sheet^bit)^colors[v])
            base_hist=new['certificate']['query']['surface']['histogram']
            self.assertEqual(new['certificate']['query']['double']['histogram'],
                             [dict(weight=r['weight'],orbits=2*r['orbits']) for r in base_hist])

    def test_coarse_misses_preserve_the_complete_result_even_when_orientable(self):
        raw,_=layered_torus(1)
        for vector in ([[0,0,0,0,0,1,0]],[[0,0,0,0,0,2,0]],[[1,1,1,1,0,0,0]]):
            for reduced in (False,True):
                old=normal_topology_spectrum(raw,vector,reduce_core=reduced,coorientation=False,record_certificate=True)
                new=normal_topology_spectrum(raw,vector,reduce_core=reduced,record_certificate=True)
                self.assertEqual(new,old)
                self.assertTrue(verify_normal_topology_spectrum(raw,vector,new['certificate']))
        self.assertEqual(normal_topology_spectrum(raw,[[0,0,0,0,0,2,0]])['nonorientable_components'],0)

    def test_relabelling_and_binary_scaling_preserve_types_and_replay(self):
        raw,coords=layered_torus(4);rng=random.Random(26101001)
        for _ in range(6):
            raw,coords=relabel(raw,coords,rng)
            for m in (0,1,2,7,(1<<20000)+1):
                vector=[[m*x for x in row] for row in coords]
                for reduced in (False,True):
                    old=normal_topology_spectrum(raw,vector,reduce_core=reduced,coorientation=False)
                    new=normal_topology_spectrum(raw,vector,reduce_core=reduced,record_certificate=True)
                    self.assertEqual(old['topology_spectrum'],new['topology_spectrum'])
                    proof=json.loads(json.dumps(json_safe(new['certificate'])))
                    self.assertTrue(verify_normal_topology_spectrum(raw,vector,proof))

    def test_derived_proof_mutations_and_producer_disabled_legacy_replay(self):
        raw,coords=layered_torus(8)
        old=normal_topology_spectrum(raw,coords,coorientation=False,record_certificate=True)['certificate']
        proof=normal_topology_spectrum(raw,coords,record_certificate=True)['certificate']
        disabled=['fastunknot.normal_topology.normal_topology_spectrum',
            'fastunknot.normal_topology.canonical_disk_core',
            'fastunknot.normal_topology.orbit_transversal',
            'fastunknot.normal_topology.weighted_orbit_histogram',
            'fastunknot.normal_surface_parity._parity_certificate',
            'fastunknot.interval_orbits.count_orbits','fastunknot.interval_orbits._count_orbits',
            'fastunknot.topology_spectrum.recover_topology_spectrum']
        with ExitStack() as stack:
            for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError))
            for cert in (proof,old):self.assertTrue(verify_normal_topology_spectrum(raw,coords,cert))
        for field in proof['query']['double']:
            bad=deepcopy(proof);del bad['query']['double'][field]
            self.assertFalse(verify_normal_topology_spectrum(raw,coords,bad))
        for field,value in [('schema','bad'),('dimension',True),('dimension',3),
                            ('coorientation',None),('histogram',[]),('extra',0)]:
            bad=deepcopy(proof);bad['query']['double'][field]=value
            self.assertFalse(verify_normal_topology_spectrum(raw,coords,bad))
        for action in ('flip','badbit','bool','missing','duplicate','cycle','extra','weight','count','duplicate_histogram'):
            bad=deepcopy(proof);double=bad['query']['double'];p=double['coorientation'];values=p['vertex_values']
            if action=='flip':values[0][1]^=1
            elif action=='badbit':values[0][1]=2
            elif action=='bool':values[0][1]=True
            elif action=='missing':values.pop()
            elif action=='duplicate':values.append(values[0])
            elif action=='cycle':p.clear();p.update(nonzero=True,cycle_edges=[0])
            elif action=='extra':p['extra']=0
            elif action=='weight':double['histogram'][0]['weight'][1]+=1
            elif action=='count':double['histogram'][0]['orbits']+=1
            else:double['histogram'].append(deepcopy(double['histogram'][0]))
            self.assertFalse(verify_normal_topology_spectrum(raw,coords,bad),action)
        bad=deepcopy(proof);bad['schema']='normal-topology-spectrum-v1'
        self.assertFalse(verify_normal_topology_spectrum(raw,coords,bad))
        bad=deepcopy(old);bad['schema']='normal-topology-spectrum-v2'
        self.assertFalse(verify_normal_topology_spectrum(raw,coords,bad))
        alternate=deepcopy(proof)
        for row in alternate['query']['double']['coorientation']['vertex_values']:row[1]^=1
        self.assertTrue(verify_normal_topology_spectrum(raw,coords,alternate))

    def test_shared_cycle_budget_strict_options_and_cancellation(self):
        raw,coords=layered_torus(8)
        result=normal_topology_spectrum(raw,coords,record_certificate=True);used=result['stats']['orbit_cycles']
        self.assertEqual(normal_topology_spectrum(raw,coords,max_cycles=used,record_certificate=True),result)
        for options in ({},{'coorientation':False}):
            partial=normal_topology_spectrum(raw,coords,max_cycles=used-1,**options)
            self.assertEqual(partial['status'],'INCONCLUSIVE');self.assertNotIn('certificate',partial)
        self.assertEqual(normal_topology_spectrum(raw,coords,max_cycles=used,coorientation=False)['status'],'INCONCLUSIVE')
        for bad in (0,1,None,'true'):
            with self.assertRaises(ValueError):normal_topology_spectrum(raw,coords,coorientation=bad)
        for operation in (lambda c:normal_topology_spectrum(raw,coords,check=c),
                          lambda c:verify_normal_topology_spectrum(raw,coords,result['certificate'],check=c)):
            calls=[0]
            def tick():calls[0]+=1
            operation(tick);total=calls[0]
            for stop in (1,total//2,total):
                calls[0]=0
                def cancel():
                    tick()
                    if calls[0]==stop:raise ValueError('caller cancellation')
                with self.assertRaisesRegex(ValueError,'caller cancellation'):operation(cancel)


if __name__=='__main__':unittest.main()
