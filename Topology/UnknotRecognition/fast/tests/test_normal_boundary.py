"""Boundary-touching component proofs, even multiplicity and independent replay."""
from copy import deepcopy
from itertools import product
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from fastunknot import normal_surface_orbits as producer
from fastunknot.normal_surface_geometry import _BOUNDARY_FIELDS, _fingerprint, _prepare, _coordinates
from fastunknot.normal_surface_orbits import normal_surface_topology
from fastunknot.normal_surface_verify import verify_normal_surface_certificate
from normal_orbit_research.fixtures import layered_torus, interior_vertex_torus

ROOT=Path(__file__).resolve().parents[1]


def combination(basis, weights):
    return [[sum(weight*surface[t][j] for weight,surface in zip(weights,basis))
             for j in range(7)] for t in range(len(basis[0]))]


def direct(raw, vector, **options):
    original=producer._classify_boundary
    def forced(*args,**kwargs):return original(*args,**kwargs,shortcuts=False)
    with patch.object(producer,'_classify_boundary',forced):
        return normal_surface_topology(raw,vector,classify_boundary=True,**options)


class NormalBoundaryTests(unittest.TestCase):
    def test_disjoint_closed_spheres_discs_and_one_sided_components(self):
        raw,basis=interior_vertex_torus()
        for a,b,c in product(range(4),repeat=3):
            vector=combination(list(basis.values()),(a,b,c))
            current=normal_surface_topology(raw,vector,classify_boundary=True,record_certificate=True)
            expected=dict(components_with_boundary=b+(c+1)//2,closed_components=a,
                orientable_components_with_boundary=b+c//2,
                nonorientable_components_with_boundary=c%2,
                closed_orientable_components=a,closed_nonorientable_components=0)
            self.assertEqual({k:current[k] for k in _BOUNDARY_FIELDS},expected,(a,b,c))
            self.assertTrue(verify_normal_surface_certificate(raw,vector,current['certificate']))
            other=direct(raw,vector,record_certificate=True)
            self.assertEqual(current['certificate']['topology'],other['certificate']['topology'])
            self.assertTrue(verify_normal_surface_certificate(raw,vector,other['certificate']))

    def test_zero_one_and_two_extra_queries_and_even_scale(self):
        raw,basis=interior_vertex_torus()
        cases=[((1,0,0),1,set()),((1,1,0),1,set()),
               ((1,2,0),1,{'surface_boundary_cone'}),
               ((1,0,1),1,{'double_boundary_cone'}),
               ((1,1,1),1,{'surface_boundary_cone','double_boundary_cone'}),
               ((1,1,1),2,{'double_boundary_cone'}),
               ((1,1,1),3,{'surface_boundary_cone','double_boundary_cone'})]
        for weights,k,extra in cases:
            vector=combination(list(basis.values()),[k*w for w in weights])
            result=normal_surface_topology(raw,vector,classify_boundary=True)
            self.assertEqual(set(result['queries'])-{'surface','double','boundary'},extra)
        simple,m=layered_torus(4)
        with patch.object(producer,'_boundary_intervals',side_effect=AssertionError):
            self.assertEqual(len(normal_surface_topology(simple,m,classify_boundary=True)['queries']),3)
        # Every edge point is marked here, even though the surface is mixed.
        simple,_=layered_torus(1)
        result=normal_surface_topology(simple,[[1,1,1,1,0,1,0]],classify_boundary=True)
        self.assertEqual(len(result['queries']),3)

    def test_even_certificate_does_not_claim_an_unknown_primitive_partition(self):
        raw,basis=interior_vertex_torus();base=combination(list(basis.values()),(1,1,1))
        results={}
        for k in (2,3,6,2**5000):
            vector=[[k*x for x in row] for row in base]
            result=normal_surface_topology(raw,vector,classify_boundary=True,record_certificate=True)
            self.assertEqual(result['closed_components'],k)
            self.assertEqual(result['orientable_components_with_boundary'],k+k//2)
            self.assertEqual(result['nonorientable_components_with_boundary'],k%2)
            encoded=json.loads(json.dumps(json_safe(result['certificate'])))
            self.assertTrue(verify_normal_surface_certificate(raw,vector,encoded))
            results[k]=(vector,result['certificate'])
        vector,odd=results[3];bad=deepcopy(odd);bad['queries']=results[2][1]['queries']
        # Same quotient Q and same valid remaining query proofs, but omission
        # of Q's touched count is insufficient for an odd original scale.
        self.assertFalse(verify_normal_surface_certificate(raw,vector,bad))
        vector,even=results[2];extra=deepcopy(even);extra['queries']=odd['queries']
        self.assertTrue(verify_normal_surface_certificate(raw,vector,extra))
        # Any valid common divisor is accepted when the matching quotient's
        # complete queries are supplied, without asking the checker to find gcd.
        vector,proof=results[6];alternate=deepcopy(proof);alternate['coordinate_divisor']=3
        quotient=[[2*x for x in row] for row in base]
        alternate['queries']=normal_surface_topology(raw,quotient,classify_boundary=True,
            record_certificate=True,reduce_multiplicity=False)['certificate']['queries']
        self.assertTrue(verify_normal_surface_certificate(raw,vector,alternate))

    def test_closed_projective_plane_and_even_orientation_cover(self):
        source=json.loads((ROOT/'normal_orbit_research/data/projective_plane_torus.json').read_text())
        raw=source['triangulation']
        for plane,disc in ((1,0),(2,0),(3,0),(1,1),(2,2),(5,3)):
            vector=combination([source['coordinates'],source['boundary_disk']],(plane,disc))
            result=normal_surface_topology(raw,vector,classify_boundary=True,record_certificate=True)
            self.assertEqual(result['closed_orientable_components'],plane//2)
            self.assertEqual(result['closed_nonorientable_components'],plane%2)
            self.assertEqual(result['orientable_components_with_boundary'],disc)
            self.assertEqual(result['nonorientable_components_with_boundary'],0)
            self.assertFalse(result['compressing_disk'])
            self.assertTrue(verify_normal_surface_certificate(raw,vector,result['certificate']))

    def test_missing_forged_or_unbound_cones_never_supply_topology(self):
        raw,basis=interior_vertex_torus();vector=combination(list(basis.values()),(1,1,1))
        proof=normal_surface_topology(raw,vector,classify_boundary=True,record_certificate=True)['certificate']
        for name in ('surface_boundary_cone','double_boundary_cone'):
            bad=deepcopy(proof);del bad['queries'][name]
            self.assertFalse(verify_normal_surface_certificate(raw,vector,bad))
            bad=deepcopy(proof);bad['queries'][name]=bad['queries']['surface']
            self.assertFalse(verify_normal_surface_certificate(raw,vector,bad))
        for key in _BOUNDARY_FIELDS:
            for value in (True,-1,1.0,proof['topology'][key]+1):
                bad=deepcopy(proof);bad['topology'][key]=value
                self.assertFalse(verify_normal_surface_certificate(raw,vector,bad),(key,value))
        for g in (0,True,1.0,2,None):
            bad=deepcopy(proof);bad['coordinate_divisor']=g
            self.assertFalse(verify_normal_surface_certificate(raw,vector,bad),g)
        for schema in ('normal-surface-topology-v1','normal-surface-topology-v2'):
            bad=deepcopy(proof);bad['schema']=schema
            self.assertFalse(verify_normal_surface_certificate(raw,vector,bad))
        other=combination(list(basis.values()),(2,1,1))
        self.assertFalse(verify_normal_surface_certificate(raw,other,proof))

    def test_shared_limits_during_extra_queries_and_replay(self):
        raw,basis=interior_vertex_torus();vector=combination(list(basis.values()),(1,1,1))
        full=normal_surface_topology(raw,vector,classify_boundary=True,record_certificate=True)
        base=sum(full['queries'][name]['cycles'] for name in ('surface','double','boundary'))
        self.assertGreater(full['cycles'],base)
        for cap in (base,full['cycles']-1):
            partial=normal_surface_topology(raw,vector,classify_boundary=True,
                                           record_certificate=True,max_cycles=cap)
            self.assertEqual(partial['status'],'INCONCLUSIVE')
            self.assertNotIn('certificate',partial);self.assertNotIn('components',partial)
            self.assertNotIn('components_with_boundary',partial)
        self.assertEqual(normal_surface_topology(raw,vector,classify_boundary=True,
            record_certificate=True,max_cycles=full['cycles']),full)
        proof=full['certificate'];events=sum(len(q['operations']) for q in proof['queries'].values())
        self.assertTrue(verify_normal_surface_certificate(raw,vector,proof,max_operations=events))
        self.assertFalse(verify_normal_surface_certificate(raw,vector,proof,max_operations=events-1))

    def test_replay_uses_no_planner_gcd_or_search_and_cancellation_propagates(self):
        raw,basis=interior_vertex_torus();vector=combination(list(basis.values()),(1,1,1))
        proof=normal_surface_topology(raw,vector,classify_boundary=True,record_certificate=True)['certificate']
        with patch.object(producer,'_classify_boundary',side_effect=AssertionError), \
             patch.object(producer,'_primitive_coordinates',side_effect=AssertionError), \
             patch.object(producer,'count_orbits',side_effect=AssertionError):
            self.assertTrue(verify_normal_surface_certificate(raw,vector,proof))
        def stop(*args,**kwargs):raise ValueError('cancel boundary geometry')
        with patch.object(producer,'_boundary_intervals',stop):
            with self.assertRaisesRegex(ValueError,'cancel boundary geometry'):
                normal_surface_topology(raw,vector,classify_boundary=True)
        with patch('fastunknot.normal_surface_verify._boundary_intervals',stop):
            with self.assertRaisesRegex(ValueError,'cancel boundary geometry'):
                verify_normal_surface_certificate(raw,vector,proof)
        with self.assertRaises(ValueError):normal_surface_topology(raw,vector,classify_boundary=1)

    def test_legacy_proof_formats_and_empty_classification(self):
        raw,base=layered_torus(1)
        for k in (1,3):
            vector=[[k*x for x in row] for row in base]
            default=normal_surface_topology(raw,vector,record_certificate=True,coorientation=False)
            self.assertEqual(default,normal_surface_topology(raw,vector,record_certificate=True,classify_boundary=False,coorientation=False))
            self.assertEqual(default['certificate']['schema'],'normal-surface-topology-v'+str(1 if k==1 else 2))
            self.assertFalse(set(_BOUNDARY_FIELDS)&set(default))
            self.assertTrue(verify_normal_surface_certificate(raw,vector,default['certificate']))
        vector=[[0]*7];r=normal_surface_topology(raw,vector,classify_boundary=True,record_certificate=True)
        self.assertTrue(all(r[k]==0 for k in _BOUNDARY_FIELDS))
        self.assertEqual(r['certificate']['coordinate_divisor'],1)
        self.assertTrue(verify_normal_surface_certificate(raw,vector,r['certificate']))


if __name__=='__main__':unittest.main()
