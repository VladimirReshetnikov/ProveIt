"""Inside-core prism face regions, ports and independently replayed profiles."""
from contextlib import ExitStack
from copy import deepcopy
import json
import unittest
from unittest.mock import patch
from fastunknot.integer_codec import json_safe
from fastunknot.normal_prism_interfaces import normal_prism_face_regions
from fastunknot.normal_prism_interfaces_verify import verify_normal_prism_interfaces
from fastunknot.normal_cut_complement import normal_complement_components
from normal_orbit_research.fixtures import layered_torus

class PrismInterfaceTests(unittest.TestCase):
    def test_attached_regions_inside_a_single_primitive_cut_core(self):
        expected={2:(2,2),4:(3,6),8:(3,14),16:(3,30)}
        for t,(regions,ports)in expected.items():
            raw,v=layered_torus(t);cut=normal_complement_components(raw,v,classify_prisms=True)
            self.assertEqual((cut['core_components'],cut['prismatic_components']),(1,0))
            r=normal_prism_face_regions(raw,v,record_certificate=True);s=r['structure']
            self.assertEqual((s['face_attached_components'],len(s['ports'])),(regions,ports))
            self.assertEqual(s['unattached_components'],0)
            self.assertTrue(verify_normal_prism_interfaces(raw,v,r['certificate']))
            self.assertEqual(sorted(p for row in s['attached_regions']for p in row['ports']),list(range(ports)))

    def test_parallel_families_preserve_whole_piece_count(self):
        for t in (1,2,4):
            raw,v=layered_torus(t)
            for n in (1,2,5,64):
                rows=[[n*x for x in row]for row in v]
                old=normal_complement_components(raw,rows,classify_prisms=True)
                r=normal_prism_face_regions(raw,rows,record_certificate=True);s=r['structure']
                self.assertEqual(s['unattached_components'],old['prismatic_components'])
                self.assertLessEqual(len(s['core_cells']),6*t);self.assertLessEqual(len(s['ports']),24*t)
                self.assertTrue(all(p['corner']>=0 and p['rank']>0 for p in s['ports']))
                self.assertTrue(verify_normal_prism_interfaces(raw,rows,r['certificate']))

    def test_empty_prism_graph_has_complete_empty_profiles(self):
        raw,v=layered_torus(1)
        for rows in ([[0]*7],v):
            r=normal_prism_face_regions(raw,rows,record_certificate=True)
            self.assertEqual(r['structure']['prism_points'],0)
            self.assertEqual(r['structure']['attached_regions'],[])
            self.assertEqual(r['structure']['unattached_profiles'],[])
            self.assertTrue(verify_normal_prism_interfaces(raw,rows,r['certificate']))

    def test_ribbon_euler_counts_bands_including_self_pairings(self):
        raw,_=layered_torus(1)
        for n in (2,3,4,5):
            rows=[[0,0,0,0,0,n,0]]
            r=normal_prism_face_regions(raw,rows,record_certificate=True)
            for p in r['structure']['attached_regions']+r['structure']['unattached_profiles']:
                self.assertEqual(p['ribbon_euler_characteristic'],p['prism_cells']-p['face_bands'])
            self.assertTrue(verify_normal_prism_interfaces(raw,rows,r['certificate']))

    def test_large_binary_ports_and_profiles_replay_without_producers(self):
        raw,v=layered_torus(4);n=1<<16384;rows=[[n*x for x in row]for row in v]
        r=normal_prism_face_regions(raw,rows,record_certificate=True)
        self.assertEqual(r['structure']['unattached_components'],n-1)
        wire=json.loads(json.dumps(json_safe(r['certificate'])))
        disabled=('fastunknot.normal_prism_interfaces._interface_system','fastunknot.normal_prism_interfaces._profiles',
            'fastunknot.normal_prism_interfaces.normal_prism_face_regions','fastunknot.weighted_orbits.weighted_orbit_histogram',
            'fastunknot.interval_orbits.count_orbits')
        with ExitStack()as stack:
            for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer')))
            self.assertTrue(verify_normal_prism_interfaces(raw,rows,wire))

    def test_source_ports_partitions_weights_and_ribbon_claims_mutated(self):
        raw,v=layered_torus(4);proof=normal_prism_face_regions(raw,v,record_certificate=True)['certificate'];mutations=[]
        for key,value in (('schema','normal-cut-components-v2'),('input_sha256','0'*64),('weighted_certificate',None)):
            p=deepcopy(proof);p[key]=value;mutations.append(p)
        for key in ('rank','source_face','core_cell','prism_point'):
            p=deepcopy(proof);p['structure']['ports'][0][key]+=1;mutations.append(p)
        p=deepcopy(proof);p['structure']['attached_regions'][0]['ports'].pop();mutations.append(p)
        p=deepcopy(proof);p['structure']['attached_regions'][0]['ribbon_euler_characteristic']+=1;mutations.append(p)
        p=deepcopy(proof);p['structure']['core_cells'][0]['chamber']+=1;mutations.append(p)
        p=deepcopy(proof);p['weighted_certificate']['weights'][0][2][0]+=1;mutations.append(p)
        p=deepcopy(proof);p['structure']['prism_points']=True;mutations.append(p)
        for p in mutations:self.assertFalse(verify_normal_prism_interfaces(raw,v,p))
        other,vec=layered_torus(5)
        self.assertFalse(verify_normal_prism_interfaces(other,vec,proof))

    def test_caps_and_cancellation_are_not_structures(self):
        raw,v=layered_torus(4);r=normal_prism_face_regions(raw,v,max_cycles=0,record_certificate=True)
        self.assertEqual(r['status'],'INCONCLUSIVE');self.assertNotIn('structure',r);self.assertNotIn('certificate',r)
        proof=normal_prism_face_regions(raw,v,record_certificate=True)['certificate']
        self.assertFalse(verify_normal_prism_interfaces(raw,v,proof,max_operations=0))
        with self.assertRaises(ValueError):normal_prism_face_regions(raw,v,max_cycles=True)
        def stop():raise ValueError('external cancellation')
        with self.assertRaisesRegex(ValueError,'external cancellation'):normal_prism_face_regions(raw,v,check=stop)
        with self.assertRaisesRegex(ValueError,'external cancellation'):verify_normal_prism_interfaces(raw,v,proof,check=stop)

if __name__=='__main__':unittest.main()
