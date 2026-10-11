"""Compressed cut connectivity, source binding and independent replay."""
from contextlib import ExitStack
from copy import deepcopy
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from fastunknot.normal_cut_complement import normal_complement_components,_chamber_system
from fastunknot.normal_cut_complement_verify import verify_normal_complement_certificate,_reference_chambers
from fastunknot.normal_surface_geometry import _prepare,_coordinates,NormalOrbitError
from normal_orbit_research.fixtures import layered_torus

ROOT=Path(__file__).resolve().parents[2]

class CutComplementTests(unittest.TestCase):
    def test_parallel_disc_vertex_link_and_one_sided_families(self):
        raw,meridian=layered_torus(1)
        families=[(meridian,lambda n:n),([[1,1,1,1,0,0,0]],lambda n:n+1),
            ([[0,0,0,0,0,1,0]],lambda n:n//2+1)]
        for vector,expected in families:
            for scale in range(1,7):
                rows=[[scale*x for x in row]for row in vector]
                result=normal_complement_components(raw,rows,record_certificate=True)
                self.assertEqual(result['cut_components'],expected(scale))
                self.assertTrue(verify_normal_complement_certificate(raw,rows,result['certificate']))
        empty=[[0]*7]
        self.assertEqual(normal_complement_components(raw,empty)['cut_components'],1)

    def test_saved_actual_geometry_cases_and_pairing_size(self):
        bank={r['id']:r['triangulation']for r in json.loads((ROOT/'reports/57/results/discovery_corpus.json').read_text())['records']}
        pilot=json.loads((ROOT/'synthesis/data/complement-chamber-pilot.json').read_text())
        groups={}
        for record in pilot['records']:groups.setdefault(record['id'],[]).append(record)
        self.assertEqual(len(groups),48)
        for name,cases in groups.items():
            for case in (cases[0],cases[-1]):
                raw=bank[name];rows=case['coordinates'];prepared=_prepare(raw,lambda:None)
                n,pairs=_chamber_system(prepared,rows,lambda:None)
                reference_size,reference_rows=_reference_chambers(prepared,rows,lambda:None)
                self.assertEqual(n,reference_size)
                self.assertEqual(reference_rows,[[p.a,p.b,p.c,p.d,-1 if p.reverse else 1]for p in pairs])
                self.assertEqual(n,len(rows)+sum(sum(row)for row in rows))
                self.assertLessEqual(len(pairs),20*len(rows))
                result=normal_complement_components(raw,rows,record_certificate=True)
                self.assertEqual(result['cut_components'],case['components'])
                self.assertTrue(verify_normal_complement_certificate(raw,rows,result['certificate']))

    def test_mixed_vertex_links_and_quadrilateral_sheets(self):
        raw,_=layered_torus(1)
        for links in range(4):
            for mobius in range(7):
                rows=[[links]*4+[0,mobius,0]]
                result=normal_complement_components(raw,rows,record_certificate=True)
                self.assertEqual(result['cut_components'],links+mobius//2+1)
                self.assertTrue(verify_normal_complement_certificate(raw,rows,result['certificate']))

    def test_large_binary_multiplicity_is_not_divided_out(self):
        raw,meridian=layered_torus(1);n=1<<16384
        rows=[[n*x for x in row]for row in meridian]
        result=normal_complement_components(raw,rows,record_certificate=True)
        self.assertEqual(result['cut_components'],n)
        self.assertEqual(result['cycles'],4)
        wire=json.loads(json.dumps(json_safe(result['certificate'])))
        coordinates=json.loads(json.dumps(json_safe(rows)))
        self.assertTrue(verify_normal_complement_certificate(raw,coordinates,wire))
        wrong=deepcopy(wire);wrong['cut_components']=1
        self.assertFalse(verify_normal_complement_certificate(raw,coordinates,wrong))

    def test_checker_uses_no_chamber_or_orbit_producer(self):
        raw,rows=layered_torus(5)
        result=normal_complement_components(raw,rows,record_certificate=True)
        disabled=('fastunknot.normal_cut_complement.normal_complement_components',
            'fastunknot.normal_cut_complement._chamber_system','fastunknot.interval_orbits.count_orbits')
        with ExitStack()as stack:
            for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer used')))
            self.assertTrue(verify_normal_complement_certificate(raw,rows,result['certificate']))

    def test_schema_source_count_and_trace_mutations_rejected(self):
        raw,rows=layered_torus(2);proof=normal_complement_components(raw,rows,record_certificate=True)['certificate']
        for key,value in (('schema','normal-surface-topology-v1'),('input_sha256','0'*64),
                          ('cut_components',True),('cut_components','1'),('cut_components',0),
                          ('cut_components',100),('orbit_certificate',None)):
            wrong=deepcopy(proof);wrong[key]=value
            self.assertFalse(verify_normal_complement_certificate(raw,rows,wrong))
        wrong=deepcopy(proof);wrong['extra']=1
        self.assertFalse(verify_normal_complement_certificate(raw,rows,wrong))
        wrong=deepcopy(proof);wrong['orbit_certificate']['pairings'][0][0]+=1
        self.assertFalse(verify_normal_complement_certificate(raw,rows,wrong))
        other,vector=layered_torus(3)
        self.assertFalse(verify_normal_complement_certificate(other,vector,proof))
        changed=[[2*x for x in row]for row in rows]
        self.assertFalse(verify_normal_complement_certificate(raw,changed,proof))

    def test_caps_and_malformed_geometry_are_not_conclusions(self):
        raw,rows=layered_torus(3)
        capped=normal_complement_components(raw,rows,max_cycles=0,record_certificate=True)
        self.assertEqual(capped['status'],'INCONCLUSIVE')
        self.assertNotIn('cut_components',capped);self.assertNotIn('certificate',capped)
        proof=normal_complement_components(raw,rows,record_certificate=True)['certificate']
        self.assertFalse(verify_normal_complement_certificate(raw,rows,proof,max_operations=0))
        with self.assertRaises(ValueError):normal_complement_components(raw,rows,max_cycles=True)
        with self.assertRaises(ValueError):verify_normal_complement_certificate(raw,rows,proof,max_operations=True)
        bad=deepcopy(rows);bad[0]=[False]*7
        with self.assertRaises(NormalOrbitError):normal_complement_components(raw,bad)
        with self.assertRaises(NormalOrbitError):verify_normal_complement_certificate(raw,bad,proof)

    def test_false_valued_callback_exceptions_propagate(self):
        raw,rows=layered_torus(1)
        proof=normal_complement_components(raw,rows,record_certificate=True)['certificate']
        class Cancel:
            def __bool__(self):return False
            def __call__(self):raise ValueError('external cancellation')
        with self.assertRaisesRegex(ValueError,'external cancellation'):
            normal_complement_components(raw,rows,check=Cancel())
        with self.assertRaisesRegex(ValueError,'external cancellation'):
            verify_normal_complement_certificate(raw,rows,proof,check=Cancel())

if __name__=='__main__':unittest.main()
