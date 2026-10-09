"""Native census integration: option boundaries, public claims and trace reuse."""
from copy import deepcopy
import unittest
from unittest.mock import patch
from fastunknot.normal_surface_components import normal_component_census
from fastunknot.normal_component_verify import verify_normal_component_certificate
from fastunknot.normal_disk_kernel import normal_compressing_disk_count, verify_normal_disk_count_certificate
from normal_orbit_research.fixtures import layered_torus


class IntegrationTests(unittest.TestCase):
    def test_options_rejected_before_geometry_or_trace_replay(self):
        raw,vector=layered_torus(1)
        with patch('fastunknot.normal_surface_components._prepare',side_effect=AssertionError('geometry should not run')):
            for options in ({'max_cycles':True},{'max_cycles':-1},{'periodic_rule':'unknown'},
                            {'periodic_rule':'unknown','orbit_certificate':{}},
                            {'max_cycles':0,'orbit_certificate':{}}):
                with self.assertRaises(ValueError):normal_component_census(raw,vector,**options)

    def test_all_modes_reuse_one_trace_with_producer_disabled(self):
        raw,vector=layered_torus(5)
        disk=normal_component_census(raw,vector,record_certificate=True)
        trace=disk['certificate']['weighted_orbits']['orbit_proof']
        with patch('fastunknot.weighted_orbits.count_orbits',side_effect=AssertionError('search should not run')):
            for mode in ('disk','summary','coordinates'):
                result=normal_component_census(raw,vector,mode=mode,orbit_certificate=trace,record_certificate=True)
                self.assertTrue(result['stats']['reused_orbit_certificate'])
                self.assertEqual(result['compressing_disk_components'],1)
                self.assertTrue(verify_normal_component_certificate(raw,vector,result['certificate']))
        other=[[2*x for x in row] for row in vector]
        with self.assertRaises(ValueError):normal_component_census(raw,other,orbit_certificate=trace)

    def test_core_count_has_no_total_component_claim_and_binds_original(self):
        raw,meridian=layered_torus(3);factor=1<<1024
        vector=[[factor*x+(factor+1 if i<4 else 0) for i,x in enumerate(row)] for row in meridian]
        result=normal_compressing_disk_count(raw,vector,record_certificate=True)
        self.assertEqual(result['compressing_disk_components'],factor)
        self.assertNotIn('components',result)
        self.assertTrue(verify_normal_disk_count_certificate(raw,vector,result['certificate']))
        altered=deepcopy(vector)
        for row in altered:
            for i in range(4):row[i]+=1
        self.assertFalse(verify_normal_disk_count_certificate(raw,altered,result['certificate']))
        bad=deepcopy(result['certificate']);bad['compressing_disk_components']=True
        self.assertFalse(verify_normal_disk_count_certificate(raw,vector,bad))

    def test_false_callable_cancellation_propagates_through_all_interfaces(self):
        class Cancel:
            def __bool__(self):return False
            def __call__(self):raise RuntimeError('stop requested')
        raw,vector=layered_torus(1)
        for fn in (normal_component_census,normal_compressing_disk_count):
            with self.assertRaisesRegex(RuntimeError,'stop requested'):fn(raw,vector,check=Cancel())
        for fn in (verify_normal_component_certificate,verify_normal_disk_count_certificate):
            with self.assertRaisesRegex(RuntimeError,'stop requested'):fn(raw,vector,{},check=Cancel())
