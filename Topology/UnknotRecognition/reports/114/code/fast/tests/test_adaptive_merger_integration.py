"""Native scheduler contracts across weighted and normal-component consumers."""
import unittest
from unittest.mock import patch
from fastunknot.interval_orbits import count_orbits
from fastunknot.weighted_orbits import weighted_orbit_histogram
from fastunknot.weighted_orbit_verify import verify_weighted_orbit_certificate
from fastunknot.normal_surface_components import normal_component_census
from fastunknot.normal_component_verify import verify_normal_component_certificate
from fastunknot.normal_disk_kernel import normal_compressing_disk_count, verify_normal_disk_count_certificate
from normal_orbit_research.fixtures import layered_torus
from test_interval_merge_queue import five_cycle_system


def legacy(*args,**options):return count_orbits(*args,**options,merger_scheduler='legacy')


class AdaptiveMergerIntegrationTests(unittest.TestCase):
    def test_invalid_option_does_not_consume_input_and_false_callback_propagates(self):
        def pairs():raise AssertionError('input consumed');yield
        for bad in (None,[],True,{},'unknown'):
            with self.assertRaises(ValueError):count_orbits(1,pairs(),merger_scheduler=bad)
        class Cancel:
            def __bool__(self):return False
            def __call__(self):raise RuntimeError('stop scheduler')
        for scheduler in ('adaptive','queue','legacy'):
            with self.assertRaisesRegex(RuntimeError,'stop scheduler'):count_orbits(0,[],check=Cancel(),merger_scheduler=scheduler)

    def test_weighted_binary_trace_is_identical_and_replay_needs_no_scheduler(self):
        n,pairs=five_cycle_system(16,(1<<1024)+160)
        weights=[(0,n,(2,-3,1)),(3,n-5,(-1,4,7))]
        with patch('fastunknot.weighted_orbits.count_orbits',side_effect=legacy):
            old=weighted_orbit_histogram(n,pairs,weights,record_certificate=True)
        new=weighted_orbit_histogram(n,pairs,weights,record_certificate=True)
        self.assertEqual(old['certificate'],new['certificate'])
        self.assertEqual(old['histogram'],new['histogram'])
        self.assertGreater(new['stats']['orbit_stats']['merger_queue_switches'],0)
        with patch('fastunknot.interval_orbits.count_orbits',side_effect=AssertionError),patch('fastunknot.interval_merger.periodic_closure',side_effect=AssertionError),patch('fastunknot.interval_merger.hybrid_closure',side_effect=AssertionError):
            self.assertTrue(verify_weighted_orbit_certificate(n,pairs,weights,new['certificate']))

    def test_all_normal_query_modes_keep_the_same_source_bound_proof(self):
        tri,meridian=layered_torus(8);g=1<<128
        vector=[[g*x+(g+1 if j<4 else 0) for j,x in enumerate(row)] for row in meridian]
        for mode in ('disk','summary','coordinates','core'):
            fn=normal_compressing_disk_count if mode=='core' else normal_component_census
            options={} if mode=='core' else dict(mode=mode)
            with patch('fastunknot.weighted_orbits.count_orbits',side_effect=legacy):old=fn(tri,vector,record_certificate=True,**options)
            new=fn(tri,vector,record_certificate=True,**options)
            self.assertEqual(old['certificate'],new['certificate']);self.assertEqual(new['compressing_disk_components'],g)
            verify=verify_normal_disk_count_certificate if mode=='core' else verify_normal_component_certificate
            self.assertTrue(verify(tri,vector,new['certificate']))

    def test_every_cycle_allowance_preserves_completeness_and_no_partial_certificate(self):
        n,pairs=five_cycle_system(8)
        for limit in range(7):
            results=[count_orbits(n,pairs,max_cycles=limit,record_certificate=True,merger_scheduler=s) for s in ('legacy','adaptive','queue')]
            for r in results[1:]:
                self.assertEqual((r.complete,r.orbits,r.cycles,r.certificate),(results[0].complete,results[0].orbits,results[0].cycles,results[0].certificate))
            if limit<5:self.assertIsNone(results[0].certificate);self.assertIsNone(results[0].orbits)
