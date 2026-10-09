"""Global reflection certificates and the deliberately optional wide-end rule."""
from copy import deepcopy
from itertools import combinations_with_replacement
import json
import random
import unittest
from unittest.mock import patch

from fastunknot.integer_codec import json_safe
from fastunknot.interval_orbits import IntervalPairing, count_orbits
from fastunknot.interval_orbit_verify import verify_orbit_certificate
from fastunknot.normal_surface_orbits import normal_surface_topology
from fastunknot.normal_surface_verify import verify_normal_surface_certificate
from fastunknot.normal_surface_geometry import _prepare, _coordinates, _arc_system
from normal_orbit_research.fixtures import layered_torus
from tests.test_interval_orbits import all_pairings, explicit_components, random_pairings


class IntervalDirectionTests(unittest.TestCase):
    def test_literal_orbits_under_both_rules_and_directions(self):
        systems=[]
        for n in range(1,5):
            systems.extend((n,pairs) for pairs in combinations_with_replacement(all_pairings(n),2))
        rng=random.Random(261009517)
        systems.extend((n,random_pairings(rng,n,rng.randrange(12)))
                       for n in [rng.randrange(1,50) for _ in range(250)])
        for n,pairs in systems:
            expected=len(set(explicit_components(n,pairs)))
            for rule in ('fine_wilf','aht'):
                for direction in ('reverse','wide'):
                    result=count_orbits(n,pairs,periodic_rule=rule,sweep_direction=direction,record_certificate=True)
                    self.assertEqual(result.orbits,expected)
                    self.assertTrue(verify_orbit_certificate(n,pairs,result.certificate))

    def test_reflection_is_an_involution_and_replay_uses_no_producer(self):
        raw,coords=layered_torus(4)
        p=_prepare(raw,lambda:None);a=_coordinates(p,coords,lambda:None);n,pairs=_arc_system(p,a)
        proof=count_orbits(n,pairs,sweep_direction='reverse',record_certificate=True).certificate
        with patch('fastunknot.interval_orbits.count_orbits',side_effect=AssertionError), \
             patch('fastunknot.interval_orbits._wide_end_is_left',side_effect=AssertionError):
            self.assertTrue(verify_orbit_certificate(n,pairs,proof))
        # Two additional global reflections are a valid alternate trace.
        alternate=deepcopy(proof);alternate['operations'][:0]=[{'op':'reflect'},{'op':'reflect'}]
        self.assertTrue(verify_orbit_certificate(n,pairs,alternate))
        bad=deepcopy(proof);bad['operations'].pop(0)
        self.assertFalse(verify_orbit_certificate(n,pairs,bad))
        for version in (1,2,5,True):
            self.assertFalse(verify_orbit_certificate(n,pairs,dict(proof,version=version)))
        bad=deepcopy(proof);bad['operations'][0]['size']=n+1
        self.assertFalse(verify_orbit_certificate(n,pairs,bad))
        bad=deepcopy(proof);bad['orbit_count']+=1
        self.assertFalse(verify_orbit_certificate(n,pairs,bad))

    def test_binary_coordinates_budgets_and_cancellation(self):
        for rule,version in (('fine_wilf',3),('aht',4)):
            n=(1<<20000)+7
            pairs=[IntervalPairing(0,n-2,1,n-1)]
            result=count_orbits(n,pairs,sweep_direction='reverse',periodic_rule=rule,record_certificate=True)
            proof=json.loads(json.dumps(json_safe(result.certificate)))
            self.assertEqual(proof['version'],version)
            self.assertEqual(result.orbits,1)
            self.assertTrue(verify_orbit_certificate(n,pairs,proof))
            self.assertEqual(count_orbits(n,pairs,sweep_direction='reverse',periodic_rule=rule,
                record_certificate=True,max_cycles=result.cycles),result)
            partial=count_orbits(n,pairs,sweep_direction='reverse',max_cycles=result.cycles-1,record_certificate=True)
            self.assertFalse(partial.complete);self.assertIsNone(partial.certificate)
        n=32;pairs=[IntervalPairing(0,7,20,27),IntervalPairing(1,20,5,24,True)]
        for call in (lambda check:count_orbits(n,pairs,sweep_direction='wide',check=check),
                     lambda check:verify_orbit_certificate(n,pairs,count_orbits(n,pairs,sweep_direction='reverse',record_certificate=True).certificate,check=check)):
            ticks=[0]
            def count():ticks[0]+=1
            call(count);total=ticks[0]
            for stop in (1,total//2,total):
                ticks[0]=0
                def cancel():
                    ticks[0]+=1
                    if ticks[0]==stop:raise RuntimeError('cancelled')
                with self.assertRaisesRegex(RuntimeError,'cancelled'):call(cancel)

    def test_forward_compatibility_ties_static_gaps_and_empty(self):
        for n,pairs in ((0,[]),(10,[]),(10,[IntervalPairing(3,3,7,7)]),
                        (15,[IntervalPairing(5,9,5,9,True)])):
            original=list(pairs)
            self.assertEqual(count_orbits(n,pairs,record_certificate=True),
                             count_orbits(n,pairs,sweep_direction='wide',record_certificate=True))
            result=count_orbits(n,pairs,sweep_direction='reverse',record_certificate=True)
            self.assertEqual(result.orbits,len(set(explicit_components(n,pairs))))
            self.assertTrue(verify_orbit_certificate(n,pairs,result.certificate))
            self.assertEqual(pairs,original)
        for direction in (None,True,0,'adaptive',[],{}):
            with self.assertRaises(ValueError):count_orbits(0,[],sweep_direction=direction)

    def test_normal_queries_classification_multiplicity_and_event_caps(self):
        raw,base=layered_torus(4)
        for scale in (0,1,2,7):
            coords=[[scale*v for v in row] for row in base]
            for classify in (False,True):
                for coorientation in (False,True):
                    options=dict(record_certificate=True,classify_boundary=classify,coorientation=coorientation)
                    before=normal_surface_topology(raw,coords,**options)
                    for direction in ('reverse','wide'):
                        after=normal_surface_topology(raw,coords,sweep_direction=direction,**options)
                        self.assertEqual(before['certificate']['topology'],after['certificate']['topology'])
                        proof=after['certificate'];events=sum(len(q['operations']) for q in proof['queries'].values())
                        self.assertTrue(verify_normal_surface_certificate(raw,coords,proof,max_operations=events))
                        if events:self.assertFalse(verify_normal_surface_certificate(raw,coords,proof,max_operations=events-1))
        with self.assertRaises(ValueError):normal_surface_topology(raw,base,sweep_direction='unknown')
