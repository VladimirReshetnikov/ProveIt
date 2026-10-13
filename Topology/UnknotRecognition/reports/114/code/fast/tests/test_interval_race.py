"""Restart accounting, real checkpoint bounds, and independently replayed winners."""
import random
import unittest
from unittest.mock import patch

from fastunknot.interval_orbits import IntervalPairing, OrbitResult, count_orbits
from fastunknot.interval_orbit_verify import verify_orbit_certificate
from fastunknot.normal_surface_orbits import normal_surface_topology
from fastunknot.normal_surface_verify import verify_normal_surface_certificate
from normal_orbit_research.fixtures import layered_torus
from tests.test_interval_orbits import explicit_components, random_pairings


def measured(n,pairs,direction,**options):
    work=[0]
    def tick():work[0]+=1
    result=count_orbits(n,pairs,sweep_direction=direction,check=tick,**options)
    return result,work[0]


def switch_fixture():
    rng=random.Random(261009521)
    for _ in range(7):
        n=rng.randrange(20,120)
        pairs=[IntervalPairing(a,a,b,b) for a,b in
               ((rng.randrange(n),rng.randrange(n)) for _ in range(rng.randrange(n,3*n)))]
    return n,pairs


class IntervalRaceTests(unittest.TestCase):
    def test_real_graph_switch_discards_five_incomplete_traces(self):
        n,pairs=switch_fixture()
        result=count_orbits(n,pairs,sweep_direction='race',record_certificate=True)
        self.assertEqual((n,len(pairs)),(72,195))
        self.assertEqual(result.orbits,len(set(explicit_components(n,pairs))))
        self.assertEqual(result.stats['race_attempts'],6)
        self.assertEqual(result.stats['race_winning_direction'],1)
        self.assertEqual(result.stats['race_winning_work'],50174)
        self.assertEqual(result.stats['race_final_allowance'],50176)
        self.assertEqual(result.certificate,count_orbits(n,pairs,sweep_direction='reverse',record_certificate=True).certificate)
        self.assertTrue(verify_orbit_certificate(n,pairs,result.certificate))

    def test_literal_results_bound_and_exact_winning_proof(self):
        rng=random.Random(261009520)
        cases=[(0,[]),(10,[])]
        cases += [(n,[IntervalPairing(0,0,i,i) for i in range(1,n)]) for n in (16,32,64)]
        cases += [(n,random_pairings(rng,n,rng.randrange(20))) for n in [rng.randrange(1,65) for _ in range(200)]]
        restarted=False
        for n,pairs in cases:
            literal=len(set(explicit_components(n,pairs)))
            for rule in ('aht','fine_wilf'):
                fixed=[measured(n,pairs,d,periodic_rule=rule,record_certificate=True) for d in ('forward','reverse')]
                answer,actual_work=measured(n,pairs,'race',periodic_rule=rule,record_certificate=True)
                s=answer.stats;winner=s['race_winning_direction'];initial=s['race_initial_allowance']
                optimum=min(w for _,w in fixed);budget=initial;rounds=0
                while budget<optimum:budget*=2;rounds+=1
                self.assertEqual(s['race_final_allowance'],budget)
                self.assertLessEqual(s['race_checkpoint_work'],4*budget-2*initial+2*rounds+1)
                self.assertLessEqual(s['race_checkpoint_work'],12*max(initial,optimum))
                self.assertEqual(s['race_checkpoint_work']+s['race_startup_work'],actual_work)
                self.assertEqual(s['race_forward_cycles']+s['race_reverse_cycles'],answer.cycles)
                self.assertEqual(s['race_forward_work']+s['race_reverse_work'],s['race_checkpoint_work'])
                self.assertEqual(s['race_restarts'],s['race_attempts']-1)
                self.assertEqual(answer.orbits,literal)
                self.assertEqual(answer.certificate,fixed[winner][0].certificate)
                self.assertEqual(s['race_winning_work'],fixed[winner][1])
                self.assertTrue(verify_orbit_certificate(n,pairs,answer.certificate))
                restarted |= s['race_restarts']>0
        self.assertTrue(restarted)

    def test_second_direction_can_win_without_false_partial_proof(self):
        # Isolate the scheduling rule with deterministic checkpoint streams.
        # Real AHT and literal-orbit correctness are tested independently above.
        def engine(n,pairs,*,check,_cycle_started,sweep_direction,**options):
            _cycle_started({'initial_pairings':0,'input_bits':n.bit_length()})
            for _ in range(100 if sweep_direction=='forward' else 3):check()
            return OrbitResult(True,0,1,{},None)
        with patch('fastunknot.interval_race._count_orbits',side_effect=engine):
            result=count_orbits(0,[],sweep_direction='race')
        self.assertEqual(result.stats['race_winning_direction'],1)
        self.assertEqual(result.stats['race_attempts'],2)
        self.assertEqual(result.stats['race_checkpoint_work'],12)
        self.assertEqual(result.cycles,2)

    def test_shared_cycle_caps_include_abandoned_attempts(self):
        n=32;pairs=[IntervalPairing(0,0,i,i) for i in range(1,n)]
        full=count_orbits(n,pairs,sweep_direction='race',record_certificate=True)
        self.assertGreater(full.cycles,full.stats['race_winning_cycles'])
        self.assertEqual(count_orbits(n,pairs,sweep_direction='race',record_certificate=True,max_cycles=full.cycles),full)
        for cap in (0,1,10,full.cycles-1):
            partial=count_orbits(n,pairs,sweep_direction='race',record_certificate=True,max_cycles=cap)
            self.assertFalse(partial.complete);self.assertIsNone(partial.orbits);self.assertIsNone(partial.certificate)
            self.assertEqual(partial.cycles,cap)
        self.assertTrue(count_orbits(0,[],sweep_direction='race',max_cycles=0).complete)

    def test_cancellation_binary_input_and_all_merger_schedulers(self):
        n=(1<<20000)+7;pairs=[IntervalPairing(0,n-2,1,n-1)]
        for merger in ('adaptive','legacy','queue'):
            result=count_orbits(n,pairs,sweep_direction='race',record_certificate=True,merger_scheduler=merger)
            self.assertEqual(result.orbits,1)
            self.assertTrue(verify_orbit_certificate(n,pairs,result.certificate))
        n=32;pairs=[IntervalPairing(0,0,i,i) for i in range(1,n)]
        _,total=measured(n,pairs,'race')
        for stop in (1,33,total//2,total):
            calls=[0]
            def cancel():
                calls[0]+=1
                if calls[0]==stop:raise RuntimeError('caller cancellation')
            with self.assertRaisesRegex(RuntimeError,'caller cancellation'):
                count_orbits(n,pairs,sweep_direction='race',check=cancel)
        for options in ({'max_cycles':True},{'record_certificate':1},{'merger_scheduler':None},{'periodic_rule':'bad'}):
            with self.assertRaises(ValueError):count_orbits(0,[],sweep_direction='race',**options)

    def test_normal_composition_and_producer_free_replay(self):
        raw,coords=layered_torus(8)
        for classify in (False,True):
            for coorientation in (False,True):
                options=dict(record_certificate=True,classify_boundary=classify,coorientation=coorientation)
                old=normal_surface_topology(raw,coords,**options)
                new=normal_surface_topology(raw,coords,sweep_direction='race',**options)
                self.assertEqual(old['certificate']['topology'],new['certificate']['topology'])
                with patch('fastunknot.interval_race.race_orbits',side_effect=AssertionError), \
                     patch('fastunknot.interval_orbits._count_orbits',side_effect=AssertionError):
                    self.assertTrue(verify_normal_surface_certificate(raw,coords,new['certificate']))
                self.assertEqual(normal_surface_topology(raw,coords,sweep_direction='race',max_cycles=new['cycles'],**options),new)
                partial=normal_surface_topology(raw,coords,sweep_direction='race',max_cycles=new['cycles']-1,**options)
                self.assertEqual(partial['status'],'INCONCLUSIVE');self.assertNotIn('certificate',partial)
