"""Reject the intake counterexample; count proofs and selector proofs differ."""
from copy import deepcopy
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from fastunknot.interval_orbits import IntervalPairing,count_orbits
from fastunknot.interval_orbit_verify import verify_orbit_certificate
from fastunknot.orbit_transversal import orbit_transversal,transversal_from_orbit_certificate
from fastunknot.orbit_transversal_verify import verify_orbit_transversal_certificate


class TopologyTraceContractTests(unittest.TestCase):
    def test_retained_false_transversal_is_rejected(self):
        path=Path(__file__).resolve().parents[2]/'synthesis/data/incoming-sectors-reflection-counterexample.json'
        record=json.loads(path.read_text());cert=record['incorrect_certificate']
        pairs=[IntervalPairing(0,0,1,1)]
        self.assertTrue(verify_orbit_certificate(3,pairs,cert['orbit_proof']))
        self.assertFalse(verify_orbit_transversal_certificate(3,pairs,cert))
        with self.assertRaisesRegex(ValueError,'monotone'):
            transversal_from_orbit_certificate(3,pairs,cert['orbit_proof'])
        valid=orbit_transversal(3,pairs,record_certificate=True)
        self.assertEqual(valid['representative_intervals'],[[0,1],[2,3]])
        self.assertTrue(verify_orbit_transversal_certificate(3,pairs,valid['certificate']))

    def test_reflection_pair_is_rejected_even_when_its_orbit_relation_is_unchanged(self):
        pairs=[IntervalPairing(0,1,2,3,True)]
        result=orbit_transversal(4,pairs,record_certificate=True)
        altered=deepcopy(result['certificate']);proof=altered['orbit_proof']
        proof['version']=3;proof['operations'][:0]=[{'op':'reflect'},{'op':'reflect'}]
        self.assertTrue(verify_orbit_certificate(4,pairs,proof))
        self.assertFalse(verify_orbit_transversal_certificate(4,pairs,altered))
        # A newer threshold version with the same monotone events is harmless.
        proof['operations']=proof['operations'][2:]
        self.assertTrue(verify_orbit_transversal_certificate(4,pairs,altered))

    def test_explicit_forward_discovery_and_false_valued_cancellation(self):
        from fastunknot import orbit_transversal as module
        pairs=[IntervalPairing(0,0,1,1)]
        with patch.object(module,'count_orbits',wraps=count_orbits) as wrapped:
            result=orbit_transversal(3,pairs,record_certificate=True)
        self.assertEqual(wrapped.call_args.kwargs['sweep_direction'],'forward')
        class Cancel:
            def __bool__(self):return False
            def __call__(self):raise ValueError('caller cancellation')
        for call in (lambda:orbit_transversal(3,pairs,check=Cancel()),
                     lambda:verify_orbit_transversal_certificate(3,pairs,result['certificate'],check=Cancel())):
            with self.assertRaisesRegex(ValueError,'caller cancellation'):call()

    def test_outer_surface_checker_rejects_reflected_boundary_language(self):
        from fastunknot.normal_topology import normal_topology_spectrum
        from fastunknot.normal_topology_verify import verify_normal_topology_spectrum
        from fastunknot.normal_surface_geometry import _prepare,_coordinates,_arc_system
        from normal_orbit_research.fixtures import layered_torus
        raw,coords=layered_torus(4)
        answer=normal_topology_spectrum(raw,coords,record_certificate=True)
        proof=deepcopy(answer['certificate'])
        boundary=proof['query']['boundary_transversal']['orbit_proof']
        boundary['version']=3
        boundary['operations'][:0]=[{'op':'reflect'},{'op':'reflect'}]
        prepared=_prepare(raw,lambda:None)
        core=_coordinates(prepared,proof['core_coordinates'],lambda:None)
        size,pairs=_arc_system(prepared,core,boundary=True)
        self.assertTrue(verify_orbit_certificate(size,pairs,boundary))
        self.assertFalse(verify_normal_topology_spectrum(raw,coords,proof))
