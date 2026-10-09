import json
from pathlib import Path
import random
import subprocess
import sys
import unittest
from unittest.mock import patch

from fastunknot import Diagram, khovanov_rank, recognize
from fastunknot.geometry import ScanLimit
from fastunknot.minimal_window import erase_above, khovanov_minimal_window_auto
from fastunknot.nice_order import certify, nice_order, OrderError
from fastunknot.scan_fast import FastScan
from fastunknot.window_scan import khovanov_window

ROOT=Path(__file__).resolve().parents[1]


class MinimalWindowTests(unittest.TestCase):
    def test_truncating_before_cancellation_invents_guard_object(self):
        def disk():
            scan=FastScan();scan.mid=[0,0];scan.deg=[1,2]
            scan.out=[{1:1},{}];scan.inc=[set(),{0}];scan.live=2
            return scan
        before=disk();erase_above(before,1);before.eliminate()
        after=disk();after.eliminate();erase_above(after,1)
        self.assertEqual(before.live,1)
        self.assertEqual(after.live,0)

    def test_certificates_and_invalid_orders(self):
        d=Diagram.from_braid(3,[1,2]*4)
        cert=nice_order(d.pd)
        self.assertTrue(cert.nice)
        self.assertEqual(cert,certify(d.pd,cert.order))
        self.assertEqual(cert.attachments[-1],4)
        for order in ([0]*8,[True]+list(range(1,8))):
            with self.assertRaises(ValueError):certify(d.pd,order)
        self.assertFalse(certify(Diagram.from_braid(2,[1]).pd,[0]).nice)
        with self.assertRaises(ScanLimit):
            nice_order(d.pd,check=lambda: (_ for _ in ()).throw(ScanLimit('stop')))

    def test_random_intervals_reducers_and_binomial_profiles(self):
        rng=random.Random(2026100812);accepted=0;certified=0
        while accepted<100:
            strands=rng.randrange(2,6)
            word=[rng.choice((-1,1))*rng.randrange(1,strands) for _ in range(rng.randrange(1,13))]
            try:d=Diagram.from_braid(strands,word)
            except ValueError:continue
            full=khovanov_rank(d.pd)['by_degree']
            lower=rng.randrange(-1,len(word)+2);upper=lower+rng.randrange(4)
            expected={h:c for h,c in full.items() if lower<=h<=upper}
            for mode in ('standard','residue','adaptive'):
                r=khovanov_minimal_window_auto(d,lower,upper,reduction=mode,
                     composition='component-dense' if accepted<15 else 'standard',
                     check_d_squared=True,trace=True)
                self.assertEqual(r['by_degree'],expected)
                self.assertEqual(r['binomial_bound_certified'],r['nice_order']['nice'])
                if r['binomial_bound_certified']:certified+=1
                self.assertEqual(r['stats']['binomial_stages_checked'],len(word) if r['nice_order']['nice'] else 0)
            accepted+=1
        self.assertGreater(certified,0)

    def test_raw_profiles_and_padding_shift(self):
        for padding in range(5):
            d=Diagram.from_braid(2,[1,-1]*padding+[1]*3)
            allh=khovanov_rank(d.pd)['by_degree']
            result=khovanov_minimal_window_auto(d,0,d.crossings,trace=True)
            self.assertEqual(result['by_degree'],allh)
            self.assertTrue(result['complete_rank'])
            if padding:
                self.assertEqual(khovanov_minimal_window_auto(d,0,padding-1,mirror=False)['by_degree'],{})
        d=Diagram.from_braid(3,[1,-2]*5)
        order=list(nice_order(d.pd).order)
        profiles=[]
        for mode in ('standard','residue','adaptive'):
            profiles.append(khovanov_minimal_window_auto(d,0,2,order=order,mirror=False,
                             trace=True,reduction=mode)['stages'])
        self.assertEqual(profiles[0],profiles[1]);self.assertEqual(profiles[0],profiles[2])

    def test_limits_and_pipeline_contract(self):
        d=Diagram.from_braid(2,[1]*3)
        for opts in (dict(seconds=0),dict(max_objects=0)):
            with self.assertRaises(ScanLimit):khovanov_minimal_window_auto(d,0,0,**opts)
        for opts in (dict(seconds=float('nan')),dict(reduction='wrong'),dict(composition_max_variables=-1)):
            with self.assertRaises(ValueError):khovanov_minimal_window_auto(d,0,0,**opts)
        opts=dict(use_braid=False,use_seifert=False,use_reduction=False,use_descending=False,
                  use_alexander=False,use_jones=False,use_factorization=False,
                  window_strategy='minimal',window_seconds=1)
        self.assertEqual(recognize(d,window_radius=0,**opts).method,'reduced-khovanov-F2-scan')
        r=recognize(d,window_radius=3,**opts)
        self.assertEqual(r.status,'KNOTTED')
        self.assertEqual(r.method,'khovanov-window-obstruction')
        self.assertEqual(r.evidence['khovanov_windows']['strategy'],'minimal')
        cmd=[sys.executable,'-B','-m','fastunknot','window','-','--minimal','--normalized','--auto-mirror']
        p=subprocess.run(cmd,input=json.dumps(dict(braid=dict(strands=2,word=[1]*3))),text=True,capture_output=True)
        self.assertEqual(p.returncode,0,p.stderr)
        self.assertEqual(json.loads(p.stdout)['normalized_by_degree'],{'0':2})
