"""Primitive annulus capping on an independently replayed moved source."""
from contextlib import ExitStack
from copy import deepcopy
from io import StringIO
import json
import unittest
from unittest.mock import patch

from fastunknot import Diagram,recognize
from fastunknot.__main__ import main
from fastunknot.pachner_epochs import pachner_epoch_seed_decide
from fastunknot.pachner_commitments import _State,_Names,_events,_advance
from fastunknot.cocycle_gauge import optimize_cocycle_gauge
from fastunknot.cocycle_span_verify import verify_cocycle_span
from fastunknot.normal_surface_geometry import _prepare
from fastunknot.normal_transport_verify import verify_transport_annulus_certificate,verify_transport_disk_certificate
from causal_research.native import diagram_cases
from test_pachner_recognizer import OPTIONS


class TransportAnnulusTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        source=next(s for s in diagram_cases()if s['name']=='optimized-positive')
        cls.diagram=Diagram.from_pd(source['pd'])
        cls.answer=pachner_epoch_seed_decide(cls.diagram,shellings=True,optimize=True,
            regauge_interval=4,annulus_caps=True,max_epochs=64)

    def test_actual_nonempty_diagram_caps_a_verified_initial_annulus(self):
        r=self.answer;self.assertEqual(r['status'],'UNKNOT');self.assertEqual(r['method'],'native-pachner-annulus')
        self.assertEqual(r['stats']['epochs'],0);self.assertEqual(r['stats']['annulus_queries'],1)
        self.assertEqual(r['certificate']['schema'],'diagram-transport-annulus-v1')
        self.assertTrue(verify_transport_annulus_certificate(self.diagram,r['certificate']))
        self.assertFalse(verify_transport_disk_certificate(self.diagram,r['certificate']))
        self.assertFalse(verify_transport_annulus_certificate(Diagram.from_braid(2,[1,1,1]),r['certificate']))

    def test_nonempty_geometric_and_gauge_chain_replays_the_exact_final_source(self):
        base=deepcopy(self.answer['certificate']);raw=base['surface_certificate']['triangulation'];h=base['source_heights']
        state=_State(raw,h,tuple(range(len(h))),0,0,())
        event=next(e for e in _events(state,True,lambda:None)if e.kind=='up')
        after=_advance(state,event,_Names(len(h)),lambda:None);gauged=optimize_cocycle_gauge(after.raw,after.heights)
        surface=dict(schema='diagram-cocycle-annulus-v1',input_pd=base['input_pd'],triangulation=after.raw,**gauged['span_witness'])
        proof=dict(base,steps=list(after.trace)+[dict(gauge=gauged['certificate'])],surface_certificate=surface)
        self.assertTrue(verify_transport_annulus_certificate(self.diagram,proof))
        missing=deepcopy(proof);missing['steps'].pop(0)
        self.assertFalse(verify_transport_annulus_certificate(self.diagram,missing))
        swapped=deepcopy(proof);swapped['surface_certificate']['triangulation']=raw
        self.assertFalse(verify_transport_annulus_certificate(self.diagram,swapped))

    def test_minimum_connectivity_and_primitive_source_arithmetic_are_not_assertions(self):
        proof=self.answer['certificate'];mutations=[]
        p=deepcopy(proof);p['surface_certificate']['span_certificate']=None;mutations.append(p)
        p=deepcopy(proof);p['surface_certificate']['coordinates'][0][0]+=1;mutations.append(p)
        p=deepcopy(proof);p['surface_certificate']['heights'][0][0]+=1;mutations.append(p)
        p=deepcopy(proof);p['surface_certificate']['span_certificate']['disc_count']+=1;mutations.append(p)
        p=deepcopy(proof);p['surface_certificate']['schema']='diagram-cocycle-disc-v1';mutations.append(p)
        p=deepcopy(proof);p['source_heights'][0][0]=True;mutations.append(p)
        p=deepcopy(proof);p['shelling']['moves'].append(p['shelling']['moves'][0]);mutations.append(p)
        for p in mutations:self.assertFalse(verify_transport_annulus_certificate(self.diagram,p))

    def test_independent_replay_disables_span_cochain_and_geometric_producers(self):
        disabled=('fastunknot.cocycle_span.minimize_cocycle_span','fastunknot.pachner_epochs.pachner_epoch_seed_decide',
            'fastunknot.normal_cocycle.rank_one_cocycle_seed','fastunknot.diagram_exterior.diagram_exterior',
            'fastunknot.pachner23.pachner_23','fastunknot.pachner32.pachner_32',
            'fastunknot.cocycle_transport.transport_cocycle','fastunknot.normal_disk_kernel.normal_compressing_disk_count')
        with ExitStack()as stack:
            for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer used in replay')))
            self.assertTrue(verify_transport_annulus_certificate(self.diagram,self.answer['certificate']))

    def test_explicit_recognizer_and_cli_option_require_epoch_mode(self):
        r=recognize(self.diagram,**OPTIONS,use_pachner_seed=True,pachner_seed_epochs=64,
                    pachner_seed_regauge_interval=4,pachner_seed_annulus=True)
        self.assertEqual(r.status,'UNKNOT');self.assertEqual(r.method,'native-pachner-annulus')
        self.assertTrue(verify_transport_annulus_certificate(self.diagram,r.evidence['pachner_seed']['certificate']))
        flags=['recognize','-','--pachner-seed','--pachner-seed-epochs','64','--pachner-seed-regauge-interval','4',
            '--pachner-seed-annulus','--no-reduction','--no-descending','--no-seifert','--no-braid','--no-rational',
            '--no-factor','--no-modular','--no-jones','--no-alexander','--no-r3']
        output=StringIO()
        with patch('sys.stdin',StringIO(json.dumps({'pd':self.diagram.pd}))),patch('sys.stdout',output):
            self.assertEqual(main(flags),0)
        parsed=json.loads(output.getvalue());self.assertEqual(parsed['method'],'native-pachner-annulus')
        with self.assertRaises(ValueError):recognize(self.diagram,pachner_seed_annulus=True)
        with self.assertRaises(ValueError):pachner_epoch_seed_decide(self.diagram,annulus_caps=1)

    def test_zero_work_is_not_a_cap_certificate_and_complete_fallback_remains(self):
        for d,expected in ((self.diagram,'UNKNOT'),(Diagram.from_braid(2,[1,1,1]),'KNOTTED')):
            r=recognize(d,**OPTIONS,use_pachner_seed=True,pachner_seed_epochs=64,
                pachner_seed_annulus=True,pachner_seed_max_work=0)
            self.assertEqual(r.status,expected);self.assertEqual(r.evidence['pachner_seed']['status'],'INCONCLUSIVE')
            self.assertNotIn('certificate',r.evidence['pachner_seed'])

    def test_callback_exception_identity_and_legacy_coherent_mode(self):
        error=InterruptedError('annulus interrupted')
        def stop():raise error
        with self.assertRaises(InterruptedError)as caught:verify_transport_annulus_certificate(self.diagram,self.answer['certificate'],check=stop)
        self.assertIs(caught.exception,error)
        d=Diagram.from_braid(2,[1])
        a=pachner_epoch_seed_decide(d,max_epochs=0,max_work=None)
        b=pachner_epoch_seed_decide(d,max_epochs=0,max_work=None,annulus_caps=False)
        self.assertEqual(a,b)

    def test_valid_nonprimitive_minimum_span_is_not_an_annulus_cap_witness(self):
        proof=deepcopy(self.answer['certificate']);surface=proof['surface_certificate'];span=surface['span_certificate']
        surface['heights']=[[2*x for x in row]for row in surface['heights']]
        surface['coordinates']=[[2*x for x in row]for row in surface['coordinates']]
        span['potential']=[2*x for x in span['potential']]
        span['coordinates']=[[2*x for x in row]for row in span['coordinates']]
        span['disc_count']*=2
        p=_prepare(surface['triangulation'],lambda:None)
        vertices=[p['vertex_roots'][4*t:4*t+4]for t in range(len(p['tetrahedra']))]
        self.assertTrue(verify_cocycle_span(vertices,surface['heights'],span))
        self.assertFalse(verify_transport_annulus_certificate(self.diagram,proof))


if __name__=='__main__':unittest.main()
