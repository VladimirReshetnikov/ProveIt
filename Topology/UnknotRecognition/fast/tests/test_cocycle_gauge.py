"""Exact vertex coboundaries and complete move/gauge source-chain replay."""
from contextlib import ExitStack
from copy import deepcopy
import json
from io import StringIO
import unittest
from unittest.mock import patch

from fastunknot import Diagram,recognize
from fastunknot.__main__ import main
from fastunknot.cocycle_gauge import optimize_cocycle_gauge
from fastunknot.cocycle_gauge_verify import verify_cocycle_gauge
from fastunknot.normal_transport_verify import verify_transport_disk_certificate
from fastunknot.pachner_epochs import pachner_epoch_seed_decide
from fastunknot.normal_surface_geometry import _prepare,_EDGES
from fastunknot.integer_codec import json_safe
from test_pachner_recognizer import OPTIONS


class CocycleGaugeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.diagram=Diagram.from_braid(2,[1,1,-1])
        cls.answer=pachner_epoch_seed_decide(cls.diagram,shellings=True,optimize=True,max_epochs=64,regauge_interval=4)

    def test_verified_periodic_gauge_reaches_the_disc_with_fewer_epochs(self):
        r=self.answer;self.assertEqual(r['status'],'UNKNOT')
        self.assertEqual((r['stats']['epochs'],r['stats']['remaining_tetrahedra'],r['stats']['nodes']),(24,30,83))
        self.assertEqual((r['stats']['gauge_queries'],r['stats']['gauge_changes']),(6,3))
        self.assertEqual((r['stats']['upward_moves'],r['stats']['downward_moves']),(4,28))
        self.assertEqual(r['certificate']['schema'],'diagram-transport-disc-v2')
        self.assertEqual(len(r['certificate']['steps']),35)
        self.assertTrue(verify_transport_disk_certificate(self.diagram,r['certificate']))

    def test_actual_gauge_differences_are_one_global_vertex_coboundary(self):
        proof=self.answer['certificate'];raw=proof['shelling']['triangulation'];h=proof['source_heights'];checked=0
        for step in proof['steps']:
            if 'gauge'not in step:
                raw=step['triangulation'];h=step['transport']['heights'];continue
            gauge=step['gauge'];self.assertTrue(verify_cocycle_gauge(raw,h,gauge))
            prepared=_prepare(raw,lambda:None);p=dict(gauge['potential']);after=gauge['heights']
            for t in range(len(h)):
                for a,b in _EDGES:
                    self.assertEqual((after[t][b]-after[t][a])-(h[t][b]-h[t][a]),
                        p[prepared['vertex_roots'][4*t+b]]-p[prepared['vertex_roots'][4*t+a]])
            h=after;checked+=1
        self.assertEqual(checked,3)

    def test_gauge_mutations_and_legacy_schema_downgrade_are_rejected(self):
        proof=self.answer['certificate'];index=next(i for i,s in enumerate(proof['steps'])if 'gauge'in s)
        mutations=[]
        for field,value in (('schema','wrong'),('source_sha256','0'*64),('potential',[])):
            p=deepcopy(proof);p['steps'][index]['gauge'][field]=value;mutations.append(p)
        p=deepcopy(proof);p['steps'][index]['gauge']['potential'][0][0]=True;mutations.append(p)
        p=deepcopy(proof);p['steps'][index]['gauge']['potential'][0][1]+=1;mutations.append(p)
        p=deepcopy(proof);p['steps'][index]['gauge']['heights'][0][0]+=1;mutations.append(p)
        p=deepcopy(proof);p['steps'].pop(index);mutations.append(p)
        p=deepcopy(proof);p['schema']='diagram-transport-disc-v1';mutations.append(p)
        p=deepcopy(proof);p['disc_certificate']['compressing_disk_components']=0;mutations.append(p)
        for p in mutations:self.assertFalse(verify_transport_disk_certificate(self.diagram,p))

    def test_replay_does_not_import_the_gauge_optimizer_or_move_search(self):
        disabled=('fastunknot.cocycle_gauge.optimize_cocycle_gauge','fastunknot.cocycle_span.minimize_cocycle_span',
                  'fastunknot.pachner_epochs.pachner_epoch_seed_decide','fastunknot.pachner_cover_search.find_pachner_descent',
                  'fastunknot.pachner23.pachner_23','fastunknot.pachner32.pachner_32',
                  'fastunknot.cocycle_transport.transport_cocycle')
        with ExitStack()as stack:
            for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer used during replay')))
            self.assertTrue(verify_transport_disk_certificate(self.diagram,self.answer['certificate']))
            self.assertFalse(verify_transport_disk_certificate(Diagram.from_braid(2,[1,1,1]),self.answer['certificate']))

    def test_explicit_recognizer_cli_mode_and_legacy_zero_interval(self):
        d=Diagram.from_braid(2,[1])
        a=recognize(d,**OPTIONS,use_pachner_seed=True,pachner_seed_epochs=2,pachner_seed_regauge_interval=0)
        b=recognize(d,**OPTIONS,use_pachner_seed=True,pachner_seed_epochs=2)
        self.assertEqual(a.evidence,b.evidence)
        output=StringIO();flags=['recognize','-','--pachner-seed','--pachner-seed-epochs','2',
            '--pachner-seed-regauge-interval','4','--no-reduction','--no-descending','--no-seifert',
            '--no-braid','--no-rational','--no-factor','--no-modular','--no-jones','--no-alexander','--no-r3']
        with patch('sys.stdin',StringIO(json.dumps({'braid':{'strands':2,'word':[1]}}))),patch('sys.stdout',output):
            self.assertEqual(main(flags),0)
        result=json.loads(output.getvalue());self.assertEqual(result['method'],'native-pachner-epochs')
        self.assertTrue(verify_transport_disk_certificate(d,result['evidence']['pachner_seed']['certificate']))

    def test_caps_validation_and_callback_identity(self):
        for options in ({'max_work':0},{'max_nodes':5},{'max_epochs':1}):
            r=pachner_epoch_seed_decide(self.diagram,shellings=True,optimize=True,regauge_interval=4,**options)
            self.assertEqual(r['status'],'INCONCLUSIVE');self.assertNotIn('certificate',r)
        for value in (True,-1):
            with self.assertRaises(ValueError):pachner_epoch_seed_decide(self.diagram,regauge_interval=value)
        with self.assertRaises(ValueError):recognize(self.diagram,pachner_seed_regauge_interval=4)
        error=InterruptedError('gauge interrupted')
        def stop():raise error
        with self.assertRaises(InterruptedError)as caught:verify_transport_disk_certificate(self.diagram,self.answer['certificate'],check=stop)
        self.assertIs(caught.exception,error)

    def test_large_common_potential_offset_survives_portable_integer_encoding(self):
        proof=deepcopy(self.answer['certificate'])
        for step in proof['steps']:
            if 'gauge'in step:
                for item in step['gauge']['potential']:item[1]+=1<<9000
        # A common vertex offset cancels in every normalized tetrahedron;
        # neither the edge cochain nor any actual final coordinate changes.
        self.assertTrue(verify_transport_disk_certificate(self.diagram,proof))
        portable=json.loads(json.dumps(json_safe(proof)))
        self.assertTrue(verify_transport_disk_certificate(self.diagram,portable))


if __name__=='__main__':unittest.main()
