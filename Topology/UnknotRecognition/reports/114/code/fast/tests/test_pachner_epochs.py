"""Strict epoch progress, whole-chain authority and unchanged fallback."""
from copy import deepcopy
import json
from io import StringIO
import unittest
from unittest.mock import patch

from fastunknot import Diagram,recognize
from fastunknot.pachner_epochs import pachner_epoch_seed_decide
from fastunknot.normal_transport_verify import verify_transport_disk_certificate
from fastunknot.__main__ import main
from test_pachner_recognizer import OPTIONS


class PachnerEpochTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.diagram=Diagram.from_braid(2,[1,1,-1])
        cls.answer=pachner_epoch_seed_decide(cls.diagram,shellings=True,optimize=True,max_epochs=64)

    def test_actual_diagram_disc_after_strict_descent_epochs(self):
        answer=self.answer;self.assertEqual(answer['status'],'UNKNOT')
        self.assertEqual(answer['stats']['epochs'],33)
        self.assertEqual((answer['stats']['initial_tetrahedra'],answer['stats']['remaining_tetrahedra']),(54,21))
        self.assertEqual(answer['stats']['nodes'],191)
        self.assertEqual((answer['stats']['upward_moves'],answer['stats']['downward_moves']),(9,42))
        self.assertEqual(len(answer['certificate']['steps']),51)
        self.assertTrue(verify_transport_disk_certificate(self.diagram,answer['certificate']))
        self.assertTrue(all(r['before']>r['after']and r['upward_moves']<=1
                            for r in answer['stats']['epoch_records']))

    def test_per_epoch_budget_is_not_claimed_as_one_global_upward_budget(self):
        self.assertEqual(self.answer['scope']['max_upward_per_epoch'],1)
        self.assertGreater(self.answer['stats']['upward_moves'],1)
        self.assertLessEqual(self.answer['stats']['epochs'],self.answer['stats']['initial_tetrahedra'])

    def test_full_chain_replay_uses_no_descent_or_move_producers(self):
        disabled=('fastunknot.pachner_epochs.pachner_epoch_seed_decide',
                  'fastunknot.pachner_cover_search.find_pachner_descent',
                  'fastunknot.pachner23.pachner_23','fastunknot.pachner32.pachner_32',
                  'fastunknot.cocycle_transport.transport_cocycle','fastunknot.diagram_exterior.diagram_exterior')
        from contextlib import ExitStack
        with ExitStack()as stack:
            for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer used during replay')))
            self.assertTrue(verify_transport_disk_certificate(self.diagram,self.answer['certificate']))
            self.assertFalse(verify_transport_disk_certificate(Diagram.from_braid(2,[1,1,1]),self.answer['certificate']))
            for mutation in ('missing','reordered','height','count'):
                proof=deepcopy(self.answer['certificate'])
                if mutation=='missing':proof['steps'].pop(2)
                elif mutation=='reordered':proof['steps'][0],proof['steps'][1]=proof['steps'][1],proof['steps'][0]
                elif mutation=='height':proof['steps'][3]['transport']['heights'][0][0]+=1
                else:proof['disc_certificate']['compressing_disk_components']=0
                self.assertFalse(verify_transport_disk_certificate(self.diagram,proof))

    def test_shared_node_epoch_and_work_caps_remain_inconclusive(self):
        for options in ({'max_work':0},{'max_nodes':0},{'max_nodes':5},{'max_epochs':1}):
            answer=pachner_epoch_seed_decide(self.diagram,shellings=True,optimize=True,**options)
            self.assertEqual(answer['status'],'INCONCLUSIVE');self.assertNotIn('certificate',answer)
            if options.get('max_nodes')is not None:self.assertLessEqual(answer['stats']['nodes'],options['max_nodes'])
        self.assertEqual(pachner_epoch_seed_decide(Diagram.from_braid(2,[1,1,1]),
            shellings=True,optimize=True,max_epochs=2)['status'],'INCONCLUSIVE')

    def test_optional_recognizer_returns_new_replayed_witness_and_keeps_fallback(self):
        answer=recognize(self.diagram,**OPTIONS,use_pachner_seed=True,pachner_seed_epochs=64)
        self.assertEqual(answer.status,'UNKNOT');self.assertEqual(answer.method,'native-pachner-epochs')
        self.assertTrue(verify_transport_disk_certificate(self.diagram,answer.evidence['pachner_seed']['certificate']))
        negative=recognize(Diagram.from_braid(2,[1,1,1]),**OPTIONS,use_pachner_seed=True,
                           pachner_seed_epochs=64,pachner_seed_max_work=0)
        self.assertEqual(negative.status,'KNOTTED')
        self.assertEqual(negative.evidence['pachner_seed']['status'],'INCONCLUSIVE')

    def test_source_positive_and_unchanged_explicit_single_search(self):
        d=Diagram.from_braid(2,[1])
        positive=pachner_epoch_seed_decide(d,max_epochs=0,max_work=None)
        self.assertEqual(positive['status'],'UNKNOT');self.assertEqual(positive['stats']['epochs'],0)
        old=recognize(d,**OPTIONS,use_pachner_seed=True)
        explicit=recognize(d,**OPTIONS,use_pachner_seed=True,pachner_seed_epochs=0)
        self.assertEqual(old.status,explicit.status);self.assertEqual(old.evidence,explicit.evidence)

    def test_validation_and_caller_exception_identity(self):
        for options in ({'max_upward_per_epoch':True},{'max_epochs':-1},{'max_nodes':False},{'shellings':1}):
            with self.assertRaises(ValueError):pachner_epoch_seed_decide(self.diagram,**options)
        with self.assertRaises(ValueError):recognize(self.diagram,pachner_seed_epochs=True)
        error=InterruptedError('epoch interrupted')
        def stop():raise error
        with self.assertRaises(InterruptedError)as caught:pachner_epoch_seed_decide(self.diagram,check=stop)
        self.assertIs(caught.exception,error)

    def test_cli_explicit_epoch_mode_emits_a_replayable_witness(self):
        output=StringIO();flags=['recognize','-','--pachner-seed','--pachner-seed-epochs','2',
            '--no-reduction','--no-descending','--no-seifert','--no-braid','--no-rational',
            '--no-factor','--no-modular','--no-jones','--no-alexander','--no-r3']
        with patch('sys.stdin',StringIO(json.dumps({'braid':{'strands':2,'word':[1]}}))),patch('sys.stdout',output):
            self.assertEqual(main(flags),0)
        result=json.loads(output.getvalue());self.assertEqual(result['method'],'native-pachner-epochs')
        self.assertTrue(verify_transport_disk_certificate(Diagram.from_braid(2,[1]),
            result['evidence']['pachner_seed']['certificate']))


if __name__=='__main__':unittest.main()
