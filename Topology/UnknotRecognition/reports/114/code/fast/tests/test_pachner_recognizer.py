"""Diagram-level source binding and complete fallback after local searches."""
from io import StringIO
import json
import unittest
from unittest.mock import patch

from fastunknot import Diagram,recognize
from fastunknot.normal_pachner_search import pachner_seed_decide
from fastunknot.normal_transport_verify import verify_transport_disk_certificate
from fastunknot.__main__ import main

OPTIONS=dict(use_reduction=False,use_descending=False,use_seifert=False,
    use_braid=False,use_rational=False,use_factorization=False,use_modular=False,
    use_jones=False,use_alexander=False,use_r3=False,max_objects=20000)


class PachnerRecognizerTests(unittest.TestCase):
    def test_verified_native_positive_precedes_complete_scanning(self):
        d=Diagram.from_braid(2,[1])
        answer=recognize(d,**OPTIONS,use_pachner_seed=True,pachner_seed_max_work=None)
        self.assertEqual(answer.status,'UNKNOT');self.assertEqual(answer.method,'native-pachner-search')
        proof=answer.evidence['pachner_seed']['certificate']
        self.assertTrue(verify_transport_disk_certificate(d,proof))
        self.assertFalse(verify_transport_disk_certificate(Diagram.from_braid(2,[1,1,1]),proof))

    def test_caps_are_local_and_preserve_the_complete_fallback(self):
        for word,expected in (([1],'UNKNOT'),([1,1,1],'KNOTTED')):
            d=Diagram.from_braid(2,word)
            answer=recognize(d,**OPTIONS,use_pachner_seed=True,pachner_seed_max_work=0)
            self.assertEqual(answer.status,expected)
            self.assertEqual(answer.evidence['pachner_seed']['status'],'INCONCLUSIVE')
            self.assertNotEqual(answer.method,'native-pachner-search')
            self.assertNotIn('certificate',answer.evidence['pachner_seed'])

    def test_source_positive_avoids_building_unused_cover_index(self):
        d=Diagram.from_braid(2,[1])
        with patch('fastunknot.pachner_cover_search._build_index',side_effect=AssertionError('unused index')):
            answer=pachner_seed_decide(d,max_region_size=6,max_upward=1,max_work=None)
        self.assertEqual(answer['status'],'UNKNOT')
        self.assertEqual(answer['stats']['root_probe']['nodes'],1)
        self.assertTrue(verify_transport_disk_certificate(d,answer['certificate']))

    def test_root_probe_and_region_search_share_node_allowance(self):
        d=Diagram.from_braid(2,[1,1,1])
        with patch('fastunknot.pachner_cover_search._build_index',side_effect=AssertionError('index after node cap')):
            answer=pachner_seed_decide(d,max_region_size=6,max_upward=1,max_nodes=1,
                shellings=True,max_work=None)
        self.assertEqual(answer['status'],'INCONCLUSIVE')
        self.assertEqual(answer['bounded_search_status'],'INCONCLUSIVE')
        self.assertEqual(answer['stats']['root_probe']['nodes'],1)
        self.assertEqual(answer['stats']['search']['nodes'],0)

    def test_validation_and_disabled_default(self):
        d=Diagram.from_braid(2,[1])
        baseline=recognize(d,**OPTIONS)
        explicit=recognize(d,**OPTIONS,use_pachner_seed=False)
        self.assertEqual(baseline.status,explicit.status);self.assertEqual(baseline.evidence,explicit.evidence)
        self.assertNotIn('pachner_seed',baseline.evidence)
        for options in ({'use_pachner_seed':1},{'pachner_seed_max_upward':True},
                        {'pachner_seed_max_nodes':-1},{'pachner_seed_max_work':False}):
            with self.assertRaises(ValueError):recognize(d,**OPTIONS,**options)

    def test_cli_emits_replayable_positive_evidence(self):
        output=StringIO();data=json.dumps({'braid':{'strands':2,'word':[1]}})
        flags=['recognize','-','--pachner-seed','--no-reduction','--no-descending',
            '--no-seifert','--no-braid','--no-rational','--no-factor',
            '--no-modular','--no-jones','--no-alexander','--no-r3']
        with patch('sys.stdin',StringIO(data)),patch('sys.stdout',output):
            self.assertEqual(main(flags),0)
        answer=json.loads(output.getvalue());self.assertEqual(answer['method'],'native-pachner-search')
        self.assertTrue(verify_transport_disk_certificate(Diagram.from_braid(2,[1]),
            answer['evidence']['pachner_seed']['certificate']))


if __name__=='__main__':unittest.main()
