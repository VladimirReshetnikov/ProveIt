import copy
import json
import unittest
from fastunknot.cyclic_garside import compress, verify, CertificateError
from fastunknot.cyclic_garside.verify import VerificationLimit
from fastunknot.cyclic_garside.oracles import old_barrier

class VerifierTests(unittest.TestCase):
    def setUp(self):
        self.word=old_barrier(2)
        self.cert=compress(4,self.word)['certificate']

    def bad(self,cert):
        with self.assertRaises(CertificateError):
            verify(4,self.word,cert)

    def test_json_round_trip(self):
        self.assertEqual(verify(4,self.word,json.loads(json.dumps(self.cert))),(1,2,3))

    def test_corrupt_digest(self):
        c=copy.deepcopy(self.cert);c['input_digest']='0'*64;self.bad(c)

    def test_wrong_group_and_extra_fields(self):
        for field,value in [('strands',5),('strands',True),('schema','other'),('extra',1)]:
            c=copy.deepcopy(self.cert);c[field]=value;self.bad(c)

    def test_illegal_rotation(self):
        for cut in (-1,len(self.word),True):
            c=copy.deepcopy(self.cert);c['rotation']=cut;self.bad(c)
        c=copy.deepcopy(self.cert);c['mode']='linear';c['rotation']=1;self.bad(c)

    def test_corrupt_output(self):
        c=copy.deepcopy(self.cert);c['output']=[1];self.bad(c)

    def test_overlap(self):
        c=copy.deepcopy(self.cert);c['replacements']*=2;self.bad(c)

    def test_corrupt_target(self):
        c=copy.deepcopy(self.cert);c['replacements'][0]['target']=2;self.bad(c)

    def test_missing_step(self):
        c=copy.deepcopy(self.cert);c['replacements'][0]['proof'].pop();self.bad(c)

    def test_bad_transfer(self):
        c=copy.deepcopy(self.cert)
        c['replacements'][0]['proof'][0]['moves'].append([1000000,1]);self.bad(c)

    def test_bad_extraction(self):
        c=copy.deepcopy(self.cert);c['replacements'][0]['proof'][0]['delta']=1000;self.bad(c)

    def test_verification_allowance(self):
        with self.assertRaises(VerificationLimit):
            verify(4,self.word,self.cert,max_moves=0)

    def test_wrong_source(self):
        with self.assertRaises(CertificateError):
            verify(4,(1,)+self.word,self.cert)

    def test_zero_or_boolean_output_letter(self):
        for a in (0,True,4):
            c=copy.deepcopy(self.cert);c['output']=[a];self.bad(c)
