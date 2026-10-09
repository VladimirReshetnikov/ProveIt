import unittest
from signed_continuations.codec import *
from signed_continuations.core import *
from signed_continuations.verify import verify_basis

class CodecTests(unittest.TestCase):
    def test_roundtrip_huge(self):
        f=[Candidate(p,-(1<<20000)+i,str(i)) for i,p in enumerate(partitions(3))]
        cert=reduce_family(f).certificate
        rebuilt=family_from_dict(family_to_dict(f)); c=certificate_from_dict(cert.as_dict())
        self.assertEqual(f,rebuilt); self.assertEqual(c,cert)
        self.assertTrue(verify_basis(rebuilt,c))
    def test_schema_and_types(self):
        row=family_to_dict([Candidate(SignedPartition.discrete(1),0,'x')])[0]
        for edit in ({'cost_hex':'123'},{'offsets':[True]},{'extra':1}):
            with self.assertRaises((ValueError,TypeError)): family_from_dict([row|edit])
        d=BasisCertificate((0,),(1,),1,'abstract').as_dict()
        for edit in ({'selected':[True]},{'expressions_hex':['-0x1']},{'width':True}):
            with self.assertRaises((ValueError,TypeError)): certificate_from_dict(d|edit)
