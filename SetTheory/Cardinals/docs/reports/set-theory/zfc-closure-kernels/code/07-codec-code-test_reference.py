from __future__ import annotations
import json
import unittest
from syntax import *
from checker import check, InvalidCertificate, encode_bytes, decode_bytes, search

def identity(p: Formula) -> list:
    # The ordinary five-line K/S derivation, with zero-based references.
    return [['K',p,I(p,p)],['K',p,p],['S',p,I(p,p),p],['MP',0,2],['MP',1,3]]

class ReferenceTests(unittest.TestCase):
    def test_identity(self):
        out=check(json.loads(json.dumps(identity(E(0,0)))))
        self.assertTrue(out['valid']); self.assertFalse(out['refutation'])
        self.assertEqual(out['conclusion'],I(E(0,0),E(0,0)))
    def test_bottom_identity_not_refutation(self):
        out=check(json.loads(json.dumps(identity(B))))
        self.assertEqual(out['conclusion'],I(B,B)); self.assertFalse(out['refutation'])
    def test_top(self): self.assertEqual(check([['TOP']])['conclusion'],T)
    def test_exfalso_not_refutation(self):
        out=check([['EFQ',['E',0,0]]]); self.assertFalse(out['refutation'])
    def test_theory_axioms_closed(self):
        for r in ([['EC']],[['PSC',['E',0,2]]],[['PSC',['A',0,['E',0,1]]]]):
            self.assertEqual(free(check(r)['conclusion']),set())
    def test_quantifier(self):
        out=check([['UI',0,1,['A',1,['E',0,1]]]])
        consequent=out['conclusion'][2]
        self.assertEqual(free(consequent),{1})
        self.assertEqual(alpha_key(consequent),alpha_key(A(9,E(1,9))))
    def test_q_side_condition(self):
        with self.assertRaises(InvalidCertificate): check([['Q',0,['E',0,0],['B']]])
    def test_q_valid(self): self.assertTrue(check([['Q',0,['E',1,1],['E',0,1]]])['valid'])
    def test_generalization_alpha(self):
        cert=json.loads(json.dumps(identity(E(0,0))))
        cert += [['GEN',0,4],['ALPHA',5,['A',7,['I',['E',7,7],['E',7,7]]]]]
        self.assertTrue(check(cert)['valid'])
    def test_alpha_rejects_capture(self):
        with self.assertRaises(InvalidCertificate):
            check([['TOP'],['GEN',0,0],['ALPHA',1,['A',0,['E',0,0]]]])
    def test_forward_reference(self):
        with self.assertRaises(InvalidCertificate): check([['GEN',0,0]])
    def test_mp_mismatch(self):
        with self.assertRaises(InvalidCertificate): check([['TOP'],['EFQ',['T']],['MP',0,1]])
    def test_no_admission(self):
        for tag in ('AXIOM','ASSUME','ADMIT','EQ'):
            with self.assertRaises(InvalidCertificate): check([[tag,['B']]])
    def test_malformed_formula(self):
        for f in (['E',True,0],['E',-1,0],['eq',0,0],['H',0,1],['I',['B']],['B',0]):
            with self.assertRaises(InvalidCertificate): check([['EFQ',f]])
    def test_malformed_certificate(self):
        for c in ([],{},None,[[]],[['TOP',0]],[['MP',False,0]]):
            with self.assertRaises(ValueError): check(c)
    def test_byte_enumeration_roundtrip(self):
        c=json.loads(json.dumps(identity(E(0,0))))
        self.assertEqual(decode_bytes(encode_bytes(c)),c)
    def test_bounded_enumeration_no_false_halt(self): self.assertIsNone(search(1,1000))
    def test_raw_codec_targets(self):
        self.assertEqual(decode(0),T); self.assertEqual(decode(1),B)
        self.assertEqual(decode(3),E(0,0)); self.assertNotEqual(decode(1),decode(3))
        self.assertEqual(decode(5),B)
    def test_canonical_constant_folding(self):
        f=I(T,T); self.assertEqual(decode(encode(f)),T)
        self.assertEqual(decode(encode(f)),normalize(f))
    def test_capture_avoidance(self):
        f=A(1,E(0,1)); g=subst(f,{0:1})
        self.assertEqual(free(g),{1}); self.assertEqual(alpha_key(g),alpha_key(A(7,E(1,7))))
    def test_simultaneous_swap(self): self.assertEqual(subst(E(0,1),{0:1,1:0}),E(1,0))
    def test_bound_slot_not_replaced(self):
        self.assertEqual(subst(A(0,E(0,1)),{0:4,1:5}),A(0,E(0,5)))
    def test_schema_alpha_stability(self):
        f=A(7,I(E(0,7),E(7,1))); g=A(9,I(E(0,9),E(9,1)))
        self.assertEqual(alpha_key(closure(f)),alpha_key(closure(g)))
    def test_metric_controls(self):
        h=('H',0,1)
        oldpt=nodes(extensionality('old'))+nodes(closure(h,seed='point',mixed=True,curried=False))
        oldsub=nodes(extensionality('old'))+nodes(closure(h,mixed=True,curried=False))
        oldq=nodes(congruence('old'))+nodes(closure(h,mixed=True,curried=False))
        newq=nodes(congruence())+nodes(closure(h))
        self.assertEqual((oldpt,oldsub,oldq,newq),(69,72,83,64))
if __name__=='__main__': unittest.main(verbosity=2)
