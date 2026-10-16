from __future__ import annotations
import itertools,json,random,sys,unittest
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'code'))
from logic import *
from codec import encode,decode,candidate

class ReferenceTests(unittest.TestCase):
    def test_identity(self):
        a=E(0,0);b=Imp(a,a)
        cert=[[0,a,b],[0,a,a],[1,a,b,a],[5,0,2],[5,1,3]]
        self.assertEqual(check(cert),{'valid':True,'refutation':False,'lines':5})
        self.assertTrue(same(derive(cert)[-1],Imp(a,a)))
    def test_ec_and_schema(self):
        for cert in ([[7]],[[8,E(0,1)]],[[8,All(0,Imp(E(0,2),E(1,3)))]]):
            self.assertTrue(check(cert)['valid']);self.assertFalse(check(cert)['refutation'])
            self.assertFalse(free(derive(cert)[-1]))
    def test_bad_references(self):
        for c in ([[5,0,0]],[[7],[5,0,1]],[[7],[6,0,-1]],[[7],[5,0,0]]):
            self.assertFalse(check(c)['valid'])
    def test_reject_admissions(self):
        for c in ([],[[100,BOTTOM]],[[8,['=',0,1]]],[[7,BOTTOM]],[[0,BOTTOM]]):
            self.assertFalse(check(c)['valid'])
    def test_booleans_not_integers(self):
        for c in ([[True,E(0,0),E(1,1)]],[[6,False,0]],[[8,[0,True,1]]]):
            self.assertFalse(check(c)['valid'])
    def test_capture_avoidance(self):
        a=All(1,E(0,1));out=rename_free(a,{0:1})
        self.assertEqual(free(out),{1});self.assertNotEqual(out[1],1)
        self.assertTrue(same(out,All(5,E(1,5))))
        self.assertEqual(rename_free(All(0,E(0,1)),{0:4}),All(0,E(0,1)))
    def test_simultaneous_rename_and_shadowing(self):
        self.assertEqual(rename_free(E(0,1),{0:1,1:0}),E(1,0))
        a=All(1,Imp(E(0,1),All(1,E(1,0))))
        self.assertEqual(free(rename_free(a,{0:1})),{1})
        self.assertTrue(same(All(0,All(0,E(0,2))),All(5,All(7,E(7,2)))))
        self.assertFalse(same(All(0,E(0,2)),All(2,E(2,0))))
    def test_q2_freshness(self):
        self.assertFalse(check([[4,0,E(0,1),E(2,2)]])['valid'])
        self.assertTrue(check([[4,3,E(0,1),E(2,2)]])['valid'])
    def test_alpha_rule(self):
        a=derive([[7]])[0]
        self.assertTrue(check([[7],[9,0,a]])['valid'])
        self.assertFalse(check([[7],[9,0,BOTTOM]])['valid'])
    def test_bottom_is_logically_false(self):
        for n in (1,2):
            pairs=list(itertools.product(range(n),repeat=2))
            for bits in range(1<<(n*n)):
                e={p for k,p in enumerate(pairs) if bits>>k&1}
                self.assertFalse(evaluate(BOTTOM,range(n),e,{}))
    def test_quantifier_instantiation_semantics(self):
        formulas=[All(1,E(0,1)),Imp(E(0,1),All(1,E(0,1))),All(0,E(0,1))]
        for n in (1,2):
            pairs=list(itertools.product(range(n),repeat=2))
            for bits in range(1<<(n*n)):
                e={p for k,p in enumerate(pairs) if bits>>k&1}
                for a in formulas:
                    ax=derive([[3,0,1,a]])[0]
                    for vals in itertools.product(range(n),repeat=2):
                        self.assertTrue(evaluate(ax,range(n),e,dict(enumerate(vals))))
    def test_prefix_code(self):
        xs=[0,1,100,[],[0,[]],[7],[[7]],[[8,[0,0,1]]]]
        for x in xs:self.assertEqual(decode(encode(x)),x)
        for bits in ('','0','1','01','11','1000','x'):
            with self.assertRaises(ValueError):decode(bits)
        self.assertEqual([candidate(i) for i in range(7)],['','0','1','00','01','10','11'])
    def test_random_roundtrips(self):
        rng=random.Random(20261016)
        def obj(d):
            if d==0 or rng.randrange(2):return rng.randrange(12)
            return [obj(d-1) for _ in range(rng.randrange(4))]
        for _ in range(1000):
            x=obj(4);self.assertEqual(decode(encode(x)),x)
    def test_schema_semantics_independent(self):
        rng=random.Random(254)
        matrices=[E(0,1),Imp(E(0,2),Not(E(1,0))),All(0,Imp(E(0,2),E(1,0))),
                  Not(All(3,Imp(E(0,3),E(1,3))))]
        checked=0
        for n in (1,2,3):
            dom=range(n)
            for _ in range(40):
                e={(i,j) for i in dom for j in dom if rng.randrange(2)}
                m=matrices[rng.randrange(len(matrices))]
                params=sorted(free(m)-{0,1})
                def subset(x,y):return all((z,x) not in e or (z,y) in e for z in dom)
                def direct(env):
                    def r(x,y):return evaluate(m,dom,e,env|{0:x,1:y})
                    bounded=all(any(all(not r(x,y) or subset(y,b) for y in dom)
                                    for b in dom) for x in dom)
                    if not bounded:return True
                    return all(any(
                      all(not ((subset(x,a) or (x,c) in e) and r(x,y)) or (y,c) in e
                          for x in dom for y in dom)
                      and all((y,c) not in e or any(r(x,y) for x in dom) for y in dom)
                      for c in dom) for a in dom)
                expected=all(direct(dict(zip(params,vals)))
                             for vals in itertools.product(dom,repeat=len(params)))
                self.assertEqual(evaluate(schema(m),dom,e,{}),expected);checked+=1
        self.assertEqual(checked,120)

if __name__=='__main__':unittest.main()
