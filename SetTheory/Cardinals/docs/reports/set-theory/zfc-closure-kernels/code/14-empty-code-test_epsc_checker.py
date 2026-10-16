import itertools, json, unittest
from pathlib import Path
from epsc_checker import *

def truth(a,domain,mem,env):
    if a==BOT:return False
    if a[0]=='mem':return mem[env[a[1]]][env[a[2]]]
    if a[0]=='imp':return not truth(a[1],domain,mem,env) or truth(a[2],domain,mem,env)
    return all(truth(a[2],domain,mem,env|{a[1]:x}) for x in domain)

class CheckerTests(unittest.TestCase):
    def test_identity(self):
        p=Mem(0,1)
        records=[['K',p,Imp(p,p)],['K',p,p],['S',p,Imp(p,p),p],['MP',0,2],['MP',1,3]]
        result=check(records)
        self.assertEqual(result['conclusion'],Imp(p,p));self.assertFalse(result['refutation'])
    def test_missing_rule_repaired(self):
        self.assertEqual(check([['UI',2,1,Mem(1,2)]])['conclusion'],Imp(All(2,Mem(1,2)),Mem(1,1)))
    def test_capture_avoidance(self):
        a=All(1,Mem(0,1));got=replace_free(a,{0:1})
        self.assertEqual(got,All(2,Mem(1,2)))
        self.assertEqual(free(got),{1})
    def test_shadowed_slot(self):
        m=All(0,Mem(0,1));out=epsc(m)
        self.assertEqual(free(out),set());self.assertNotEqual(out,BOT)
    def test_rejects_forward_reference(self):
        with self.assertRaises(ValueError):check([['GEN',0,0]])
    def test_rejects_fake_conclusion(self):
        with self.assertRaises(ValueError):check([['EPSC',Mem(0,1),BOT]])
    def test_rejects_boolean_label(self):
        with self.assertRaises(ValueError):formula(['mem',True,0])
    def test_vacuity_side_condition(self):
        with self.assertRaises(ValueError):check([['QD',0,Mem(0,1),BOT]])
    def test_ir_is_explicit(self):
        with self.assertRaises(ValueError):check([['IR']])
        self.assertTrue(check([['IR']],True)['valid'])
    def test_bad_mp(self):
        with self.assertRaises(ValueError):check([['K',Mem(0,0),BOT],['MP',0,0]])
    def test_substitution_semantics(self):
        forms=[Mem(0,1),All(1,Mem(0,1)),All(0,Mem(0,1)),
               All(2,Imp(Mem(0,2),All(1,Mem(2,1))))]
        checks=0
        for bits in range(16):
            mem=[[bool(bits&(1<<(i*2+j))) for j in range(2)] for i in range(2)]
            for vals in itertools.product(range(2),repeat=4):
                env=dict(enumerate(vals))
                for a in forms:
                    for x,y in itertools.product(range(3),repeat=2):
                        self.assertEqual(truth(replace_free(a,{x:y}),range(2),mem,env),
                                         truth(a,range(2),mem,env|{x:env[y]}));checks+=1
        self.assertEqual(checks,9216)

if __name__=='__main__':unittest.main()
