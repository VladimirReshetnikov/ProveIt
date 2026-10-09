from copy import deepcopy
import itertools
import random
import unittest
from unittest.mock import patch

from compressed_b3 import *
from compressed_b3.grammar import expand
from compressed_b3.engine import Reducer, IMAGE
from compressed_b3.forest import summarize, project, recognize_forest, verify_forest
from experiments.oracles import explicit, matrix, tokens_reduce, cyclic_tokens
from experiments.families import sleeve, singleton_forest


class GrammarTests(unittest.TestCase):
    def test_empty(self):
        b = Builder(); d = b.data(0)
        self.assertEqual(recognize(d)['status'], 'LINK')
    def test_bad_generator(self):
        for g in (0, 3, True, '1'):
            with self.assertRaises(ValueError): Builder().letter(g)
    def test_forward_reference(self):
        with self.assertRaises(ValueError): validate(dict(strands=3, rules=[['e'], ['c',1,0]], root=1))
    def test_bool_root(self):
        with self.assertRaises(ValueError): validate(dict(strands=3, rules=[['e']], root=False))
    def test_power_inverse(self):
        b=Builder();root=b.power(b.word([1,-2]),-7);d=b.data(root)
        self.assertEqual(expand(d),[2,-1]*7)
    def test_summary_multiplicity(self):
        b=Builder();d=b.data(b.power(b.word([1,-2]),1<<200))
        s=validate(d);self.assertEqual(s.lengths[s.root],1<<201);self.assertEqual(s.exponents[s.root],0)
    def test_foreign_strands(self):
        with self.assertRaises(ValueError):validate(dict(strands=4,rules=[['e']],root=0))


class StringTests(unittest.TestCase):
    def test_forced_polynomial_equal(self):
        a=Arena(equality_probe_steps=0,prefix_probe_steps=0)
        u=a.from_word([1,2,1,3]*12);v=0
        for x in [1,2,1,3]*12:v=a.concat(v,a.letter(x))
        self.assertTrue(a.equal(u,v));self.assertGreater(a.stats['splits'],0)
    def test_random_equal_and_lcp(self):
        rng=random.Random(451)
        for _ in range(80):
            u=[rng.randint(1,3) for _ in range(rng.randrange(1,50))];v=u[:]
            if rng.randrange(2):v[rng.randrange(len(v))]=rng.randint(1,3)
            a=Arena(equality_probe_steps=0,prefix_probe_steps=0)
            U=a.from_word(u);V=0
            for x in v:V=a.concat(V,a.letter(x))
            self.assertEqual(a.equal(U,V),u==v)
            k=next((i for i,(x,y) in enumerate(zip(u,v)) if x!=y),len(u))
            self.assertEqual(a.lcp(U,V),k)
    def test_all_slices(self):
        a=Arena();u=list(range(1,24));root=a.from_word(u)
        for i in range(24):
            for j in range(i,24):self.assertEqual(a.expand(a.slice(root,i,j)),u[i:j])
    def test_inverse_involution(self):
        a=Arena();r=Reducer(a);u=a.from_word([1,2,3,1,2])
        self.assertTrue(a.equal(u,r.inverse(r.inverse(u))))
    def test_boundary_merge(self):
        a=Arena();r=Reducer(a);u=a.from_word([1,2]);v=a.from_word([2,1])
        root,k=r.multiply(u,v);self.assertEqual(k,0);self.assertEqual(a.expand(root),[1,3,1])
    def test_boundary_cascade(self):
        a=Arena();r=Reducer(a);u=a.from_word([2,1,3]);v=a.from_word([2,1,2])
        root,k=r.multiply(u,v);self.assertEqual(k,2);self.assertEqual(a.expand(root),[3])
    def test_random_products(self):
        rng=random.Random(398)
        for _ in range(300):
            u=tokens_reduce(rng.choices([1,2,3],k=50));v=tokens_reduce(rng.choices([1,2,3],k=50))
            a=Arena();r=Reducer(a);root,_=r.multiply(a.from_word(u),a.from_word(v))
            self.assertEqual(a.expand(root),tokens_reduce(u+v))
    def test_random_cyclic(self):
        rng=random.Random(123)
        for _ in range(150):
            u=tokens_reduce(rng.choices([1,2,3],k=80));a=Arena();r=Reducer(a)
            c,q,_,_=r.cyclic(a.from_word(u))
            self.assertEqual(a.expand(c),cyclic_tokens(u))
            root,_=r.multiply(q,c);root,_=r.multiply(root,r.inverse(q))
            self.assertEqual(a.expand(root),u)


class RecognitionTests(unittest.TestCase):
    def test_small_complete_sweep(self):
        for n in range(5):
            for w in itertools.product((1,-1,2,-2),repeat=n):
                b=Builder();d=b.data(b.word(w));r=recognize(d)
                self.assertEqual(r['status'],explicit(w));self.assertEqual(r['status'],matrix(w))
                self.assertEqual(verify(d,r['certificate']),r['status'])
    def test_artin_relation(self):
        rng=random.Random(194)
        for _ in range(40):
            left=rng.choices([1,-1,2,-2],k=7);right=rng.choices([1,-1,2,-2],k=7)
            ds=[]
            for centre in ([1,2,1],[2,1,2]):
                b=Builder();ds.append(b.data(b.word(left+centre+right)))
            self.assertEqual(recognize(ds[0])['status'],recognize(ds[1])['status'])
    def test_conjugation_and_mirror(self):
        rng=random.Random(641)
        for _ in range(70):
            w=rng.choices([1,-1,2,-2],k=12);q=rng.choices([1,-1,2,-2],k=15)
            for v in (q+w+[-x for x in q[::-1]],[-x for x in w]):
                b=Builder();d=b.data(b.word(v));self.assertEqual(recognize(d)['status'],explicit(w))
    def test_huge_positive_no_expansion(self):
        d=sleeve(256)
        with patch.object(Arena,'expand',side_effect=AssertionError('expansion forbidden')):
            r=recognize(d);self.assertEqual(verify(d,r['certificate']),'UNKNOT')
    def test_huge_negative_no_expansion(self):
        d=sleeve(256,negative=True)
        with patch.object(Arena,'expand',side_effect=AssertionError('expansion forbidden')):
            r=recognize(d);self.assertEqual(verify(d,r['certificate']),'KNOTTED')
    def test_reassociated_sleeve_forced_fallback(self):
        d=sleeve(8,reassociated=True)
        r=recognize(d,equality_probe_steps=0,prefix_probe_steps=0)
        self.assertGreater(r['stats']['splits'],0)
        self.assertEqual(verify(d,r['certificate'],equality_probe_steps=0),'UNKNOT')
    def test_limits(self):
        with self.assertRaises(Limit):recognize(sleeve(20),max_nodes=3)
        with self.assertRaises(Limit):recognize(sleeve(20),max_work=3)


class CertificateTests(unittest.TestCase):
    def setUp(self):
        self.d=sleeve(5);self.c=recognize(self.d)['certificate']
    def test_wrong_source(self):
        d=sleeve(6)
        with self.assertRaises(ValueError):verify(d,self.c)
    def test_wrong_verdict(self):
        c=deepcopy(self.c);c['status']='KNOTTED'
        with self.assertRaises(ValueError):verify(self.d,c)
    def test_wrong_exponent(self):
        c=deepcopy(self.c);c['exponent_hex']='0x0'
        with self.assertRaises(ValueError):verify(self.d,c)
    def test_wrong_cancellation(self):
        c=deepcopy(self.c);i=next(i for i,k in enumerate(c['cancellations_hex']) if int(k,16)>0)
        c['cancellations_hex'][i]=hex(int(c['cancellations_hex'][i],16)+1)
        with self.assertRaises(ValueError):verify(self.d,c)
    def test_wrong_cyclic_trim(self):
        c=deepcopy(self.c);c['cyclic']['trim_hex']='0x0'
        with self.assertRaises(ValueError):verify(self.d,c)
    def test_wrong_grammar_letter(self):
        c=deepcopy(self.c);i=next(i for i,r in enumerate(c['string_rules']) if r[0]=='t')
        c['string_rules'][i][1]=99
        with self.assertRaises(ValueError):verify(self.d,c)
    def test_no_producer_no_lcp_during_verify(self):
        with patch('compressed_b3.engine.recognize',side_effect=AssertionError),patch.object(Arena,'lcp',side_effect=AssertionError):
            self.assertEqual(verify(self.d,self.c),'UNKNOT')


class ForestTests(unittest.TestCase):
    def test_many_strands_positive(self):
        d=singleton_forest(5,6);r=recognize_forest(d)
        self.assertEqual(verify_forest(d,r['certificate']),'UNKNOT')
        self.assertEqual(r['certificate']['cuts'],[3,6,9,12])
    def test_many_strands_negative(self):
        d=singleton_forest(4,5,negative_index=2);r=recognize_forest(d)
        self.assertEqual(verify_forest(d,r['certificate']),'KNOTTED')
    def test_huge_forest_no_expansion(self):
        d=singleton_forest(5,128)
        with patch.object(Arena,'expand',side_effect=AssertionError):
            r=recognize_forest(d);self.assertEqual(verify_forest(d,r['certificate']),'UNKNOT')
    def test_big_empty_strand_range(self):
        d=dict(strands=10**100,rules=[['e']],root=0);r=recognize_forest(d)
        self.assertEqual(verify_forest(d,r['certificate']),'LINK')
    def test_missing_root_support(self):
        d=dict(strands=4,rules=[['e'],['g',1],['g',2],['g',3]],root=1)
        self.assertEqual(recognize_forest(d)['status'],'LINK')
    def test_at_most_two(self):
        for e,status in [(1,'UNKNOT'),(3,'KNOTTED')]:
            d=dict(strands=2,rules=[['e'],['g',1]],root=1)
            for _ in range(e-1):d['rules'].append(['c',d['root'],1]);d['root']=len(d['rules'])-1
            r=recognize_forest(d);self.assertEqual(verify_forest(d,r['certificate']),status)
    def test_one_strand(self):
        d=dict(strands=1,rules=[['e']],root=0);r=recognize_forest(d)
        self.assertEqual(verify_forest(d,r['certificate']),'UNKNOT')
    def test_unresolved_four_strands(self):
        d=dict(strands=4,rules=[['e']],root=0)
        for g in [1,2,-3]*3:
            j=len(d['rules']);d['rules'].append(['g',g]);d['rules'].append(['c',d['root'],j]);d['root']=j+1
        r=recognize_forest(d);self.assertEqual(verify_forest(d,r['certificate']),'INCONCLUSIVE')
    def test_tampered_cut(self):
        d=singleton_forest(3,2);r=recognize_forest(d);c=r['certificate'];c['cuts']=[]
        with self.assertRaises(ValueError):verify_forest(d,c)
    def test_tampered_projection(self):
        d=singleton_forest(3,2);c=recognize_forest(d)['certificate'];c['leaves'][0]['grammar']['root']=0
        with self.assertRaises(ValueError):verify_forest(d,c)

class AdditionalTests(unittest.TestCase):
    def test_exact_input_binding_rejects_boolean_alias(self):
        d=sleeve(3);c=recognize(d)['certificate']
        i=next(i for i,r in enumerate(c['input']['rules']) if r==['g',1])
        c['input']['rules'][i][1]=True
        with self.assertRaises(ValueError):verify(d,c)
    def test_matrix_growth_formula(self):
        def mm(u,v):
            a,b,c,d=u;e,f,g,h=v
            return a*e+b*g,a*f+b*h,c*e+d*g,c*f+d*h
        Q=(2,1,1,1);q=(1,0,0,1);T=(0,1,-1,1)
        for m in range(1,40):
            q=mm(q,Q);a,b,_,d=q
            out=mm(mm(q,T),(d,-b,-b,a))
            self.assertEqual(out[1],3*b*b+3*b*d+d*d)
            self.assertEqual(out[0]+out[3],1)
            self.assertGreaterEqual(out[1].bit_length(),2*m-1)
    def test_forest_without_singletons_stays_inconclusive(self):
        d=dict(strands=4,rules=[['e']],root=0)
        for g in [1,2,-3]*3:
            j=len(d['rules']);d['rules'].append(['g',g]);d['rules'].append(['c',d['root'],j]);d['root']=j+1
        out=recognize_forest(d)
        self.assertEqual(out['certificate']['cuts'],[])
        self.assertEqual(out['status'],'INCONCLUSIVE')

if __name__=='__main__':unittest.main()
