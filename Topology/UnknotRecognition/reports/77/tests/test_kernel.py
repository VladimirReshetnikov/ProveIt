import copy
import random
import unittest
from boundary_kernel.kernel import (Kernel, Signature, SLP, Builder, exponent_mod,
                                    observe, certificate, transport, check_symplectic_images)
from boundary_kernel.verify import replay, verify_certificate
from boundary_kernel.binary import (magnus, lift_chain, doubled_chain, contraction,
                                    j_action, rank, cover_observation, optimal_characters)


def word(letters):
    b = Builder(); return b.build(b.word(letters))


def separator(h):
    return [x for i in range(h) for x in (2*i+1,2*i+2,-2*i-1,-2*i-2)]


def relator(g): return separator(g)


def inv(w): return [-x for x in reversed(w)]


def comm(a,b): return a+b+inv(a)+inv(b)


def reduce_word(w):
    out=[]
    for x in w:
        if out and out[-1] == -x: out.pop()
        else: out.append(x)
    return out


class KernelTests(unittest.TestCase):
    def test_identity_and_generators(self):
        for g in range(2,10):
            k=Kernel(g)
            for j in range(2*g):
                a=k.generator(j)
                self.assertEqual(k.multiply(a,k.inverse(a)),k.zero())
                self.assertEqual(k.multiply(k.zero(),a),a)

    def test_associativity(self):
        rng=random.Random(1301)
        for g in range(2,9):
            k=Kernel(g,True)
            for _ in range(50):
                a,b,c=[Signature(tuple(rng.randrange(k.q) for _ in range(2*g)),rng.randrange(g)) for _ in range(3)]
                self.assertEqual(k.multiply(k.multiply(a,b),c),k.multiply(a,k.multiply(b,c)))

    def test_inverse_random(self):
        rng=random.Random(44)
        for g in range(2,9):
            k=Kernel(g,True)
            for _ in range(50):
                a=Signature(tuple(rng.randrange(k.q) for _ in range(2*g)),rng.randrange(g))
                self.assertEqual(k.multiply(a,k.inverse(a)),k.zero())
                self.assertEqual(k.inverse(k.inverse(a)),a)

    def test_power_literal(self):
        for g in range(2,8):
            k=Kernel(g,True); a=k.literal([1,2,3,-2])
            for e in range(-15,16):
                u=[1,2,3,-2]
                expected=k.literal((u if e>=0 else inv(u))*abs(e))
                self.assertEqual(k.power(a,e),expected)

    def test_exponent_bound(self):
        for g in range(2,15):
            for safe in (False,True):
                k=Kernel(g,safe)
                self.assertEqual(k.power(k.literal([1,2,3,4]),k.exponent),k.zero())

    def test_binary_exponents(self):
        for m in range(1,23):
            for e in range(-50,51):
                s=('-' if e<0 else '+')+'0b'+bin(abs(e))[2:]
                self.assertEqual(exponent_mod(s,m),e%m)

    def test_large_exponent_no_expansion(self):
        b=Builder(); a=b.word([1,2]); root=b.add('pow',a,'0b1'+'0'*10000)
        s=b.build(root)
        for g in (2,3,10):
            k=Kernel(g)
            residue=pow(2,10000,k.exponent)
            self.assertEqual(s.evaluate(k),k.power(k.literal([1,2]),residue))

    def test_relator(self):
        for g in range(2,20):
            for safe in (False,True):
                self.assertEqual(word(relator(g)).evaluate(Kernel(g,safe)),Kernel(g,safe).zero())

    def test_genus_recovery(self):
        for g in range(2,15):
            for h in range(g+1):
                for orientation in (1,-1):
                    w=separator(h); w=w if orientation>0 else inv(w)
                    obs=observe(word([1,3]+w+[-3,-1]),g,True)
                    self.assertEqual(obs['complementary_genera_if_simple'],sorted((h,g-h)))
                    self.assertEqual(obs['status'],'UNDETECTED' if h in (0,g) else 'NONTRIVIAL')

    def test_nonseparating_twisted_curves(self):
        for g in range(2,9):
            for e in range(-12,13):
                # a_1 b_1^e is primitive on the first one-holed torus.
                w=[1]+([2] if e>=0 else [-2])*abs(e)
                self.assertEqual(observe(word(w),g)['simple_curve_consequence'],'essential nonseparating')

    def test_relator_insertions(self):
        rng=random.Random(2026)
        for g in range(2,8):
            for _ in range(30):
                w=[rng.choice((-1,1))*rng.randrange(1,2*g+1) for _ in range(25)]
                cut=rng.randrange(len(w)+1)
                self.assertEqual(word(w).evaluate(Kernel(g,True)),word(w[:cut]+relator(g)+w[cut:]).evaluate(Kernel(g,True)))

    def test_power_grammar_literal(self):
        b=Builder(); x=b.word([1,3,-2]); y=b.add('pow',x,-3); z=b.cat(x,b.inv(y)); s=b.build(z)
        self.assertEqual(s.evaluate(Kernel(3)),Kernel(3).literal(s.expand()))

    def test_dag_sharing(self):
        b=Builder(); x=b.word([1,2]);
        for _ in range(20): x=b.cat(x,x)
        s=b.build(x)
        k=Kernel(3)
        self.assertEqual(s.evaluate(k),k.power(k.literal([1,2]),2**20))
        self.assertEqual(len(s.evaluate(k,all_nodes=True)),len(s.rules))

    def test_expansion_cap(self):
        b=Builder(); x=b.word([1]); x=b.add('pow',x,'0b1'+'0'*1000)
        with self.assertRaises(OverflowError): b.build(x).expand(100)

    def test_validation(self):
        for g in (0,1,-1,2.5,True):
            with self.assertRaises(ValueError): Kernel(g)
        for rules in ([], [('cat',0,0)], [('gen',0)], [('blah',)], [('id',1)]):
            with self.assertRaises(ValueError): SLP(rules)
        for text in ('123','0b','0b2','--0b1','0x3'):
            with self.assertRaises(ValueError): exponent_mod(text,3)
        with self.assertRaises(TypeError): exponent_mod(True,3)
        with self.assertRaises(ValueError): word([9]).evaluate(Kernel(2))
        with self.assertRaises(ValueError): Kernel(2).validate(Signature((0,)*4,2))

    def test_canonical_digest(self):
        a=SLP([('gen',1),('pow',0,13)])
        b=SLP([('gen',1),('pow',0,'0b1101')])
        self.assertEqual(a.digest(),b.digest())

    def test_independent_matrix_random(self):
        rng=random.Random(5093)
        for g in range(2,8):
            for safe in (False,True):
                for _ in range(30):
                    b=Builder(); a=b.word([rng.choice((-1,1))*rng.randrange(1,2*g+1) for _ in range(12)])
                    a=b.add('pow',a,rng.randrange(-10,11)); s=b.build(b.cat(a,b.word([1,2,-1])))
                    k=Kernel(g,safe); sig=s.evaluate(k)
                    vector,area=replay(s.payload(),g,k.q)
                    self.assertEqual((list(sig.vector),sig.area),(vector,area))

    def test_certificates(self):
        for g in range(2,7):
            for w in ([],[1],separator(1),relator(g)):
                self.assertTrue(verify_certificate(certificate(word(w),g,True)))

    def test_tampered_certificates(self):
        c=certificate(word(separator(1)),3)
        changes={'area':0,'status':'UNKNOT','vector':[0]*5,'word_sha256':'0'*64,
                 'genus':4,'coordinate_modulus':5,'simple_curve_consequence':'contractible',
                 'complementary_genera_if_simple':[0,3],
                 'requires_external_simple_source_for_consequence':False,'schema':'unknown'}
        for key,value in changes.items():
            t=copy.deepcopy(c); t[key]=value
            self.assertFalse(verify_certificate(t),key)
        t=copy.deepcopy(c); t['word']['rules'][0][1]=3
        self.assertFalse(verify_certificate(t))

    def test_malformed_replay(self):
        with self.assertRaises(ValueError): replay({'rules':[['inv',0]],'root':0},2,2)
        with self.assertRaises(ValueError): replay({'rules':[['gen',True]],'root':0},2,2)
        self.assertFalse(verify_certificate({}))

    def test_no_unknot_verdict(self):
        for w in ([],[1],separator(1)):
            result=observe(word(w),3)
            self.assertIn(result['status'],('NONTRIVIAL','UNDETECTED'))
            self.assertTrue(result['requires_external_simple_source_for_consequence'])

    def test_nonsimple_blind_word(self):
        c=comm([1],[2]); w=comm(c,[1]+c+[-1])
        self.assertTrue(reduce_word(w))
        for g in range(2,8):
            self.assertEqual(word(w).evaluate(Kernel(g)),Kernel(g).zero())
        # Map a2->b1, b2->a1 to obtain a quotient onto F(a1,b1).
        substitution={1:[1],2:[2],3:[2],4:[1]}
        image=[]
        for x in relator(2): image += substitution[x] if x>0 else inv(substitution[-x])
        self.assertEqual(reduce_word(image),[])


class TransportTests(unittest.TestCase):
    def test_even_narrow_counterexample(self):
        for g in (2,4,6,8,10):
            k=Kernel(g)
            self.assertEqual(k.power(k.generator(0),g),k.zero())
            image=k.power(k.literal([1,2]),g)
            self.assertEqual(image.vector,(0,)*(2*g))
            self.assertEqual(image.area,g//2)

    def test_narrow_transport_rejected(self):
        k=Kernel(2)
        with self.assertRaises(ValueError): transport(k,k.zero(),[k.generator(i) for i in range(4)])

    def test_dehn_twist_transport(self):
        rng=random.Random(20261009)
        for g in range(2,9):
            k=Kernel(g,True); images=[k.generator(j) for j in range(2*g)]
            images[0]=k.literal([1,2])
            self.assertTrue(check_symplectic_images(k,images))
            for _ in range(30):
                s=word([rng.choice((-1,1))*rng.randrange(1,2*g+1) for _ in range(40)])
                self.assertEqual(transport(k,s.evaluate(k),images),s.evaluate(k,images))

    def test_symplectic_central_shifts(self):
        rng=random.Random(31)
        for g in range(2,8):
            k=Kernel(g,True)
            images=[Signature(k.generator(j).vector,rng.randrange(g)) for j in range(2*g)]
            self.assertTrue(check_symplectic_images(k,images))
            for _ in range(20):
                b=Builder(); a=b.word([rng.choice((-1,1))*rng.randrange(1,2*g+1) for _ in range(15)])
                s=b.build(b.add('pow',a,rng.randrange(-50,51)))
                self.assertEqual(transport(k,s.evaluate(k),images),s.evaluate(k,images))

    def test_bad_images_rejected(self):
        k=Kernel(3,True); images=[k.zero()]*6
        self.assertFalse(check_symplectic_images(k,images))
        with self.assertRaises(ValueError): transport(k,k.zero(),images)

    def test_twist_preserves_relator(self):
        for g in range(2,8):
            source=relator(g); target=[]
            for x in source: target += [1,2] if x==1 else [-2,-1] if x==-1 else [x]
            self.assertEqual(reduce_word(target),reduce_word(source))


class BinaryTests(unittest.TestCase):
    def test_relator_matrix(self):
        for g in range(2,12):
            x,m=magnus(word(relator(g)),g)
            self.assertEqual(x,0)
            self.assertEqual(m,tuple(1 << (i^1) for i in range(2*g)))

    def test_genus_ranks(self):
        for g in range(2,12):
            for h in range(g+1):
                x,m=magnus(word(separator(h)),g)
                self.assertEqual(x,0)
                self.assertEqual(sorted((rank(m),rank([row ^ (1<<(i^1)) for i,row in enumerate(m)]))),sorted((2*h,2*(g-h))))

    def test_lift_bridge_random(self):
        rng=random.Random(6226)
        for g in range(2,6):
            for _ in range(50):
                u=[rng.choice((-1,1))*rng.randrange(1,2*g+1) for _ in range(10)]
                v=[rng.choice((-1,1))*rng.randrange(1,2*g+1) for _ in range(10)]
                s=word(comm(u,v)); x,m=magnus(s,g)
                self.assertEqual(x,0)
                for _ in range(5):
                    a=rng.randrange(1,1<<(2*g)); eps,c0,c1=lift_chain(s,g,a)
                    self.assertEqual(eps,0)
                    expected=doubled_chain(contraction(m,a),2*g)
                    self.assertEqual(c0,expected); self.assertEqual(c1,expected)

    def test_lift_relator_boundary(self):
        for g in range(2,6):
            for alpha in range(1,1<<(2*g)):
                e,c0,c1=lift_chain(word(relator(g)),g,alpha)
                self.assertEqual((e,c0,c1),(0,doubled_chain(j_action(alpha,g),2*g),doubled_chain(j_action(alpha,g),2*g)))

    def test_selected_covers(self):
        for g in range(2,12):
            self.assertEqual(len(set(optimal_characters(g))),g+1)
            for h in range(1,g):
                self.assertTrue(cover_observation(word(separator(h)),g)['detected_by'])
            self.assertFalse(cover_observation(word(relator(g)),g)['detected_by'])

    def test_lift_powers(self):
        for g in (2,3):
            for alpha in range(1,1<<(2*g)):
                b=Builder(); x=b.word([1,2,-3]); s=b.build(b.add('pow',x,-3))
                self.assertEqual(lift_chain(s,g,alpha),lift_chain(word(s.expand()),g,alpha))

    def test_magnus_power_order(self):
        for g in (2,3,4):
            for e in range(-10,11):
                b=Builder(); a=b.word([1,2,3]); s=b.build(b.add('pow',a,e))
                self.assertEqual(magnus(s,g),magnus(word(s.expand()),g))

    def test_nonsimple_blind_to_covers(self):
        c=comm([1],[2]); s=word(comm(c,[1]+c+[-1]))
        for g in (2,3,4):
            self.assertEqual(magnus(s,g),(0,(0,)*(2*g)))
            self.assertFalse(cover_observation(s,g)['detected_by'])



class CoverBankTests(unittest.TestCase):
    def test_lagrangian_circuit(self):
        from boundary_kernel.cover_bank import analyze_bank
        for g in range(2,20):
            result=analyze_bank(g,optimal_characters(g))
            self.assertTrue(result['universal_for_separating_simple_curves'])
            self.assertEqual(result['span_dimension'],g)
            self.assertEqual(result['gram_rank'],0)

    def test_independent_lagrangian_not_enough(self):
        from boundary_kernel.cover_bank import analyze_bank
        for g in range(2,20):
            result=analyze_bank(g,optimal_characters(g)[:-1])
            self.assertFalse(result['universal_for_separating_simple_curves'])
            self.assertTrue(result['coisotropic'])
            self.assertEqual(len(result['orthogonal_blocks']),g)

    def test_standard_basis_not_universal(self):
        from boundary_kernel.cover_bank import analyze_bank
        for g in range(2,10):
            r=analyze_bank(g,[1<<i for i in range(2*g)])
            self.assertTrue(r['coisotropic'])
            self.assertEqual(len(r['orthogonal_blocks']),g)
            self.assertFalse(r['universal_for_separating_simple_curves'])

    def test_nonlagrangian_optimal_bank(self):
        from boundary_kernel.cover_bank import analyze_bank
        # Three independent vectors, all three pairings nonzero, in genus two.
        r=analyze_bank(2,[1,2,7])
        self.assertEqual(r['span_dimension'],3)
        self.assertEqual(r['gram_rank'],2)
        self.assertTrue(r['universal_for_separating_simple_curves'])

    def test_duplicates_and_empty(self):
        from boundary_kernel.cover_bank import analyze_bank
        self.assertFalse(analyze_bank(2,[])['universal_for_separating_simple_curves'])
        self.assertFalse(analyze_bank(2,[1,1,1])['universal_for_separating_simple_curves'])
        self.assertTrue(analyze_bank(2,[1,4,5,5])['universal_for_separating_simple_curves'])

    def test_coordinate_replay(self):
        from boundary_kernel.cover_bank import analyze_bank
        rng=random.Random(1701)
        for g in range(2,9):
            for _ in range(20):
                a=[rng.randrange(1,1<<(2*g)) for __ in range(3*g)]
                r=analyze_bank(g,a);b=[a[j] for j in r['basis_indices']]
                for original,mask in zip(a,r['coordinate_masks']):
                    rebuilt=0
                    for j,x in enumerate(b):
                        if (mask>>j)&1: rebuilt^=x
                    self.assertEqual(original,rebuilt)

    def test_bad_bank(self):
        from boundary_kernel.cover_bank import analyze_bank
        for bank in ([0],[16],[-1],[True]):
            with self.assertRaises(ValueError): analyze_bank(2,bank)

class TransportPlanTests(unittest.TestCase):
    def test_plan_checks_once(self):
        from unittest.mock import patch
        from boundary_kernel.kernel import TransportPlan
        k=Kernel(4,True); images=[k.generator(j) for j in range(8)]
        images[0]=k.literal([1,2])
        with patch('boundary_kernel.kernel.check_symplectic_images',wraps=check_symplectic_images) as check:
            plan=TransportPlan(k,images)
            for i in range(10):
                s=word([1,3,2,-4]*i)
                self.assertEqual(plan.apply(s.evaluate(k)),s.evaluate(k,images))
            self.assertEqual(check.call_count,1)

    def test_plan_copies_image_list(self):
        from boundary_kernel.kernel import TransportPlan
        k=Kernel(2,True); images=[k.generator(j) for j in range(4)]
        plan=TransportPlan(k,images); images[0]=k.zero()
        self.assertEqual(plan.apply(k.generator(0)),k.generator(0))

    def test_mutable_signature_vector_rejected(self):
        with self.assertRaises(ValueError): Kernel(2).validate(Signature([0]*4,0))


class InputSensitiveSetupTests(unittest.TestCase):
    def test_default_generators_are_lazy(self):
        from unittest.mock import patch
        k=Kernel(1000)
        s=SLP([('gen',1)])
        with patch.object(k,'generator',wraps=k.generator) as make:
            value=s.evaluate(k)
            self.assertEqual(make.call_count,1)
        self.assertEqual(value,k.generator(0))


if __name__ == '__main__': unittest.main()
