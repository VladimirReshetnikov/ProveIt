import sys, unittest, random, itertools
from pathlib import Path
from math import gcd
from dataclasses import replace
from unittest.mock import patch
sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'code'))
from christoffel import *
from checker import verify_power
from oracle import *
from braid_bridge import produce, verify_braid_certificate, validate_braid
from contraction import *
from wordarena_adapter import query_wordarena
from jones_oracle import jones_braid

COUNTERS = {}


def cyclic_words(n, prefix=()):
    if len(prefix) == n:
        if not prefix or prefix[0] != -prefix[-1]: yield prefix
        return
    for x in (1,-1,2,-2):
        if not prefix or x != -prefix[-1]: yield from cyclic_words(n, prefix+(x,))


class ResearchTests(unittest.TestCase):
    def test_01_exhaustive_whitehead(self):
        count = powers = 0
        for n in range(1,10):
            for word in cyclic_words(n):
                arena = Arena(); root = arena.from_word(word)
                result = classify(arena.rules, root)
                expected, exponent = whitehead_primitive_power(word)
                self.assertEqual(result.certificate is not None, expected, word)
                if expected:
                    self.assertEqual(result.certificate.exponent, exponent)
                    self.assertTrue(verify_power(arena.rules, result.certificate))
                    powers += 1
                count += 1
        COUNTERS['cyclically_reduced_words_length_1_to_9'] = count
        COUNTERS['primitive_powers_in_exhaustive_set'] = powers

    def test_02_euclidean_generators_and_rotations(self):
        count = 0
        for p in range(1,13):
            for q in range(1,13):
                if gcd(p,q) != 1: continue
                arena, root = christoffel_slp(p,q)
                word = arena.expand(root)
                self.assertEqual(word.count(1),p); self.assertEqual(word.count(2),q)
                self.assertTrue(whitehead_primitive(word))
                for k in range(len(word)):
                    w = word[k:]+word[:k]
                    for sa,sb in ((1,1),(-1,1),(1,-1),(-1,-1)):
                        A = Arena(); r = A.from_word(tuple(sa*x if x==1 else sb*x for x in w)*3)
                        c = classify(A.rules,r).certificate
                        self.assertTrue(c); self.assertEqual(c.exponent,3)
                        self.assertTrue(verify_power(A.rules,c)); count += 1
        COUNTERS['rotated_signed_Christoffel_power_checks'] = count

    def test_03_random_parses(self):
        rng = random.Random(80123)
        for _ in range(1200):
            w = cyclic_reduce(rng.choice((1,-1,2,-2)) for _ in range(rng.randrange(1,50)))
            A = Arena(); pieces = [A.letter(x) for x in w]
            while len(pieces)>1:
                k=rng.randrange(len(pieces)-1); pieces[k:k+2]=[A.concat(*pieces[k:k+2])]
            r=pieces[0] if pieces else 0
            c=classify(A.rules,r).certificate
            self.assertEqual(bool(c),whitehead_primitive_power(w)[0])
            if c:self.assertTrue(verify_power(A.rules,c))
        COUNTERS['random_parse_checks']=1200

    def test_04_not_abelianization(self):
        for p,q in ((2,3),(3,5),(5,8),(13,21)):
            A=Arena(); r=A.from_word((1,)*p+(-2,)*q)
            self.assertIsNone(classify(A.rules,r).certificate)
        A=Arena(); r=A.from_word((1,1,-2,-2,-2))
        self.assertEqual(literal_width(A.expand(r)),(6,4,1))

    def test_05_noncoherence_and_preconditions(self):
        A=Arena(); r=A.from_word((1,2,-1,-2))
        self.assertIsNone(classify(A.rules,r).certificate)
        for w in ((1,-1),(1,2,-1)):
            A=Arena();r=A.from_word(w)
            with self.assertRaises(InputError):classify(A.rules,r)
        self.assertIsNone(classify([None],0).certificate)

    def test_06_pure_powers(self):
        for x in (1,-1,2,-2):
            A=Arena();r=A.power(A.letter(x),2**4096)
            c=classify(A.rules,r).certificate
            self.assertEqual(c.exponent,2**4096);self.assertEqual(c.width,0)
            self.assertTrue(verify_power(A.rules,c))

    def test_07_huge_nonuniform_no_expansion(self):
        A,r=fibonacci_slp(4096);r=A.power(r,2**4096+1)
        with patch.object(A,'expand',side_effect=AssertionError('expansion forbidden')):
            c=classify(A.rules,r).certificate
            self.assertTrue(c);self.assertEqual(c.exponent,2**4096+1)
            self.assertTrue(verify_power(A.rules,c))
        COUNTERS['large_nonuniform_nodes']=len(A.rules)
        COUNTERS['large_nonuniform_expanded_length_bits']=A.lengths[r].bit_length()

    def test_08_mutations(self):
        A,r=christoffel_slp(13,8);c=classify(A.rules,r).certificate
        for field,value in (('root',0),('root',-1),('root',True),('u',14),('v',9),('exponent',2),('width',21),('exponent',True)):
            self.assertFalse(verify_power(A.rules,replace(c,**{field:value})))
        bad=list(A.rules);bad[-1]=('c',r,r)
        self.assertFalse(verify_power(bad,c))
        B=Arena();s=B.from_word((1,)*13+(2,)*8)
        fake=PowerCertificate(s,13,8,1,20)
        self.assertFalse(verify_power(B.rules,fake))

    def test_09_independent_checker(self):
        A,r=christoffel_slp(55,34);c=classify(A.rules,r).certificate
        with patch('christoffel.classify',side_effect=AssertionError), patch('christoffel.inspect',side_effect=AssertionError),patch('christoffel.profiles',side_effect=AssertionError):
            self.assertTrue(verify_power(A.rules,c))

    def test_10_invalid_nodes_and_limits(self):
        for rules in ([('t',1)], [None,('t',True)], [None,('c',0,1)], [None,('x',1)], [None,('t',3)]):
            with self.assertRaises(InputError):inspect(rules)
        A,r=fibonacci_slp(100)
        with self.assertRaises(ResourceLimit):classify(A.rules,r,limits=Limits(max_nodes=4))
        with self.assertRaises(ResourceLimit):classify(A.rules,r,limits=Limits(max_bits=4))
        with self.assertRaises(InterruptedError):classify(A.rules,r,check=lambda: (_ for _ in ()).throw(InterruptedError()))
        c=classify(A.rules,r).certificate
        with self.assertRaises(InterruptedError):verify_power(A.rules,c,check=lambda: (_ for _ in ()).throw(InterruptedError()))

    def test_11_shared_scan_and_group_types(self):
        A,r=christoffel_slp(13,8);roots=[A.power(r,12),A.power(r,18),0]
        import christoffel
        with patch('christoffel.profiles',wraps=christoffel.profiles) as spy:
            result=scan_aligned(A.rules,roots)
            self.assertEqual(spy.call_count,1)
        self.assertTrue(result['all_powers']);self.assertEqual(result['exponent_gcd'],6)
        self.assertEqual(aligned_group_type(A.rules,roots)['g'],6)
        roots.append(A.power(r,2**500+1))
        self.assertEqual(aligned_group_type(A.rules,roots)['group'],'Z')
        self.assertEqual(aligned_group_type([None,('c',0,0)],[1])['group'],'F2')

    def test_12_common_slope_guards(self):
        A=Arena();a=A.letter(1);b=A.letter(2)
        self.assertEqual(scan_aligned(A.rules,[a,b])['status'],'NONCOLLINEAR')
        r=A.from_word((1,2,-1,-2))
        self.assertFalse(scan_aligned(A.rules,[r])['all_powers'])
        bad=A.from_word((1,1,2,2,2))
        good=A.from_word((1,2,1,2,2))
        out=scan_aligned(A.rules,[bad,good])
        self.assertFalse(out['all_powers']);self.assertEqual(len(out['certificates']),1)

    def test_13_adapter(self):
        A,r=christoffel_slp(5,3)
        calls=[];A.tick=lambda *args:calls.append(1)
        output=query_wordarena(A,[r],{1,2})
        self.assertEqual(len(output['certificates']),1);self.assertTrue(calls)
        self.assertEqual(query_wordarena(A,[r],{1,2,3})['status'],'UNSUPPORTED_RANK')

    def test_14_braid_known_cases(self):
        positives=[(1,[]),(2,[1]),(2,[-1]),(3,[1,2]),(3,[1,-2]),(4,[1,2,3])]
        negatives=[(2,[1]*k) for k in (3,5,7)]+[(3,[1,-2,1,-2]),(3,[1,2]*4)]
        for b,w in positives:
            out=produce(b,w);self.assertEqual(out['status'],'UNKNOT')
            self.assertEqual(jones_braid(b,w),{0:1})
        for b,w in negatives:
            self.assertEqual(produce(b,w)['status'],'INCONCLUSIVE')
            self.assertNotEqual(jones_braid(b,w),{0:1})

    def test_15_braid_certificate_independence_and_mutation(self):
        from copy import deepcopy
        b,w=4,[1,2,3];out=produce(b,w);c=out['certificate']
        with patch('braid_bridge.presentation',side_effect=AssertionError),patch('braid_bridge.eliminate',side_effect=AssertionError),patch('braid_bridge._terminal',side_effect=AssertionError):
            self.assertTrue(verify_braid_certificate(b,w,c))
        wrong=deepcopy(c);wrong['moves'][0]['generator']=99
        self.assertFalse(verify_braid_certificate(b,w,wrong))
        wrong=deepcopy(c);wrong['terminal']['slot']=99
        self.assertFalse(verify_braid_certificate(b,w,wrong))
        self.assertFalse(verify_braid_certificate(b,[1,2,-3],c))
        with self.assertRaises(ValueError):produce(2,[1,1])
        self.assertEqual(produce(3,[1,2],cap=1)['status'],'INCONCLUSIVE')

    def test_16_random_braid_jones_crosscheck(self):
        rng=random.Random(198412)
        count=accepted=0
        for _ in range(400):
            b=rng.choice([2,3,4]);n=rng.randrange(1,11)
            w=[rng.choice([-1,1])*rng.randrange(1,b) for _ in range(n)]
            try:validate_braid(b,w)
            except ValueError:continue
            a=produce(b,w);c=produce(b,w,engine='whitehead')
            self.assertEqual(a['status'],c['status'],(b,w))
            j=jones_braid(b,w)
            if a['status']=='UNKNOT':
                self.assertEqual(j,{0:1},(b,w));accepted+=1
            count+=1
        COUNTERS['random_knot_braid_Jones_crosschecks']=count
        COUNTERS['random_knot_braids_certified_unknot']=accepted

    def test_17_braid_relations(self):
        self.assertEqual(jones_braid(3,[1,2,1,2]),jones_braid(3,[2,1,2,2]))
        self.assertEqual(jones_braid(2,[1,1,-1]),jones_braid(2,[1]))

    def test_18_balanced_contractions(self):
        with patch('christoffel.Arena.expand',side_effect=AssertionError('expansion forbidden')):
            for depth in range(1,9):
                A,roots,alive=balanced_family(depth,12)
                output=run_contractions(A.rules,roots,alive)
                self.assertEqual(len(output['rounds']),depth)
                self.assertEqual(len(output['alive']),1)
                self.assertTrue(rank_one_endpoint(output['rules'], output['roots'], output['alive']))
        COUNTERS['balanced_contraction_max_initial_rank']=256

    def test_19_contraction_images_literal(self):
        # One primitive relation on a,b and an unrelated word using c.
        A=GenericArena();p=A.from_word((1,2,1,2,2));s=A.from_word((3,1,-3,2))
        new,roots,alive,verified=apply_round(A.rules,[p,s],{1,2,3},[{'slot':0,'pair':[1,2]}])
        self.assertEqual(alive,{1,3});self.assertEqual(roots[0],0)
        self.assertEqual(new.expand(roots[1]),(3,1,1,1,-3,-1,-1))
        self.assertEqual(verified[0][2:4],(2,3))

    def test_20_contraction_round_guards(self):
        A,roots,alive=balanced_family(2,4)
        with self.assertRaises(InputError):apply_round(A.rules,roots,alive,[{'slot':0,'pair':[1,2]},{'slot':1,'pair':[1,2]}])
        with self.assertRaises(ResourceLimit):apply_round(A.rules,roots,alive,plan_round(A.rules,roots,alive),max_nodes=2)
        A=GenericArena();r=A.from_word((1,1,2,2,2))
        with self.assertRaises(InputError):apply_round(A.rules,[r],{1,2},[{'slot':0,'pair':[1,2]}])

    def test_21_raw_cancellation_not_silently_normalized(self):
        A=GenericArena();r=A.from_word((1,2,-2))
        self.assertEqual(plan_round(A.rules,[r],{1,2}),[])

    def test_22_certificate_json_large_integer(self):
        import json
        A,r=fibonacci_slp(50);r=A.power(r,2**20000+1)
        c=classify(A.rules,r).certificate
        text=json.dumps(c.json())
        self.assertEqual(int(json.loads(text)['exponent'],16),2**20000+1)


if __name__=='__main__':
    import json, time
    start=time.perf_counter()
    suite=unittest.defaultTestLoader.loadTestsFromTestCase(ResearchTests)
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    report=dict(tests_run=result.testsRun,failures=len(result.failures),errors=len(result.errors),
                seconds=time.perf_counter()-start,counters=COUNTERS)
    target=Path(__file__).resolve().parents[1]/'data'/'test_summary.json'
    target.write_text(json.dumps(report,indent=2)+'\n')
    sys.exit(not result.wasSuccessful())
