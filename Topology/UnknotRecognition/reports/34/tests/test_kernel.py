import copy
import itertools
import random
import unittest
from braidkernel import Braid, singleton_certificate, verify_certificate, connected_sum_braid, kernelize, recognize
from braidkernel.cube import reduced_khovanov, normalized_bracket, ResourceLimit
from braidkernel.descent import linear_descent, verify_descent


def random_knots(count, seed=83117, maximum=8):
    rng = random.Random(seed)
    result = []
    while len(result) < count:
        b = rng.randint(2, min(6, maximum+1))
        n = rng.randint(b-1, maximum)
        w = [rng.choice((-1,1))*rng.randrange(1,b) for _ in range(n)]
        try:
            result.append(Braid.checked(b,w))
        except ValueError:
            pass
    return result


class InputTests(unittest.TestCase):
    def test_empty_one_strand(self):
        self.assertEqual(recognize(Braid.checked(1,[]))['status'], 'UNKNOT')
    def test_invalid_strands(self):
        for b in (0,-1,True,2.5,'3'):
            with self.assertRaises(ValueError): Braid.checked(b, [])
    def test_invalid_letters(self):
        for w in ([0],[2],[-2],[True],[1.0],['1']):
            with self.assertRaises(ValueError): Braid.checked(2,w)
    def test_reject_link(self):
        for b,w in [(2,[]),(2,[1,1]),(3,[1]),(3,[1,2,1])]:
            with self.assertRaises(ValueError): Braid.checked(b,w)
    def test_sparse_strand_bomb(self):
        with self.assertRaises(ValueError): Braid.checked(10**100, [1])

class KernelTests(unittest.TestCase):
    def test_every_small_tree(self):
        for b in range(1,7):
            for signs in itertools.product((-1,1), repeat=b-1):
                w = [signs[j-1]*j for j in range(1,b)]
                for v in (w, list(reversed(w))):
                    result = kernelize(Braid.checked(b,v))
                    self.assertEqual(result['status'], 'UNKNOT')
                    self.assertEqual(result['stats']['core_letters'],0)
    def test_internal_singleton(self):
        x=Braid.checked(4,[1,3,1,3,-1,-3,2])
        fs=verify_certificate(x,singleton_certificate(x))
        self.assertEqual([f.word for f in fs],[(1,1,-1),(1,1,-1)])
        self.assertEqual(recognize(x)['status'],'UNKNOT')
    def test_factor_local_bennequin(self):
        x=Braid.checked(4,[1,1,1,-3,-3,-3,2])
        self.assertLessEqual(abs(x.exponent),x.strands-1)
        self.assertEqual(kernelize(x)['status'],'KNOTTED')
    def test_four_k_sharpness(self):
        for k in range(1,20):
            w=[]
            for j in range(k): w.extend([2*j+1,2*j+2,2*j+1,-(2*j+2)])
            x=Braid.checked(2*k+1,w);r=kernelize(x)
            self.assertEqual(r['status'],'CORE')
            self.assertEqual(r['stats']['core_letters'],4*k)
            self.assertEqual(r['stats']['input_minority'],k)
            self.assertEqual(r['stats']['singleton_cuts'],0)
    def test_large_stabilized_core(self):
        x=Braid.checked(10003,[1,2,1,-2]+list(range(3,10003)))
        r=kernelize(x)
        self.assertEqual(r['merged_kernel'], {'strands':3,'word':[1,2,1,-2]})
        self.assertEqual(recognize(x)['status'],'UNKNOT')
    def test_mirrors(self):
        for x in random_knots(50):
            a=kernelize(x);b=kernelize(Braid.checked(x.strands,[-g for g in x.word]))
            self.assertEqual(a['status'],b['status'])
            self.assertEqual(a['stats'],b['stats'])
    def test_random_bounds(self):
        for x in random_knots(400,maximum=80):
            r=kernelize(x)
            self.assertLessEqual(r['stats']['core_letters'],4*x.canonical_genus)
            if r['status']!='KNOTTED':
                self.assertLessEqual(r['stats']['core_letters'],4*r['stats']['core_minority_sum'])
                self.assertLessEqual(r['stats']['core_minority_sum'],x.minority)
    def test_certificate_wrong_word(self):
        x=Braid.checked(4,[1,2,1,-2,3]);c=singleton_certificate(x)
        y=Braid.checked(4,[1,-2,1,-2,3])
        with self.assertRaises(ValueError):verify_certificate(y,c)
    def test_certificate_missing_cut(self):
        x=Braid.checked(4,[1,2,3]);c=singleton_certificate(x);c['cuts'].pop()
        with self.assertRaises(ValueError):verify_certificate(x,c)
    def test_certificate_cut_sign(self):
        x=Braid.checked(4,[1,2,3]);c=singleton_certificate(x);c['cuts'][0]['letter']*=-1
        with self.assertRaises(ValueError):verify_certificate(x,c)
    def test_certificate_bad_projection(self):
        x=Braid.checked(4,[1,2,1,-2,3]);c=singleton_certificate(x);c['factors'][0]['word'].reverse()
        with self.assertRaises(ValueError):verify_certificate(x,c)
    def test_certificate_bad_interval(self):
        x=Braid.checked(4,[1,2,3]);c=singleton_certificate(x);c['factors'][0]['stop']+=1
        with self.assertRaises(ValueError):verify_certificate(x,c)
    def test_certificate_bad_schema(self):
        x=Braid.checked(1,[]);c=singleton_certificate(x);c['schema']='other'
        with self.assertRaises(ValueError):verify_certificate(x,c)
    def test_budget_is_unknown(self):
        x=Braid.checked(3,[1,2,1,-2])
        self.assertEqual(recognize(x,max_crossings=0)['status'],'UNKNOWN')
    def test_budget_not_false_negative(self):
        x=Braid.checked(3,[1,-2,1,-2])
        self.assertEqual(recognize(x,max_generators=1)['status'],'UNKNOWN')

class OracleTests(unittest.TestCase):
    def test_known_ranks(self):
        for b,w,rank in [(1,[],1),(2,[1],1),(2,[-1],1),(2,[1]*3,3),
                         (2,[-1]*3,3),(3,[1,-2]*2,5),(3,[1,2,1,-2],1)]:
            h=reduced_khovanov(Braid.checked(b,w),check_d_squared=True)
            self.assertEqual(h['reduced_rank'],rank)
    def test_known_jones(self):
        self.assertEqual(normalized_bracket(Braid.checked(3,[1,2,1,-2])),{0:1})
        self.assertEqual(normalized_bracket(Braid.checked(3,[1,-2]*2)),{8:1,4:-1,0:1,-4:-1,-8:1})
    def test_three_braid_exhaustive_four_letters(self):
        for w in itertools.product((-2,-1,1,2),repeat=4):
            try:x=Braid.checked(3,w)
            except ValueError:continue
            h=reduced_khovanov(x,check_d_squared=True)
            r=recognize(x)
            self.assertEqual(r['status']=='UNKNOT',h['reduced_rank']==1)
    def test_random_original_factor_product(self):
        for x in random_knots(160):
            fs=verify_certificate(x,singleton_certificate(x))
            h=reduced_khovanov(x,check_d_squared=True)
            product=1
            for f in fs:product*=reduced_khovanov(f,check_d_squared=True)['reduced_rank']
            self.assertEqual(h['reduced_rank'],product)
            merged=connected_sum_braid(fs)
            self.assertEqual(h['reduced_rank'],reduced_khovanov(merged)['reduced_rank'])
            self.assertEqual(normalized_bracket(x),normalized_bracket(merged))
    def test_mirror_ranks(self):
        for x in random_knots(30,seed=222):
            y=Braid.checked(x.strands,[-g for g in x.word])
            self.assertEqual(reduced_khovanov(x)['reduced_rank'],reduced_khovanov(y)['reduced_rank'])
    def test_crossing_cap(self):
        with self.assertRaises(ResourceLimit):reduced_khovanov(Braid.checked(3,[1,-2]*2),max_crossings=2)
    def test_time_cap(self):
        with self.assertRaises(ResourceLimit):reduced_khovanov(Braid.checked(3,[1,-2]*2),seconds=0)
    def test_zero_generators_cap(self):
        with self.assertRaises(ResourceLimit):reduced_khovanov(Braid.checked(1,[]),max_generators=0)

class DescentTests(unittest.TestCase):
    def test_long_right_chain(self):
        x=Braid.checked(20003,[1,2,1,-2]+list(range(3,20003)))
        y,c=linear_descent(x)
        self.assertEqual(y,Braid.checked(3,[1,2,1,-2]))
        self.assertEqual(verify_descent(x,c),y)
        self.assertLessEqual(c['queue_pops'],2*len(x.word))
    def test_left_chain(self):
        x=Braid.checked(9,list(range(1,7))+[7,8,7,-8])
        y,c=linear_descent(x)
        self.assertEqual(y.strands,3)
        self.assertEqual(verify_descent(x,c),y)
        self.assertEqual(reduced_khovanov(y)['reduced_rank'],1)
    def test_random_replay_and_ranks(self):
        for x in random_knots(100,seed=918):
            y,c=linear_descent(x,stop_strands=1)
            self.assertEqual(verify_descent(x,c),y)
            self.assertLessEqual(c['queue_pops'],2*len(x.word))
            self.assertLessEqual(y.minority,x.minority)
            self.assertLessEqual(y.canonical_genus,x.canonical_genus)
            self.assertEqual(reduced_khovanov(x)['reduced_rank'],reduced_khovanov(y)['reduced_rank'])
    def test_inverse_padding(self):
        x=Braid.checked(4,[1,2,1,-2,3,2,-2])
        y,c=linear_descent(x)
        self.assertEqual(verify_descent(x,c),y)
        self.assertEqual(len(y.word),4)
    def test_bad_move(self):
        x=Braid.checked(4,[1,2,1,-2,3]);y,c=linear_descent(x)
        c['steps'][0]['position']=0
        with self.assertRaises(ValueError):verify_descent(x,c)
    def test_bad_final(self):
        x=Braid.checked(4,[1,2,1,-2,3]);y,c=linear_descent(x)
        c['final_braid']['word'][0]*=-1
        with self.assertRaises(ValueError):verify_descent(x,c)
    def test_empty(self):
        x=Braid.checked(1,[]);y,c=linear_descent(x)
        self.assertEqual(verify_descent(x,c),x)
    def test_no_internal_destabilization(self):
        x=Braid.checked(4,[1,1,1,-3,-3,-3,2]);y,c=linear_descent(x)
        self.assertEqual(y.strands,4)
        self.assertEqual(kernelize(x)['status'],'KNOTTED')
    def test_invalid_stop(self):
        with self.assertRaises(ValueError):linear_descent(Braid.checked(1,[]),stop_strands=0)

if __name__=='__main__':unittest.main()
