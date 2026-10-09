import itertools
import random
import unittest
from fastunknot.cyclic_garside import compress, verify, Budget, LimitExceeded
from fastunknot.cyclic_garside.kernel import length_lower_bound
from fastunknot.cyclic_garside.oracles import (brute_kernel, artin_action, inverse_word,
    old_barrier,geodesic_unknot,c2c3_quotient)

class KernelTests(unittest.TestCase):
    def test_empty(self):
        for b in range(1,6):
            result=compress(b,())
            self.assertEqual(verify(b,(),result['certificate']),())

    def test_all_b3_words_through_length_four(self):
        for size in range(5):
            for w in itertools.product((1,-1,2,-2),repeat=size):
                for cyclic in (False,True):
                    r=compress(3,w,cyclic=cyclic,stop_at_lower_bound=False)
                    self.assertEqual(len(r['word']),brute_kernel(3,w,cyclic=cyclic))
                    self.assertEqual(verify(3,w,r['certificate']),tuple(r['word']))

    def test_random_oracle_comparisons(self):
        rng=random.Random(740)
        for _ in range(240):
            b=rng.randrange(2,5)
            w=tuple(rng.choice((-1,1))*rng.randrange(1,b) for _ in range(rng.randrange(9)))
            for c in (False,True):
                r=compress(b,w,cyclic=c,stop_at_lower_bound=False)
                self.assertEqual(len(r['word']),brute_kernel(b,w,cyclic=c))
                self.assertEqual(verify(b,w,r['certificate']),tuple(r['word']))
                cut=r['certificate']['rotation']
                self.assertEqual(artin_action(b,w[cut:]+w[:cut]),artin_action(b,r['word']))

    def test_safe_lower_bound_shortcut(self):
        rng=random.Random(312)
        for _ in range(300):
            b=rng.randrange(2,7)
            w=tuple(rng.choice((-1,1))*rng.randrange(1,b) for _ in range(rng.randrange(14)))
            a=compress(b,w); full=compress(b,w,stop_at_lower_bound=False)
            self.assertEqual(len(a['word']),len(full['word']))
            self.assertLessEqual(length_lower_bound(b,w),len(a['word']))

    def test_exponent_shortcut(self):
        r=compress(4,(1,2,3)*50)
        self.assertEqual(len(r['word']),150)
        self.assertEqual(r['stats']['appends'],0)

    def test_rank_two_barrier_removed(self):
        for h in (1,2,4,8,16,64):
            w=old_barrier(h);r=compress(4,w,cyclic=False)
            self.assertEqual(r['word'],[1,2,3])
            self.assertEqual(verify(4,w,r['certificate']),(1,2,3))
        for h in (1,2,3):
            w=old_barrier(h)
            self.assertEqual(brute_kernel(4,w,support_cap=2),len(w))

    def test_geodesic_unknots(self):
        for m in range(1,21):
            w=geodesic_unknot(m)
            self.assertEqual(len(c2c3_quotient(w)),4*m+1)
            self.assertEqual(len(compress(3,w,cyclic=False)['word']),2*m+2)
            r=compress(3,w)
            self.assertEqual(len(r['word']),2)
            self.assertEqual(verify(3,w,r['certificate']),tuple(r['word']))

    def test_freely_cyclically_reduced_hidden_sleeves(self):
        for m in range(2,17):
            u=(1,2,1)+(1,)*m;v=(2,1,2)+(1,)*m
            w=u+(1,2)+inverse_word(v)
            self.assertTrue(all(w[i]!=-w[(i+1)%len(w)] for i in range(len(w))))
            self.assertEqual(len(compress(3,w,cyclic=False)['word']),len(w))
            r=compress(3,w)
            self.assertEqual(len(r['word']),2)
            verify(3,w,r['certificate'])

    def test_random_conjugated_flat_inflations(self):
        rng=random.Random(981)
        for _ in range(60):
            b=rng.randrange(3,7)
            core=tuple(rng.choice((-1,1))*rng.randrange(1,b) for _ in range(6))
            inflated=[]
            for a in core:
                i=rng.randrange(1,b-1)
                identity=(i,i+1,i,-(i+1),-i,-(i+1))
                inflated.extend(identity+(a,))
            i=rng.randrange(1,b-1)
            u=(i,i+1,i);v=(i+1,i,i+1)
            w=u+tuple(inflated)+inverse_word(v)
            r=compress(b,w)
            self.assertLessEqual(len(r['word']),len(core))
            verify(b,w,r['certificate'])

    def test_rotation_equivariance_of_optimal_length(self):
        rng=random.Random(228)
        for _ in range(25):
            w=tuple(rng.choice((1,-1,2,-2,3,-3)) for _ in range(9))
            lengths={len(compress(4,w[s:]+w[:s])['word']) for s in range(len(w))}
            self.assertEqual(len(lengths),1)

    def test_linear_braid_equality(self):
        rng=random.Random(16)
        for _ in range(100):
            w=tuple(rng.choice((1,-1,2,-2,3,-3)) for _ in range(12))
            r=compress(4,w,cyclic=False)
            self.assertEqual(artin_action(4,w),artin_action(4,r['word']))

    def test_cooperative_limit_is_not_a_verdict(self):
        for bad in (-1, True, 1.5):
            with self.assertRaises(ValueError):
                Budget(max_ticks=bad)
        with self.assertRaises(LimitExceeded):
            compress(4,old_barrier(1),budget=Budget(max_ticks=0))
