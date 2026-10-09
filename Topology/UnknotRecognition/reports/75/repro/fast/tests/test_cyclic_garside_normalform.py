import itertools
import random
import unittest
from fastunknot.cyclic_garside.normalform import (IDENTITY, Counters, normal_form, is_normal,
                                      expand_state, simple_word)
from fastunknot.cyclic_garside.oracles import artin_action, inverse_word

class NormalFormTests(unittest.TestCase):
    def test_identity_and_two_strands(self):
        self.assertEqual(normal_form(1, ())[0], IDENTITY)
        for n in range(-20, 21):
            word = (1,) * n if n >= 0 else (-1,) * -n
            self.assertEqual(normal_form(2, word)[0], (n, ()))

    def test_input_validation(self):
        for b,w in [(0,()), (True,()), (3,(0,)), (3,(3,)), (3,(1.0,)), (3,(True,)), (1,(1,))]:
            with self.subTest(b=b,w=w), self.assertRaises(ValueError):
                normal_form(b,w)

    def test_signed_inverses(self):
        rng = random.Random(19)
        for _ in range(300):
            b = rng.randrange(2,8)
            w = tuple(rng.choice((-1,1))*rng.randrange(1,b) for _ in range(20))
            self.assertEqual(normal_form(b,w+inverse_word(w))[0],IDENTITY)

    def test_defining_relations_in_context(self):
        rng = random.Random(271)
        for _ in range(600):
            b = rng.randrange(3,9)
            prefix = tuple(rng.choice((-1,1))*rng.randrange(1,b) for _ in range(5))
            suffix = tuple(rng.choice((-1,1))*rng.randrange(1,b) for _ in range(5))
            i = rng.randrange(1,b-1)
            for a,c in [((i,i+1,i),(i+1,i,i+1)), ((i,-i),())]:
                self.assertEqual(normal_form(b,prefix+a+suffix)[0],
                                 normal_form(b,prefix+c+suffix)[0])
            if b>3:
                self.assertEqual(normal_form(b,prefix+(1,b-1)+suffix)[0],
                                 normal_form(b,prefix+(b-1,1)+suffix)[0])

    def test_all_simple_permutations_through_six_strands(self):
        for b in range(2,7):
            unit=tuple(range(b)); delta=unit[::-1]
            for p in itertools.permutations(unit):
                expected = IDENTITY if p==unit else (1,()) if p==delta else (0,(p,))
                self.assertEqual(normal_form(b,simple_word(p))[0],expected)

    def test_exhaustive_faithful_action_tables(self):
        # 5,461 B3 words and 1,555 B4 words: all collisions checked both ways.
        for b,max_length in [(3,6),(4,4)]:
            alphabet=tuple(a for i in range(1,b) for a in (i,-i))
            by_nf,by_action={},{}
            for size in range(max_length+1):
                for word in itertools.product(alphabet,repeat=size):
                    nf=normal_form(b,word)[0]; action=artin_action(b,word)
                    self.assertEqual(by_nf.setdefault(nf,action),action)
                    self.assertEqual(by_action.setdefault(action,nf),nf)
                    self.assertTrue(is_normal(b,nf))

    def test_independent_expansion_action(self):
        rng=random.Random(731)
        for _ in range(500):
            b=rng.randrange(2,7)
            w=tuple(rng.choice((-1,1))*rng.randrange(1,b) for _ in range(rng.randrange(16)))
            nf=normal_form(b,w)[0]
            self.assertEqual(artin_action(b,w),artin_action(b,expand_state(b,nf)))

    def test_amortized_transfer_bound(self):
        rng=random.Random(124)
        for _ in range(100):
            b=rng.randrange(2,10);n=rng.randrange(1,50)
            word=tuple(rng.choice((-1,1))*rng.randrange(1,b) for _ in range(n))
            c=Counters();normal_form(b,word,counters=c)
            self.assertLessEqual(c.transfers,(b*(b-1)//2)*n*(n-1)//2)
            self.assertLessEqual(c.peak_factors,n)

    def test_permutation_and_conjugacy_are_not_equality(self):
        self.assertNotEqual(normal_form(4,(1,1))[0],IDENTITY)
        self.assertNotEqual(normal_form(3,(1,))[0],normal_form(3,(2,))[0])
        self.assertNotEqual(normal_form(3,(1,2)*3)[0],IDENTITY)
