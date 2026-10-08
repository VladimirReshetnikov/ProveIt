import copy
import itertools
import random
import unittest
from cyclic_garside import compress, compress_radius, verify_radius, LimitExceeded
from cyclic_garside.verify import CertificateError
from cyclic_garside.normalform import normal_form
from cyclic_garside.oracles import artin_action, inverse_word


def rectangular_unknot(m):
    return (-1,)*m+(3,)*m+(1,)*(m+1)+(-3,)*(m-1)+(2,)


def brute_radius(b, word, radius, cyclic):
    alphabet = tuple(a for i in range(1,b) for a in (i,-i))
    target_actions = [(artin_action(b,v),len(v)) for d in range(radius+1)
                      for v in itertools.product(alphabet,repeat=d)]
    best = len(word)
    for cut in range(len(word) if cyclic and word else 1):
        w = word[cut:]+word[:cut]
        dp = list(range(len(w)+1))
        for j in range(1,len(w)+1):
            dp[j] = dp[j-1]+1
            for i in range(j):
                action = artin_action(b,w[i:j])
                for image,cost in target_actions:
                    if action == image:
                        dp[j] = min(dp[j],dp[i]+cost)
        best = min(best,dp[-1])
    return best


class RadiusTests(unittest.TestCase):
    def test_radius_one_agrees(self):
        rng = random.Random(115)
        for _ in range(150):
            b = rng.randrange(2,6)
            w = tuple(rng.choice((-1,1))*rng.randrange(1,b) for _ in range(rng.randrange(11)))
            for c in (False,True):
                a = compress(b,w,cyclic=c,stop_at_lower_bound=False)
                r = compress_radius(b,w,radius=1,cyclic=c,stop_at_lower_bound=False)
                self.assertEqual(len(a['word']),len(r['word']))
                self.assertEqual(verify_radius(b,w,r['certificate']),tuple(r['word']))

    def test_all_b3_words_through_three(self):
        for n in range(4):
            for w in itertools.product((1,-1,2,-2),repeat=n):
                for c in (False,True):
                    r = compress_radius(3,w,radius=2,cyclic=c,stop_at_lower_bound=False)
                    self.assertEqual(len(r['word']),brute_radius(3,w,2,c))
                    verify_radius(3,w,r['certificate'])

    def test_random_independent_optima(self):
        rng = random.Random(972)
        for _ in range(90):
            b = rng.randrange(2,5)
            w = tuple(rng.choice((-1,1))*rng.randrange(1,b) for _ in range(rng.randrange(8)))
            for c in (False,True):
                r = compress_radius(b,w,radius=2,cyclic=c,stop_at_lower_bound=False)
                self.assertEqual(len(r['word']),brute_radius(b,w,2,c))
                verify_radius(b,w,r['certificate'])

    def test_infinite_rectangular_barrier(self):
        for m in range(2,17):
            w = rectangular_unknot(m)
            self.assertEqual(normal_form(4,w)[0],normal_form(4,(1,3,2))[0])
            one = compress(4,w)
            two = compress_radius(4,w,radius=2)
            self.assertEqual(len(one['word']),4*m+1)
            self.assertEqual(len(two['word']),3)
            self.assertEqual(verify_radius(4,w,two['certificate']),tuple(two['word']))

    def test_small_fixed_point(self):
        w = (2,-1,2,1)
        self.assertEqual(len(compress(3,w)['word']),4)
        self.assertEqual(len(compress_radius(3,w,radius=2)['word']),2)
        u = (-1,-2)
        self.assertEqual(artin_action(3,w),artin_action(3,u+(1,2)+inverse_word(u)))

    def test_exact_trie_append_count(self):
        w = rectangular_unknot(3)
        for radius in (1,2,3):
            r = compress_radius(4,w,radius=radius,stop_at_lower_bound=False)
            self.assertEqual(r['stats']['trie_nodes'],sum(6**d for d in range(radius+1)))
            self.assertEqual(r['stats']['algebra_appends_before_proof'],2*len(w)*r['stats']['trie_nodes'])

    def test_budgets_and_invalid_radius(self):
        with self.assertRaises(LimitExceeded):
            compress_radius(4,rectangular_unknot(2),max_targets=2)
        for radius in (0,-1,True,1.5):
            with self.assertRaises(ValueError):
                compress_radius(4,rectangular_unknot(2),radius=radius)

    def test_malformed_certificate(self):
        w = rectangular_unknot(2)
        original = compress_radius(4,w)['certificate']
        for field,value in [('target_radius',True),('rotation',len(w)),('input_digest','bad'),('output',[True])]:
            bad = copy.deepcopy(original);bad[field]=value
            with self.assertRaises(CertificateError):
                verify_radius(4,w,bad)
        bad = copy.deepcopy(original);bad['replacements'][0]['target']=[1,1]
        with self.assertRaises(CertificateError):
            verify_radius(4,w,bad)
        bad = copy.deepcopy(original);bad['replacements'][0]['proof'].pop()
        with self.assertRaises(CertificateError):
            verify_radius(4,w,bad)

    def test_empty_and_positive_shortcuts(self):
        for b in range(1,6):
            r = compress_radius(b,(),radius=2)
            self.assertEqual(verify_radius(b,(),r['certificate']),())
        r = compress_radius(4,(1,2,3)*3)
        self.assertEqual(r['stats']['appends'],0)

    def test_random_linear_equality_and_cap(self):
        rng = random.Random(255)
        for _ in range(100):
            b = 4
            w = tuple(rng.choice((1,-1,2,-2,3,-3)) for _ in range(10))
            r = compress_radius(b,w,cyclic=False)
            self.assertEqual(artin_action(b,w),artin_action(b,r['word']))
            full = compress_radius(b,w,cyclic=False,stop_at_lower_bound=False)
            self.assertEqual(len(full['word']),len(r['word']))
            verify_radius(b,w,r['certificate'])
