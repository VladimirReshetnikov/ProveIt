import random
import unittest
from cyclic_garside import preprocess, normal_form_candidate, compress, compress_radius, verify, verify_radius
from cyclic_garside.oracles import artin_action, old_barrier

class PortfolioTests(unittest.TestCase):
    def test_shortcut_families(self):
        for m in (2,8,32):
            word=(-1,)*m+(3,)*m+(1,)*(m+1)+(-3,)*(m-1)+(2,)
            out=preprocess(4,word,radius=2)
            self.assertEqual(len(out['word']),3)
            self.assertTrue(out['stats']['portfolio_shortcut'])
            verify_radius(4,word,out['certificate'])
        out=preprocess(4,old_barrier(12))
        self.assertEqual(out['word'],[1,2,3])
        self.assertTrue(out['stats']['portfolio_shortcut'])

    def test_random_soundness_and_dominance(self):
        rng=random.Random(355)
        for _ in range(120):
            b=rng.randrange(2,6)
            word=tuple(rng.choice((-1,1))*rng.randrange(1,b) for _ in range(rng.randrange(13)))
            direct=normal_form_candidate(b,word)
            self.assertEqual(artin_action(b,word),artin_action(b,direct['word']))
            for radius in (1,2):
                out=preprocess(b,word,radius=radius)
                kernel=compress(b,word) if radius==1 else compress_radius(b,word,radius=2)
                self.assertLessEqual(len(out['word']),len(kernel['word']))
                checker=verify if out['certificate']['schema'].endswith('v1') else verify_radius
                checker(b,word,out['certificate'])

    def test_positive_and_empty(self):
        for b in range(1,6):
            out=preprocess(b,())
            self.assertEqual(out['word'],[])
            self.assertTrue(out['stats']['portfolio_shortcut'])
        out=preprocess(4,(1,2,3)*3)
        self.assertEqual(out['stats']['appends'],0)
