import itertools,math,random,unittest
from portkh import gf2
from portkh.languages import Language,fixed_weight,mask_register,analyze_restricted
from portkh.complexes import coupled_pair,PortComplex,TemplateBlock,expand
from test_portkh import random_two_term,random_register,elementary_rank

class Languages(unittest.TestCase):
    def test_counts_and_acceptance(self):
        for m in range(9):
            for k in range(m+1):
                language=fixed_weight(m,k)
                self.assertEqual(language.count(),math.comb(m,k))
                for word in itertools.product((0,1),repeat=m):
                    self.assertEqual(language.accepts(word),sum(word)==k)

    def test_masked_register(self):
        rng=random.Random(325)
        for _ in range(40):
            m=rng.randrange(6);k=rng.randrange(m+1)
            reg=random_register(rng,m,4,7);language=fixed_weight(m,k)
            masked=mask_register(reg,language)
            for word in itertools.product((0,1),repeat=m):
                self.assertEqual(masked.evaluate(word),reg.evaluate(word) if sum(word)==k else 0)

    def test_restricted_dense_comparison(self):
        rng=random.Random(2244)
        for _ in range(70):
            m=rng.randrange(5);k=rng.randrange(m+1)
            c=random_two_term(rng,m=m,r=rng.randrange(4),blocks=rng.randrange(1,3))
            languages=tuple(fixed_weight(m,k) for _ in c.blocks)
            ans=analyze_restricted(c,languages)
            rows,_=expand(c);keep=[];offset=0
            for b in c.blocks:
                for t in range(b.size):
                    keep.extend(offset+t*(1<<m)+x for x in range(1<<m) if x.bit_count()==k)
                offset+=b.size*(1<<m)
            restricted=[sum(((rows[i]>>j)&1) << s for s,j in enumerate(keep)) for i in keep]
            self.assertEqual(ans['homology_dimension'],len(keep)-2*elementary_rank(restricted,len(keep)))

    def test_binomial_resonance(self):
        for m,k in [(0,0),(5,2),(7,3),(8,4),(40,20),(63,31),(64,32),(127,63)]:
            c=coupled_pair(m,'invertible')
            ans=analyze_restricted(c,(fixed_weight(m,k),))
            self.assertEqual(ans['dimension'],2*math.comb(m,k))
            self.assertEqual(ans['homology_dimension'],2*(math.comb(m,k)%2))
            self.assertEqual(math.comb(m,k)%2,int(k & ~m == 0))

    def test_avoid_premature_saturation(self):
        # A=0 and only one accepted word: full-word masked model has enormous
        # uncoupled complement, but the restricted differential is a single unit.
        c=coupled_pair(40,'large_homology')
        ans=analyze_restricted(c,(fixed_weight(40,0),))
        self.assertEqual(ans['dimension'],2)
        self.assertEqual(ans['homology_dimension'],0)
        self.assertFalse(ans['rank_two_obstruction_from_budget'])

    def test_invalid_language(self):
        with self.assertRaises(ValueError):fixed_weight(3,4)
        with self.assertRaises(ValueError):Language((1,),(),2,(0,))
        with self.assertRaises(ValueError):Language((1,),(),0,(0,0))
        with self.assertRaises(ValueError):mask_register(coupled_pair(3).blocks[0].register,fixed_weight(4,1))

    def test_roundtrip(self):
        a=fixed_weight(7,3);self.assertEqual(Language.from_dict(a.to_dict()),a)
