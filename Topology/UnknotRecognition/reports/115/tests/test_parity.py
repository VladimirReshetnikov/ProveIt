import itertools
import unittest
from activation_forest import Instance
from experiments.fixtures import repository_loop,parallel_obstruction,choice_arms
from integration.parity_audit import exact_parity_defects,saturated_parity_completion

class ParityTests(unittest.TestCase):
    def test_native_loop(self): self.assertEqual(exact_parity_defects(repository_loop()),[])
    def test_even_parallel(self): self.assertEqual(exact_parity_defects(parallel_obstruction(6)),[])
    def test_odd_parallel(self): self.assertTrue(exact_parity_defects(parallel_obstruction(5)))
    def test_odd_parallel_no_lift(self): self.assertFalse(saturated_parity_completion(parallel_obstruction(5))['possible'])
    def test_choice_family_exact(self):
        for g in range(1,7): self.assertEqual(exact_parity_defects(choice_arms(g)),[])
    def test_lift_does_not_preserve_exact_count(self):
        x=Instance(2,((0,1),(0,1)),((1,),(2,)),1)
        self.assertTrue(exact_parity_defects(x));self.assertTrue(saturated_parity_completion(x)['possible'])
    def test_exhaustive_lift_criterion(self):
        edges=((0,1),(1,2),(0,2),(0,0))
        for weights in itertools.product((0,1,2),repeat=4):
            x=Instance(3,edges,tuple((w,) for w in weights),1)
            heavy=[i for i,w in enumerate(weights) if w==2]
            exists=False
            for choices in itertools.product((2,3),repeat=len(heavy)):
                lifted=list(weights)
                for e,w in zip(heavy,choices):lifted[e]=w
                y=Instance(3,edges,tuple((w,) for w in lifted),1)
                exists |= not exact_parity_defects(y)
            self.assertEqual(saturated_parity_completion(x)['possible'],exists)
    def test_constructed_lifts(self):
        for g in range(1,7):
            x=choice_arms(g);ans=saturated_parity_completion(x)
            self.assertTrue(ans['possible'])
            rows=[list(row) for row in x.matrix]
            for h,odd in enumerate(ans['odd_heavy_rows_by_column']):
                for e in range(x.m):
                    if rows[e][h]>=2: rows[e][h]=3 if e in odd else 2
            y=Instance(x.vertices,x.edges,tuple(tuple(row) for row in rows),x.columns)
            self.assertEqual(exact_parity_defects(y),[])

if __name__=='__main__':unittest.main()
