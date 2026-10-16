#!/usr/bin/env python3
"""Cross-check symbolic formula semantics against independent bitset routines."""
from itertools import product
from pathlib import Path
import json, random, unittest
from syntax import evaluate, alpha_reuse, substitute, mem, all_, imp, free_vars, erase_equality
from hull_templates import hull_axioms
from finite_hulls import cols, bounded, efh, closure

class TemplateTests(unittest.TestCase):
    comparisons=0
    def test_all_structures_through_two_objects(self):
        aa=hull_axioms()
        for n in (1,2):
            for ec,rc in product(range(1<<(n*n)),repeat=2):
                self.compare(n,ec,rc,aa)
    def test_random_three_object_structures(self):
        rng=random.Random(20261015); aa=hull_axioms()
        for _ in range(300): self.compare(3,rng.randrange(512),rng.randrange(512),aa)
    def compare(self,n,ec,rc,aa):
        e,r=cols(n,ec),cols(n,rc)
        m=lambda x,y: bool(e[y]>>x&1)
        h=lambda args: bool(r[args[0]]>>args[1]&1)
        bs,bm=bounded(n,e,r,True),bounded(n,e,r,False)
        expected={'EFH':not bs or efh(n,e,r),
                  'EFH_member_only':not bm or efh(n,e,r),
                  'TC_element_seed':not bm or closure(n,e,r,False),
                  'TC_rooted':not bm or closure(n,e,r,True),
                  'SC_rooted':not bs or closure(n,e,r,True)}
        for name,want in expected.items():
            self.assertEqual(evaluate(aa[name],n,m,hole_value=h),want)
            self.assertEqual(evaluate(alpha_reuse(aa[name]),n,m,hole_value=h),want)
            TemplateTests.comparisons+=2
    def test_capture_avoiding_substitution(self):
        f=all_(1,imp(mem(0,1),mem(1,2)))
        g=substitute(f,0,1)
        self.assertEqual(free_vars(g),{1,2})
        self.assertNotEqual(g.args[0],1)
    def test_expected_template_sizes(self):
        from syntax import metrics
        aa=hull_axioms()
        self.assertEqual(metrics(aa['EFH'])['nodes'],48)
        self.assertEqual(metrics(aa['EFH'])['hole_occurrences'],3)
        self.assertEqual(metrics(aa['TC_rooted'])['nodes'],25)

if __name__=='__main__':
    suite=unittest.defaultTestLoader.loadTestsFromTestCase(TemplateTests)
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    report={'tests_run':result.testsRun,'failures':len(result.failures),
            'errors':len(result.errors),'semantic_comparisons':TemplateTests.comparisons,
            'scope':'Formula expansion and finite semantics only; no proof derivation checker.'}
    root=Path(__file__).resolve().parents[1]
    (root/'results').mkdir(exist_ok=True)
    (root/'results/template_tests.json').write_text(json.dumps(report,indent=2)+'\n')
    raise SystemExit(not result.wasSuccessful())
