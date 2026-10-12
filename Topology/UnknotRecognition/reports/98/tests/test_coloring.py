import copy,random,unittest
from gauge_cuts import compile_grammar,extract_cut_addresses
from checker import verify_coloring_recipe,VerificationError
from coloring import build_recipe,color_at
from fixtures import random_grammar,prism,hidden_power,component_fan

class ColoringTests(unittest.TestCase):
    def test_all_random_rows(self):
        rng=random.Random(997)
        for _ in range(70):
            g=random_grammar(rng);p=compile_grammar(g)
            for ri,row in enumerate(p['atlases'][-1]['rows']):
                recipe=build_recipe(p,ri);verify_coloring_recipe(recipe,g)
                for addr in extract_cut_addresses(p,ri):
                    node=len(g['nodes'])-1
                    for branch in addr['path']:node=g['nodes'][node]['children'][branch]
                    u,v,_=g['nodes'][node]['edges'][addr['leaf_edge']]
                    self.assertNotEqual(color_at(recipe,addr['path'],u),color_at(recipe,addr['path'],v))
    def test_huge_reuse(self):
        g=hidden_power(256);p=compile_grammar(g)
        ri=next(i for i,r in enumerate(p['atlases'][-1]['rows']) if r[3]==3 and r[0]==0)
        w=build_recipe(p,ri);verify_coloring_recipe(w,g)
        self.assertLessEqual(len(w['records']),sum(len(a['rows']) for a in p['atlases']))
    def test_all_root_assignments(self):
        g=component_fan(8,retain=True);p=compile_grammar(g);w=build_recipe(p,0);verify_coloring_recipe(w,g)
        # Last branch-1 occurrence is the eighth independent edge.
        for mask in range(256):
            bits=[(mask>>j)&1 for j in range(8)]
            self.assertEqual(color_at(w,[1],0,bits),bits[-1])
            self.assertEqual(color_at(w,[1],1,bits),bits[-1])
    def test_tampered_symbolic_leaf(self):
        g=prism();p=compile_grammar(g);ri=next(i for i,r in enumerate(p['atlases'][-1]['rows']) if r[3]==3)
        w=build_recipe(p,ri);w['records'][0]['colors'][0][1]^=1
        with self.assertRaises(VerificationError):verify_coloring_recipe(w,g)
    def test_tampered_transport(self):
        g=component_fan(3);p=compile_grammar(g);w=build_recipe(p,0)
        w['records'][-1]['transports'][0][0][1]^=1
        with self.assertRaises(VerificationError):verify_coloring_recipe(w,g)

class MarkTests(unittest.TestCase):
    def test_both_mark_addresses(self):
        from coloring import mark_address
        for g in (prism(),hidden_power(128)):
            p=compile_grammar(g);ri=next(i for i,r in enumerate(p['atlases'][-1]['rows']) if r[3]==3)
            rec=build_recipe(p,ri);verify_coloring_recipe(rec,g)
            for b in (0,1):
                addr=mark_address(rec,b);node=len(g['nodes'])-1
                for ch in addr['path']:node=g['nodes'][node]['children'][ch]
                u,v,_=g['nodes'][node]['edges'][addr['leaf_edge']]
                self.assertEqual(color_at(rec,addr['path'],u),b);self.assertEqual(color_at(rec,addr['path'],v),b)
    def test_absent_mark(self):
        from coloring import mark_address
        g=component_fan(2);p=compile_grammar(g);rec=build_recipe(p,0)
        with self.assertRaises(ValueError):mark_address(rec,1)

if __name__ == "__main__":
    unittest.main()
