import unittest, copy, random
from itertools import product
from collections import Counter
from whitehead_exposure.algebra import *
from whitehead_exposure.flow import minimum_pinned_cut, verify_pinned_cut
from whitehead_exposure.selector import *
from whitehead_exposure.slp import *
from whitehead_exposure.engine import *
from whitehead_exposure.braid import *
from helpers import all_moves, literal_oracle, random_word, barrier

class WordTests(unittest.TestCase):
    def test_cyclic_normalization(self):
        self.assertEqual(cyclic_reduce([1,2,3,-2,-1]),(3,))
    def test_invalid_boolean_letter(self):
        with self.assertRaises(ValueError): validate_words([(True,)], [1])
    def test_unreduced_input(self):
        with self.assertRaises(ValueError): validate_words([(1,-1)], [1])
    def test_duplicate_alive(self):
        with self.assertRaises(ValueError): validate_words([], [1,1])
    def test_gap_formula_small(self):
        for w in ((1,), (1,1), (1,2,-1,2),(1,2,-1,-2),(1,1,2,1,2)):
            G=word_graph(w)
            for a,S in all_moves([1,2]):
                z=cyclic_reduce(y for x in w for y in whitehead_image(x,a,S))
                self.assertEqual(sum(abs(x)==abs(a) for x in z),cut_capacity(G,S))
                self.assertEqual(Counter(abs(x) for x in z if abs(x)!=abs(a)),
                                 Counter(abs(x) for x in w if abs(x)!=abs(a)))
    def test_negative_pivot(self):
        self.assertEqual(eliminate([(-1,2,2),(1,-2,-2)],0,1,Budget(),100),[(),()])

class FlowTests(unittest.TestCase):
    def test_forced(self):
        G={(0,1):7}; p=minimum_pinned_cut(G,(0,1),{0},{1},Budget())
        self.assertEqual(p['capacity'],7)
        self.assertTrue(verify_pinned_cut(G,(0,1),{0},{1},p))
    def test_conflicting(self):
        self.assertIsNone(minimum_pinned_cut({},(0,),{0},{0},Budget()))
    def test_large_capacities(self):
        a=2**2000; G={(0,1):a,(1,2):a+1}
        p=minimum_pinned_cut(G,(0,1,2),{0},{2},Budget())
        self.assertEqual(p['capacity'],a)
        self.assertTrue(verify_pinned_cut(G,(0,1,2),{0},{2},p))
    def test_random_bruteforce(self):
        rng=random.Random(145)
        for _ in range(150):
            n=rng.randint(2,7); V=tuple(range(n))
            G={(i,j):rng.randint(1,20) for i in V for j in V if i<j and rng.random()<.6}
            p=minimum_pinned_cut(G,V,{0},{n-1},Budget())
            optimum=min(cut_capacity(G,{0}|{v for v in V[1:-1] if mask>>(v-1)&1}) for mask in range(1<<(n-2)))
            self.assertEqual(p['capacity'],optimum)
            self.assertTrue(verify_pinned_cut(G,V,{0},{n-1},p))
    def test_flow_tamper(self):
        G={(0,1):3,(1,2):5}; p=minimum_pinned_cut(G,(0,1,2),{0},{2},Budget())
        p['flow'][0][2]+=1
        self.assertFalse(verify_pinned_cut(G,(0,1,2),{0},{2},p))
    def test_shore_tamper(self):
        G={(0,1):3,(1,2):5}; p=minimum_pinned_cut(G,(0,1,2),{0},{2},Budget())
        p['shore']=[0,2]
        self.assertFalse(verify_pinned_cut(G,(0,1,2),{0},{2},p))
    def test_boolean_capacity_tamper(self):
        G={(0,1):1}; p=minimum_pinned_cut(G,(0,1),{0},{1},Budget()); p['capacity']=True
        self.assertFalse(verify_pinned_cut(G,(0,1),{0},{1},p))

class SelectorTests(unittest.TestCase):
    def test_unit_bridge(self):
        self.assertEqual(unit_bridges({(-2,1):2,(-1,2):2,(-1,1):1},(-2,-1,1,2)),[(-1,1)])
    def test_parallel_edge_not_unit_bridge(self):
        self.assertEqual(unit_bridges({(-1,1):2},(-1,1)),[])
    def test_cycle_not_bridge(self):
        self.assertEqual(unit_bridges({(0,1):1,(1,2):1,(0,2):1},(0,1,2)),[])
    def test_barrier_exact_bounds(self):
        for m in (1,2,5,17):
            p=find_exposure(barrier(m),[1,2])
            self.assertEqual((p['allocation_bound'],p['length_change'],p['target_after']),(34*m,2*m-2,3))
            self.assertTrue(verify_exposure_graphs([word_graph(w) for w in barrier(m)],(1,2),p))
    def test_connected_no_flow(self):
        stats={}; find_exposure(barrier(2),[1,2],stats=stats)
        self.assertEqual(stats['flows'],0)
        self.assertGreater(stats['forced'],0)
    def test_disconnected_completeness(self):
        W=barrier(2)+[(3,3,4,3,4,2,3,4)]
        p=find_exposure(W,[1,2,3,4])
        self.assertEqual((p['allocation_bound'],p['length_change']),literal_oracle(W,[1,2,3,4]))
    def test_random_literal_oracle(self):
        rng=random.Random(54)
        for _ in range(70):
            r=rng.choice((2,3)); W=[random_word(rng,r,rng.randint(1,14)) for _ in range(rng.randint(1,4))]
            for obj in ('allocation','length'):
                p=find_exposure(W,list(range(1,r+1)),objective=obj)
                got=None if p is None else ((p['allocation_bound'],p['length_change']) if obj=='allocation' else (p['length_change'],p['allocation_bound']))
                self.assertEqual(got,literal_oracle(W,list(range(1,r+1)),obj))
    def test_primitive_blindspot(self):
        w=(1,1,2,1,1,2,1,2)
        self.assertIsNone(find_exposure([w],[1,2]))
        self.assertLess(strict_whitehead([w],[1,2],Budget())[0],0)
    def test_proper_powers(self):
        self.assertIsNone(find_exposure([(1,1),(1,1,1)],[1,2]))
    def test_affordability(self):
        self.assertIsNone(find_exposure(barrier(2),[1,2],max_after=67))
        self.assertIsNotNone(find_exposure(barrier(2),[1,2],max_after=68))
    def test_increase_cap(self):
        self.assertIsNone(find_exposure(barrier(2),[1,2],max_increase=1))
    def test_tamper_witness(self):
        W=barrier(2); G=[word_graph(w) for w in W]; p=find_exposure(W,[1,2])
        for field in ('cut_capacity','length_change','target_after','allocation_bound'):
            q=copy.deepcopy(p); q[field]+=1
            self.assertFalse(verify_exposure_graphs(G,(1,2),q))
    def test_boolean_bridge_tamper(self):
        W=barrier(2); p=find_exposure(W,[1,2]); p['bridge']=[-1,True]
        self.assertFalse(verify_exposure_graphs([word_graph(w) for w in W],(1,2),p))
    def test_graph_degree_validation(self):
        with self.assertRaises(ValueError): exposure_from_graphs([{(-1,2):1}],(1,2))

class GrammarTests(unittest.TestCase):
    def test_literal_graph_agreement(self):
        W=barrier(7); g=grammar_from_words(W,[1,2])
        self.assertEqual(grammar_graphs(g),[word_graph(w) for w in W])
    def test_huge_power_and_fused_replay(self):
        g=barrier_grammar(1000); G=grammar_graphs(g); p=exposure_from_graphs(G,(1,2))
        self.assertEqual(sum(sum(h.values()) for h in G),20*2**1000+5)
        self.assertTrue(verify_fused_exposure(g,{k:p[k] for k in ('relation','multiplier','subset')},cap=100))
    def test_grammar_cycle_rejected(self):
        with self.assertRaises(ValueError): summarize({'alive':[1],'nodes':[['concat',0,0]],'roots':[0]})
    def test_grammar_unreduced_rejected(self):
        with self.assertRaises(ValueError): summarize(grammar_from_words([(1,-1)],[1]))
    def test_boolean_terminal_rejected(self):
        g=grammar_from_words([(1,)],[1]); g['nodes'][1][1]=True
        with self.assertRaises(ValueError): summarize(g)
    def test_bad_root_rejected(self):
        g=barrier_grammar(1); g['roots']=[True]
        with self.assertRaises(ValueError): summarize(g)
    def test_bounded_evaluation_exhaustion(self):
        with self.assertRaises(ResourceLimit): image_values(barrier_grammar(10),{},cap=100)
    def test_fused_tamper(self):
        self.assertFalse(verify_fused_exposure(barrier_grammar(10),{'relation':1,'multiplier':-1,'subset':[-1,2]},cap=100000))

class EngineTests(unittest.TestCase):
    def test_strict_barrier_and_exposure_success(self):
        for m in (1,2,8):
            self.assertEqual(search_presentation(barrier(m),[1,2],mode='strict')['status'],'INCONCLUSIVE')
            x=search_presentation(barrier(m),[1,2]); self.assertEqual(x['status'],'FREE_RANK_ONE')
            self.assertEqual(len(x['moves']),2); self.assertTrue(verify_presentation_trace(x))
    def test_direct_generator(self):
        self.assertEqual(search_presentation([(1,2),(1,2)],[1,2])['status'],'FREE_RANK_ONE')
    def test_nonfree_rank_one(self):
        self.assertEqual(search_presentation([(1,1)],[1])['status'],'INCONCLUSIVE')
    def test_work_exhaustion_inconclusive(self):
        self.assertEqual(search_presentation(barrier(2),[1,2],max_work=0)['status'],'INCONCLUSIVE')
    def test_letter_exhaustion_inconclusive(self):
        self.assertEqual(search_presentation(barrier(2),[1,2],max_letters=44)['status'],'INCONCLUSIVE')
    def test_tampered_elimination(self):
        p=search_presentation(barrier(2),[1,2]); p['moves'][-1]['relation']=1
        self.assertFalse(verify_presentation_trace(p))
    def test_tampered_alive(self):
        p=search_presentation(barrier(2),[1,2]); p['remaining_generator']=1
        self.assertFalse(verify_presentation_trace(p))
    def test_external_cancellation_propagates(self):
        def cancel(): raise KeyboardInterrupt()
        with self.assertRaises(KeyboardInterrupt): search_presentation(barrier(2),[1,2],check=cancel)

class BraidTests(unittest.TestCase):
    def test_crossingless(self):
        self.assertEqual(recognize_braid(1,[])['status'],'UNKNOT')
    def test_positive_and_negative_stabilization(self):
        for s in range(2,8):
            for sign in (-1,1):
                c=recognize_braid(s,[sign*i for i in range(1,s)])
                self.assertEqual(c['status'],'UNKNOT'); self.assertTrue(verify_braid_certificate(c))
    def test_trefoil_and_figure_eight_not_accepted(self):
        self.assertEqual(recognize_braid(2,[1,1,1])['status'],'INCONCLUSIVE')
        self.assertEqual(recognize_braid(3,[1,-2,1,-2])['status'],'INCONCLUSIVE')
    def test_multicomponent_refused(self):
        self.assertEqual(recognize_braid(2,[1,1])['status'],'INCONCLUSIVE')
    def test_braid_tampering(self):
        c=recognize_braid(2,[1]); c['braid']=[1,1,1]
        self.assertFalse(verify_braid_certificate(c))
    def test_boolean_braid_refused(self):
        with self.assertRaises(ValueError): recognize_braid(2,[True])

if __name__=='__main__': unittest.main()
