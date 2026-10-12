import copy
import random
import unittest
from unittest.mock import patch
from pattern_kernel import *
from pattern_kernel.core import (natural, certify_cubic_graph, source_digest,
                                  chain_payload, Graph)
from pattern_kernel.signatures import tile_table, multiply, power, closure_cost
from pattern_kernel.verify import verify_source_witness


def brute_cut(g):
    best = 4
    for mask in range(1 << g.n):
        cost = 0; flags = 0
        for a, b in g.edges:
            ca, cb = (mask >> a) & 1, (mask >> b) & 1
            if ca != cb:
                cost += 1
            else:
                flags |= 1 << ca
        if flags == 3:
            best = min(best, cost)
    return best


class ModelTests(unittest.TestCase):
    def test_bad_ports(self):
        with self.assertRaises(ValueError):
            Tile(2, ((0, 1),), (0,), (0,))
    def test_bad_edge(self):
        with self.assertRaises(ValueError):
            Tile(2, ((0, 2),), (0,), (1,))
    def test_zero_exponent(self):
        with self.assertRaises(ValueError):
            Block(prism_tile(), 0)
    def test_bool_exponent(self):
        with self.assertRaises(ValueError):
            natural(True)
    def test_hex_integer(self):
        self.assertEqual(natural('0x10000000000000001'), 2**64 + 1)
    def test_non_cubic(self):
        with self.assertRaises(ValueError):
            solve((Block(Tile(2, ((0,1),), (0,), (1,)), 7),))
    def test_disconnected_cap_rejected(self):
        t = Tile(4, ((0,3),(1,2)), (0,1), (2,3))
        with self.assertRaises(ValueError):
            kernelize((Block(t, 100),))
    def test_small_disconnected_not_capped(self):
        t = Tile(4, ((0,3),(1,2)), (0,1), (2,3))
        self.assertEqual(kernelize((Block(t, 3),))[0][0].copies, 3)
    def test_expansion_cap(self):
        with self.assertRaises(ValueError):
            expand((Block(prism_tile(), 2**4096),))
    def test_loop_degree_two(self):
        self.assertTrue(Graph(2, ((0,0),(1,1),(0,1))).cubic())


class SignatureTests(unittest.TestCase):
    def test_prism_exponents(self):
        table = tile_table(prism_tile())
        for n in range(1, 16):
            self.assertEqual(power(table, n), power(table, min(n, 4)))
    def test_threshold_one_sharp_three(self):
        t = Tile(2, ((0,1),), (0,), (1,))
        a = tile_table(t,1)
        self.assertNotEqual(power(a,2,1),power(a,3,1))
        self.assertEqual(power(a,3,1),power(a,15,1))
    def test_disconnected_parity_counterexample(self):
        t = Tile(4, ((0,3),(1,2)), (0,1), (2,3))
        a = tile_table(t)
        self.assertNotEqual(power(a,5),power(a,6))
    def test_permutation_zero_period(self):
        t = Tile(4, ((0,3),(1,2)), (0,1), (2,3))
        a = tile_table(t); h=2; k=3; threshold=k+(k+1)*h
        for n in range(threshold, 25):
            self.assertEqual(power(a,n),power(a,threshold+(n-threshold)%h))
    def test_random_connected_signatures(self):
        rng = random.Random(20261012)
        for _ in range(30):
            n = rng.randint(4,7); w=rng.randint(1,2)
            edges=[(i,rng.randrange(i)) for i in range(1,n)]
            edges += [(rng.randrange(n),rng.randrange(n)) for _ in range(rng.randrange(5))]
            t=Tile(n,tuple(edges),tuple(range(w)),tuple(range(w,2*w)))
            for k in (0,1,2,3,4):
                a=tile_table(t,k); current=a; fixed=power(a,k+2,k)
                for exponent in range(1,k+7):
                    if exponent >= k+2:
                        self.assertEqual(current,fixed)
                    current=multiply(current,a,k)
    def test_associativity(self):
        a=tile_table(prism_tile()); b=tile_table(triangle_expansion_tile())
        self.assertEqual(multiply(multiply(a,b),a),multiply(a,multiply(b,a)))


class TopologyGraphTests(unittest.TestCase):
    def test_prism_family(self):
        for n in range(1,11):
            c=(Block(prism_tile(),n),);r=solve(c)
            expected='LOW_CYCLIC_CUT' if n<=3 else 'NO_LOW_CYCLIC_CUT'
            self.assertEqual(r['graph_proof']['verdict'],expected)
            self.assertTrue(verify_result(c,r))
    def test_small_bruteforce(self):
        for n in range(1,7):
            c=(Block(prism_tile(),n),);g,_=expand(c);r=solve(c)
            self.assertEqual(brute_cut(g)<=3,r['graph_proof']['verdict']=='LOW_CYCLIC_CUT')
    def test_k4(self):
        g=Graph(4,tuple((i,j) for i in range(4) for j in range(i+1,4)))
        self.assertEqual(certify_cubic_graph(g)['verdict'],'NO_LOW_CYCLIC_CUT')
        self.assertEqual(brute_cut(g),4)
    def test_theta(self):
        g=Graph(2,((0,1),(0,1),(0,1)))
        self.assertEqual(certify_cubic_graph(g)['verdict'],'NO_LOW_CYCLIC_CUT')
    def test_dumbbell(self):
        g=Graph(2,((0,0),(1,1),(0,1)))
        r=certify_cubic_graph(g)
        self.assertEqual(r['cost'],1)
    def test_disconnected_cubic(self):
        g=Graph(4,((0,1),)*3+((2,3),)*3)
        self.assertEqual(certify_cubic_graph(g)['cost'],0)
    def test_defect(self):
        c=(Block(prism_tile(),3),Block(triangle_expansion_tile(),1),Block(prism_tile(),4))
        r=solve(c)
        self.assertEqual(r['graph_proof']['cost'],3)
        self.assertTrue(verify_result(c,r))
    def test_huge_positive(self):
        c=(Block(prism_tile(),2**16384+1),);r=solve(c)
        self.assertEqual(r['kernel']['n'],8)
        self.assertTrue(verify_result(c,r))
    def test_huge_negative_source(self):
        c=(Block(prism_tile(),2**4096+7),Block(triangle_expansion_tile(),1),
           Block(prism_tile(),2**1024+9))
        r=solve(c);self.assertTrue(verify_result(c,r))
        w=verify_source_witness(c,r['source_witness'])
        self.assertEqual(w['cost'],3)
        self.assertEqual(len(w['crossings']),3)
    def test_no_search_during_replay(self):
        c=(Block(prism_tile(),2**128),);r=solve(c)
        with patch('pattern_kernel.core.solve',side_effect=AssertionError), \
             patch('pattern_kernel.core.kernelize',side_effect=AssertionError), \
             patch('pattern_kernel.core.expand',side_effect=AssertionError), \
             patch('pattern_kernel.core._flow',side_effect=AssertionError):
            self.assertTrue(verify_result(c,r))


class CorruptionTests(unittest.TestCase):
    def setUp(self):
        self.c=(Block(prism_tile(),100),);self.r=solve(self.c)
    def test_wrong_source(self):
        self.assertFalse(verify_result((Block(prism_tile(),101),),self.r))
    def test_bad_cap(self):
        r=copy.deepcopy(self.r);r['reduction']['kernel_copies'][0]=3
        self.assertFalse(verify_result(self.c,r))
    def test_bool_cap(self):
        r=copy.deepcopy(self.r);r['reduction']['kernel_copies'][0]=True
        self.assertFalse(verify_result(self.c,r))
    def test_missing_anchor(self):
        r=copy.deepcopy(self.r);r['graph_proof']['four_flows'].pop()
        self.assertFalse(verify_result(self.c,r))
    def test_bad_flow(self):
        r=copy.deepcopy(self.r);r['graph_proof']['four_flows'][0]['augmentations'][0]['amount']=100
        self.assertFalse(verify_result(self.c,r))
    def test_kernel_forgery(self):
        r=copy.deepcopy(self.r);r['kernel']['edges'][0]=[0,0]
        self.assertFalse(verify_result(self.c,r))
    def test_negative_multiplicity_forgery(self):
        c=(Block(prism_tile(),100),Block(triangle_expansion_tile(),1))
        r=solve(c);r['source_witness']['blocks'][0][0]['copies']='0x0'
        self.assertFalse(verify_result(c,r))
    def test_negative_color_forgery(self):
        c=(Block(prism_tile(),100),Block(triangle_expansion_tile(),1))
        r=solve(c);r['source_witness']['blocks'][1][0]['colors']='0x1000000'
        self.assertFalse(verify_result(c,r))
    def test_bad_schema(self):
        r=copy.deepcopy(self.r);r['schema']='unknot-certificate'
        self.assertFalse(verify_result(self.c,r))

if __name__=='__main__':
    unittest.main()
