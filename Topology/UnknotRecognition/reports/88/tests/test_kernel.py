import copy,random,unittest
from unittest.mock import patch
from cycle_kernel import *
from cycle_kernel.model import components
from cycle_kernel.partitions import *
from cycle_kernel.oracle import enumerate_signature,graph_signature,signature_power
from cycle_kernel.query import solve_graph,closed_source_is_cubic
from cycle_kernel.replay import verify_graph
from cycle_kernel.witness import lift_colors,verify_runs
from cycle_kernel.grammar import evaluate
from cycle_kernel.validation import source_cell_cover

EDGE=Graph(2,((0,1),),(0,),(1,))
SWAP=Graph(4,((0,3),(1,2)),(0,1),(2,3))
PRISM=Graph(4,((0,2),(1,3),(2,3)),(0,1),(2,3))
REGRESSION=Graph(9,((1,2),(8,0),(7,5),(7,5),(4,8),(3,7)),(0,1,2),(3,4,5))

def leaf(t):return {'op':'leaf','tile':t.to_dict()}
def power(t,n):return {'op':'power','child':t,'exponent_hex':hex(n)}

class ModelTests(unittest.TestCase):
    def test_invalid_vertices(self):
        with self.assertRaises(ValueError):Graph(True,())
        with self.assertRaises(ValueError):Graph(2,((0,2),))
    def test_port_alias(self):
        with self.assertRaises(ValueError):Graph(2,(),(0,),(0,)).validate_tile()
    def test_repeated_ports(self):
        with self.assertRaises(ValueError):Graph(3,(),(0,0),(1,2))
    def test_expansion_cap(self):
        with self.assertRaises(ValueError):power_explicit(EDGE,10**6)
    def test_nonpositive_binary_power(self):
        for n in [0,-1,True]:
            with self.assertRaises(ValueError):kernel_power(EDGE,n)
    def test_loops_and_parallel_edges(self):
        t=Graph(2,((0,0),(0,1),(0,1)),(0,),(1,))
        self.assertEqual(len(close(t).edges),3)
    def test_closure_cubic(self):
        self.assertTrue(closed_source_is_cubic(PRISM));self.assertFalse(closed_source_is_cubic(EDGE))

class PartitionTests(unittest.TestCase):
    def test_permutation(self):
        c=stabilize(boundary_partition(SWAP));self.assertEqual(c['s'],1)
        self.assertTrue(verify_stabilization(boundary_partition(SWAP),c))
    def test_maximal_shift(self):
        w=12;t=Graph(2*w,tuple((i,w+i+1) for i in range(w-1)),tuple(range(w)),tuple(range(w,2*w)))
        c=stabilize(boundary_partition(t));self.assertEqual(c['s'],w)
        self.assertEqual(c['ranks'],list(range(w-1,-1,-1))+[0])
    def test_divisor_tamper(self):
        p=boundary_partition(SWAP);c=stabilize(p);c['divisor']=[0]*4
        self.assertFalse(verify_stabilization(p,c))
    def test_late_plateau(self):
        p=(0,1,2,1,2,3);c=stabilize(p);a=tuple(c['partition'])
        for _ in range(20):a=product(a,p);self.assertEqual(rank(a),0)

class NormalizationTests(unittest.TestCase):
    def compare(self,t,n,k=3):
        g,_=kernel_power(t,n,k,connected_fastpath=False)
        self.assertEqual(graph_signature(g,k),signature_power(t,n,k))
    def test_regression_cap_is_not_a_port(self):
        nf=normal_form(REGRESSION)
        self.assertEqual([len(t.left) for t in nf.templates.values()],[1])
        self.assertTrue(source_cell_cover(nf,7)['valid']);self.compare(REGRESSION,101,0)
    def test_swap_keeps_parity(self):
        a=kernel_power(SWAP,101)[0];b=kernel_power(SWAP,102)[0]
        self.assertNotEqual(boundary_partition(a),boundary_partition(b))
    def test_connected_sharp_four(self):
        a=enumerate_signature(power_explicit(EDGE,3));b=enumerate_signature(power_explicit(EDGE,4))
        self.assertNotEqual(a[0][0][3],b[0][0][3])
        self.assertEqual(enumerate_signature(kernel_power(EDGE,1001)[0]),b)
    def test_rank_zero(self):
        t=Graph(6,((0,4),(1,5)),(0,1,2),(3,4,5));self.compare(t,41)
    def test_detached_loops(self):
        t=Graph(3,((0,1),(2,2)),(0,),(1,));self.compare(t,99)
    def test_isolated_vertices(self):
        t=Graph(6,(),(0,1),(2,3));self.compare(t,99)
    def test_multiplicity_torsion_not_invented(self):
        # Exact mark absence must saturate: isolated edges cannot be discarded.
        t=Graph(4,((0,1),(2,3)),(0,),(1,));self.compare(t,39,1)
    def test_source_cell_cover(self):
        for t in [EDGE,SWAP,PRISM,REGRESSION]:
            s=stabilize(boundary_partition(t))['s'];nf=normal_form(power_explicit(t,s))
            for n in (3,4,7):self.assertTrue(source_cell_cover(nf,n)['valid'])
    def test_all_thresholds(self):
        for k in range(6):self.compare(SWAP,31,k)
    def test_binary_stress(self):
        for bits in (128,1024,4096,16384):
            g,m=kernel_power(SWAP,(1<<bits)+1)
            self.assertEqual((g.n,len(g.edges)),(24,22))
    def test_seeded_signatures(self):
        r=random.Random(711)
        for i in range(80):
            w=1+i%3;n=2*w+r.randrange(3)
            t=Graph(n,tuple((r.randrange(n),r.randrange(n)) for _ in range(r.randrange(n+3))),tuple(range(w)),tuple(range(w,2*w)))
            self.compare(t,27,i%4)

class QueryTests(unittest.TestCase):
    def test_cube_positive(self):
        g=close(power_explicit(PRISM,4));p=solve_graph(g)
        self.assertEqual(p['verdict'],'NO_LOW_MARKED_CUT');self.assertTrue(verify_graph(g,p))
    def test_prism_negative(self):
        g=close(power_explicit(PRISM,3));p=solve_graph(g)
        self.assertEqual(p['verdict'],'LOW_MARKED_CUT');self.assertTrue(verify_graph(g,p))
    def test_search_disabled_replay(self):
        g=close(power_explicit(PRISM,4));p=solve_graph(g)
        with patch('cycle_kernel.query.solve_graph',side_effect=AssertionError):self.assertTrue(verify_graph(g,p))
    def test_missing_anchor_rejected(self):
        g=close(power_explicit(PRISM,4));p=solve_graph(g);p['exclusions'].pop()
        self.assertFalse(verify_graph(g,p))
    def test_forged_flow_rejected(self):
        g=close(power_explicit(PRISM,4));p=solve_graph(g);p['exclusions'][0]['paths'][0]['amount']=999
        self.assertFalse(verify_graph(g,p))
    def test_forged_coloring_rejected(self):
        g=close(power_explicit(PRISM,3));p=solve_graph(g);p['colors']=[0]*g.n
        self.assertFalse(verify_graph(g,p))
    def test_random_query_oracle(self):
        r=random.Random(899)
        for _ in range(80):
            n=6;g=Graph(n,tuple((r.randrange(n),r.randrange(n)) for _ in range(r.randrange(1,12))))
            brute=enumerate_signature(g)[0][0][3]<=3;p=solve_graph(g)
            self.assertEqual(p['verdict']=='LOW_MARKED_CUT',brute);self.assertTrue(verify_graph(g,p))

class LiftTests(unittest.TestCase):
    def test_huge_connected_lift(self):
        runs=lift_colors(EDGE,(1<<16384)+1,[[0,0],[0,1],[1,1],[1,0]])
        self.assertTrue(verify_runs(EDGE,(1<<16384)+1,runs))
    def test_detached_lift(self):
        g=Graph(2,((0,1),));runs=lift_colors(g,1<<4096,[[0,0],[1,1],[0,0],[0,0]],detached=True)
        self.assertTrue(verify_runs(g,1<<4096,runs,detached=True))
    def test_repeat_wrong_count(self):
        runs=lift_colors(EDGE,100,[[0,0]]);runs[0]['repeat_hex']='0x63'
        self.assertFalse(verify_runs(EDGE,100,runs))
    def test_nonconstant_repeat_forbidden(self):
        self.assertFalse(verify_runs(EDGE,10,[dict(colors=[0,1],repeat_hex='0xa')],100))

class GrammarTests(unittest.TestCase):
    def test_nested_formula(self):
        tree=power({'op':'serial','children':[power(leaf(SWAP),13),leaf(PRISM)]},9)
        a,_=evaluate(tree);b,_=evaluate(tree,compress=False)
        self.assertEqual(graph_signature(a),graph_signature(b))
    def test_parallel_formula(self):
        tree=power({'op':'parallel','children':[power(leaf(EDGE),9),power(leaf(EDGE),11)]},17)
        a,_=evaluate(tree);b,_=evaluate(tree,compress=False)
        self.assertEqual(graph_signature(a),graph_signature(b))
    def test_depth_cap(self):
        tree=power(power(leaf(EDGE),2),2)
        with self.assertRaises(ValueError):evaluate(tree,max_depth=1)
    def test_huge_nested(self):
        tree=leaf(SWAP)
        for _ in range(6):tree=power(tree,2**128+3)
        a,stats=evaluate(tree);self.assertEqual(stats['max_power_depth'],6)
        self.assertLess(len(a.edges),1000)

if __name__=='__main__':unittest.main()
