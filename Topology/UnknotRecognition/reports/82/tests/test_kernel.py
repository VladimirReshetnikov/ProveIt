import itertools
import math
import random
import unittest
from corner_kernel import *
from corner_kernel.compiler import (compile_boundary, recover_matching, Port,
                                    Incomplete, verify_count_transcript)
from corner_kernel.oracles import BlockOracle, SingletonOracle, ExplicitOracle
from reference import literal_glue, finite_boundary_oracles


def signed_partial_pairings(labels):
    if not labels:
        yield ()
        return
    a,rest = labels[0],labels[1:]
    yield from signed_partial_pairings(rest)
    for j,b in enumerate(rest):
        reduced = rest[:j]+rest[j+1:]
        for tail in signed_partial_pairings(reduced):
            for bit in (0,1):
                yield (Gluing(a,b,bit),)+tail


class KernelTests(unittest.TestCase):
    def test_gap_bit_changes_topology(self):
        s=[Surface(1,1)]
        adjacent=make_kernel(s,[(0,[Edge('a'),Edge('b')])])
        separated=make_kernel(s,[(0,[Edge('a'),Edge(),Edge('b'),Edge()])])
        self.assertEqual(signature(glue(adjacent,[Gluing('a','b')]).kernel),((2,0,True),))
        self.assertEqual(signature(glue(separated,[Gluing('a','b')]).kernel),((0,2,True),))

    def test_direction_bit_changes_topology(self):
        k=make_kernel([Surface(1,1)],[(0,[Edge('a'),Edge(),Edge('b'),Edge()])])
        self.assertEqual(signature(glue(k,[Gluing('a','b',0)]).kernel),((0,1,False),))
        self.assertEqual(signature(glue(k,[Gluing('a','b',1)]).kernel),((0,2,True),))

    def test_cyclic_order_changes_genus(self):
        gs=[Gluing('a','c'),Gluing('b','d')]
        def k(word):
            return make_kernel([Surface(1,1)],[(0,sum(([Edge(x),Edge()] for x in word),[]))])
        self.assertEqual(signature(glue(k('abcd'),gs).kernel),((-1,1,True),))
        self.assertEqual(signature(glue(k('acbd'),gs).kernel),((-1,3,True),))

    def test_two_discs_full_circle(self):
        k=make_kernel([Surface(1,1),Surface(1,1)],[(0,[Edge('a')]),(1,[Edge('b')])])
        self.assertEqual(signature(glue(k,[Gluing('a','b')]).kernel),((2,0,True),))

    def test_annulus_to_torus_or_klein(self):
        k=make_kernel([Surface(0,2)],[(0,[Edge('a')]),(0,[Edge('b')])])
        self.assertEqual(signature(glue(k,[Gluing('a','b',1)]).kernel),((0,0,True),))
        self.assertEqual(signature(glue(k,[Gluing('a','b',0)]).kernel),((0,0,False),))

    def test_nonorientability_persists(self):
        k=make_kernel([Surface(0,1,False),Surface(1,1)],[(0,[Edge('a'),Edge()]),(1,[Edge('b'),Edge()])])
        self.assertEqual(signature(glue(k,[Gluing('a','b')]).kernel),((0,1,False),))

    def test_invalid_inputs(self):
        with self.assertRaises(ValueError): Surface(0,1,True)
        with self.assertRaises(ValueError): Edge(length=0)
        with self.assertRaises(ValueError): Gluing('a','a')
        k=make_kernel([Surface(1,1)],[(0,[Edge('a'),Edge('b'),Edge('c')])])
        with self.assertRaises(ValueError): glue(k,[Gluing('a','b'),Gluing('b','c')])
        with self.assertRaises(ValueError): glue(k,[Gluing('a','z')])
        with self.assertRaises(ValueError): make_kernel([Surface(1,1)],[(0,[Edge('a'),Edge('a')])])

    def test_huge_lengths_and_binary_roundtrip(self):
        size=1<<16384
        k=make_kernel([Surface(1,1)],[(0,[Edge('a'),Edge(length=size),Edge('b'),Edge(length=size)])])
        self.assertEqual(Kernel.from_dict(k.to_dict()),k)
        self.assertEqual(signature(glue(k,[Gluing('a','b')]).kernel),((0,2,True),))
        b=1<<16384
        k=make_kernel([Surface(2-b,b)],[])
        self.assertEqual(glue(k,[]).kernel,k)

    def test_exhaustive_partial_polygon_gluings(self):
        count=0
        for n in range(1,9):
            labels=tuple(map(str,range(n)))
            s=[Surface(1,1)]
            raw=[(0,[Edge(x) for x in labels])]
            k=make_kernel(s,raw)
            for gs in signed_partial_pairings(labels):
                count+=1
                self.assertEqual(signature(glue(k,gs).kernel),literal_glue(s,raw,gs))
        self.assertEqual(count, sum(sum(math.factorial(n)//(math.factorial(n-2*j)*math.factorial(j))
                                       for j in range(n//2+1)) for n in range(1,9)))
        print('EXHAUSTIVE_CASES',count)

    def test_random_expansion_and_composition(self):
        rng=random.Random(20261012)
        count=0
        for case in range(1600):
            n=rng.randrange(1,5)
            surfaces=[];raw=[];labels=[]
            for i in range(n):
                b=rng.randrange(1,4)
                ori=rng.choice([True,True,False])
                g=rng.randrange(3) if ori else rng.randrange(1,4)
                surfaces.append(Surface(2-b-(2*g if ori else g),b,ori))
                for c in range(b):
                    edges=[]
                    for j in range(rng.randrange(1,5)):
                        label=f'p{len(labels)}';labels.append(label)
                        edges.append(Edge(label,rng.randrange(2)))
                        if rng.randrange(3): edges.append(Edge(length=rng.randrange(1,9)))
                    raw.append((i,edges))
            rng.shuffle(labels)
            m=rng.randrange(len(labels)//2+1)
            gs=[Gluing(labels[2*j],labels[2*j+1],rng.randrange(2)) for j in range(m)]
            k=make_kernel(surfaces,raw)
            direct=glue(k,gs).kernel
            self.assertEqual(signature(direct),literal_glue(surfaces,raw,gs))
            split=rng.randrange(m+1)
            sequential=glue(glue(k,gs[:split]).kernel,gs[split:]).kernel
            self.assertEqual(signature(direct),signature(sequential))
            # A second unseen continuation is an observer-equivalence check.
            live=list(direct.ports);rng.shuffle(live)
            tail=[Gluing(live[j],live[j+1],rng.randrange(2)) for j in range(0,len(live)-1,2)]
            self.assertEqual(signature(glue(direct,tail).kernel),signature(glue(sequential,tail).kernel))
            count+=1
        print('RANDOM_SURFACE_CASES',count)

    def test_compiler_random_cycles(self):
        rng=random.Random(770012)
        for case in range(700):
            b=rng.randrange(1,5)
            raw=[];label=0
            for c in range(b):
                edges=[]
                for j in range(rng.randrange(1,7)):
                    if rng.randrange(3):
                        edges.append(Edge(str(label),rng.randrange(2)));label+=1
                    else:
                        edges.append(Edge(length=rng.randrange(1,12)))
                raw.append((0,edges))
            surfaces=[Surface(2-b,b)]
            ports,vc,rc=finite_boundary_oracles(raw)
            compiled,matching=compile_boundary(surfaces,ports,vc,rc)
            self.assertEqual(len(compiled.ports),len(ports))
            self.assertLessEqual(matching.queries, 2*len(ports)*math.ceil(math.log2(max(2,2*len(ports))))+2*len(ports)+3)
            self.assertTrue(verify_count_transcript(matching.transcript,vc,rc))
            labels=list(compiled.ports);rng.shuffle(labels)
            gs=[Gluing(labels[j],labels[j+1],rng.randrange(2)) for j in range(0,len(labels)-1,2)]
            self.assertEqual(signature(glue(compiled,gs).kernel),literal_glue(surfaces,raw,gs))
        print('COMPILER_CASES',700)

    def test_huge_analytic_compiler(self):
        # Residual path i has [i*(L+1),(i+1)*(L+1)) as its vertices.
        # Ports run from the end of path i-1 to the start of path i.
        for bits in (8,128,1024,16384):
            p,L=12,1<<bits
            blocks=[(i*(L+1),(i+1)*(L+1)) for i in range(p)]
            rc=BlockOracle(blocks);vc=SingletonOracle(rc.n)
            ports=[Port(f'p{i:02}',0,blocks[(i-1)%p][1]-1,blocks[i][0]) for i in range(p)]
            k,m=compile_boundary([Surface(1,1)],ports,vc,rc)
            self.assertEqual(len(k.cycles),1)
            self.assertEqual(sum(len(c.edges) for c in k.cycles),2*p)
            self.assertEqual(m.passive_boundary,0)
        print('MAXIMUM_BINARY_COORDINATE_BITS',16385)

    def test_shared_budget_and_cancellation(self):
        v=ExplicitOracle(4,[]);r=ExplicitOracle(4,[(0,1),(2,3)])
        with self.assertRaises(Incomplete): recover_matching([0,1,2,3],v,r,max_queries=1)
        def stop(): raise KeyboardInterrupt('cancelled')
        with self.assertRaises(KeyboardInterrupt): recover_matching([0,1,2,3],v,r,check=stop)

    def test_bad_degree_and_forged_transcript(self):
        v=ExplicitOracle(4,[]);r=ExplicitOracle(4,[(0,1),(1,2),(2,3)])
        with self.assertRaises(ValueError): recover_matching([0,1,2,3],v,r)
        r=ExplicitOracle(4,[(0,1),(2,3)])
        m=recover_matching([0,1,2,3],v,r)
        bad=[dict(row) for row in m.transcript];bad[0]['count']+=1
        self.assertFalse(verify_count_transcript(bad,v,r))

if __name__=='__main__':
    unittest.main(verbosity=2)
