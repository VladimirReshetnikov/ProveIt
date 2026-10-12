import unittest
from dataclasses import replace
from itertools import combinations
from math import gcd
import json
import random
from interface_homology import *
from interface_homology.smith import smith, verify_smith, torsion_blocks, rank_mod_two, WorkLimit
from interface_homology.boundary import s3_boundary_consequences
from tests.oracle import expand, sympy_smith, random_model


class InterfaceTests(unittest.TestCase):
    def group(self, model):
        p = condense(model)
        self.assertTrue(verify_condensation(model, p))
        s = smith(p.matrix, cols=p.relation_count)
        self.assertTrue(verify_smith(p.matrix, s, cols=p.relation_count))
        return p, p.rows-len(s.diagonal)+p.free_bulk, torsion_blocks(s.diagonal, p.two_torsion_bulk)

    def test_empty(self):
        p, free, torsion = self.group(Model(Core(0)))
        self.assertEqual((p.b0, free, torsion, p.euler), (0, 0, (), 0))

    def test_disc_attachments(self):
        core = Core(1, ((0, 0),))
        for n in range(13):
            model = Model(core, (Surface(True, 0, 1, circles=(Loop(0, (1,)*n),)),))
            p, free, torsion = self.group(model)
            self.assertEqual(free, int(n == 0))
            self.assertEqual(torsion, ((n, 1),) if n > 1 else ())

    def test_signed_boundary_sum(self):
        core = Core(1, ((0, 0),))
        for word in [(1,), (-1,)]:
            _, free, tors = self.group(Model(core, (Surface(True, 0, 2, circles=(Loop(0,(1,)), Loop(0,word))),)))
            self.assertEqual((free, tors), (1, ((2,1),)) if word == (1,) else (2, ()))

    def test_mobius_attachment(self):
        core = Core(1, ((0, 0),))
        for n in range(12):
            _, free, tors = self.group(Model(core, (Surface(False, 1, 1, circles=(Loop(0,(1,)*n),)),)))
            self.assertEqual(free, 1)
            self.assertEqual(tors, ((2,1),) if n % 2 == 0 else ())

    def test_twisting_doubles_not_repeatedly(self):
        core = Core(1, ((0, 0),), (Loop(0, (1,)*3),))
        surfaces = tuple(Surface(False, 1, 1, circles=(Loop(0,(1,)),)) for _ in range(5))
        _, free, tors = self.group(Model(core, surfaces))
        self.assertEqual(free, 0)
        self.assertEqual(tors, ((2,4), (6,1)))

    def test_unsaturated_large_genus(self):
        n = 1 << 16384
        core = Core(1, ((0, 0),))
        p, free, tors = self.group(Model(core, (Surface(True, n, n+3, circles=(Loop(0,(1,1)),)),)))
        self.assertEqual(p.rows, 1)
        self.assertEqual(free, 3*n+2)
        self.assertEqual(tors, ())

    def test_huge_unported_multiplicity(self):
        n = 1 << 16384
        model = Model(Core(0), (Surface(False, 5, 0, n),))
        p, free, tors = self.group(model)
        self.assertEqual((p.b0, free, tors), (n, 4*n, ((2,n),)))
        raw = wire(p.payload())
        decoded = unwire(json.loads(json.dumps(raw)))
        self.assertEqual(decoded['free_bulk'], 4*n)
        self.assertLess(len(json.dumps(raw)), 40000)

    def test_graph_cycle_from_intervals(self):
        model = Model(Core(2), (Surface(True,0,1,intervals=(0,1,0)),))
        p, free, tors = self.group(model)
        self.assertEqual((p.graph_cycle_rank, p.b0, free, tors), (1,1,1,()))

    def test_spheres_and_projective_planes(self):
        p, free, tors = self.group(Model(Core(0), (Surface(True,0,0,7), Surface(False,1,0,9))))
        self.assertEqual((p.b0, p.euler, free, tors), (16,23,0,((2,9),)))

    def test_invalid_models(self):
        bad = [Model(Core(True)), Model(Core(0, ((0,0),))),
               Model(Core(1), (Surface(False,0,1),)),
               Model(Core(1), (Surface(True,0,1,circles=(Loop(0),),intervals=(0,)),)),
               Model(Core(1), (Surface(True,0,1,2,intervals=(0,)),)),
               Model(Core(2, ((0,1),), (Loop(0,(1,)),))),
               Model(Core(1), (Surface(True,0,0,intervals=(0,)),))]
        for model in bad:
            with self.assertRaises(ValueError): condense(model)

    def test_replay_mutations(self):
        model = Model(Core(2, ((0,1),(1,1))), (Surface(False,2,1,circles=(Loop(1,(2,2)),)),))
        p = condense(model)
        mutants = [replace(p, b0=p.b0+1), replace(p, free_bulk=p.free_bulk+1),
                   replace(p, two_torsion_bulk=1), replace(p, graph_cycle_rank=7),
                   replace(p, source_sha256='0'*64), replace(p, matrix=((9,), (2,))),
                   replace(p, core_forest=()), replace(p, core_generators=(0,)),
                   replace(p, relation_count=9), replace(p, surface_free=(99,))]
        for q in mutants: self.assertFalse(verify_condensation(model,q))

    def test_hex_integer_rejections(self):
        for text in ['-0','00','+1','0x10','A','-','']:
            with self.assertRaises(ValueError): unwire({'$integer':text})
        self.assertEqual(unwire(wire(-123456)), -123456)

    def test_random_expanded_presentations(self):
        rng = random.Random(2026101201)
        for i in range(1200):
            model = random_model(rng)
            p, free, tors = self.group(model)
            a, c, b0 = expand(model)
            diag = sympy_smith(a,c)
            with self.subTest(case=i):
                self.assertEqual(p.b0,b0)
                self.assertEqual(free,len(a)-len(diag))
                self.assertEqual(tors,torsion_blocks(diag))


class SmithTests(unittest.TestCase):
    def test_rectangular_zero_shapes(self):
        for a,c in [((),5), (((),(),()),0), (((0,0),(0,0)),2)]:
            s=smith(a,cols=c)
            self.assertEqual(s.diagonal,())
            self.assertTrue(verify_smith(a,s,cols=c))

    def test_random_against_sympy(self):
        rng=random.Random(2026101202)
        for _ in range(1800):
            m,n=rng.randrange(0,7),rng.randrange(0,7)
            a=tuple(tuple(rng.randrange(-30,31) for _ in range(n))for _ in range(m))
            s=smith(a,cols=n)
            self.assertTrue(verify_smith(a,s,cols=n))
            self.assertEqual(s.diagonal,sympy_smith(a,n))

    def test_determinantal_divisors(self):
        from sympy import Matrix
        rng=random.Random(2026101203)
        for _ in range(200):
            m,n=rng.randrange(1,5),rng.randrange(1,5)
            a=tuple(tuple(rng.randrange(-5,6)for _ in range(n))for _ in range(m))
            s=smith(a)
            previous=1
            for k,d in enumerate(s.diagonal,1):
                divisor=0
                for rows in combinations(range(m),k):
                    for cols in combinations(range(n),k):
                        divisor=gcd(divisor,abs(int(Matrix([[a[i][j]for j in cols]for i in rows]).det())))
                self.assertEqual(divisor,previous*d)
                previous=divisor

    def test_operation_and_bit_caps(self):
        with self.assertRaises(WorkLimit): smith(((2,3),(4,6)),max_operations=0)
        with self.assertRaises(WorkLimit): smith(((256,),),max_entry_bits=3)
        s=smith(((2,3),(4,6)))
        self.assertFalse(verify_smith(((2,3),(4,6)),s,max_operations=0))
        self.assertFalse(verify_smith(((2,3),(4,6)),replace(s,diagonal=(1,1))))
        self.assertFalse(verify_smith(((2,3),(4,6)),replace(s,operations=(('ra',0,0,1),))))

    def test_bulk_torsion_canonicalization(self):
        rng=random.Random(2026101204)
        for _ in range(500):
            ds=[]; x=1
            for __ in range(rng.randrange(0,8)):
                x*=rng.randrange(1,7);ds.append(x)
            mu=rng.randrange(0,9)
            vals=ds+[2]*mu
            a=tuple(tuple(v if i==j else 0 for j,v in enumerate(vals))for i in range(len(vals)))
            expected=torsion_blocks(sympy_smith(a,len(vals)))
            self.assertEqual(torsion_blocks(ds,mu),expected)
        self.assertEqual(torsion_blocks((3,12),1<<16384),((2,(1<<16384)-1),(6,1),(12,1)))

    def test_twisted_free_formula(self):
        rng=random.Random(2026101205)
        for _ in range(700):
            d,t=rng.randrange(0,7),rng.randrange(0,7)
            s=tuple(tuple(rng.randrange(-12,13)for _ in range(t))for _ in range(d))
            a=s+tuple(tuple(2 if i==j else 0 for j in range(t))for i in range(t))
            diagonal=sympy_smith(a,t)
            self.assertEqual(len(a)-len(diagonal),d)
            r=rank_mod_two(s,cols=t)
            self.assertEqual(torsion_blocks(diagonal),((2,t-r),)if t>r else ())

    def test_conditional_boundary_not_verifier(self):
        p=s3_boundary_consequences(1,0)
        self.assertTrue(p.ball_under_hypothesis)
        self.assertIn('NOT VERIFIED',p.hypothesis)
        self.assertEqual(s3_boundary_consequences(5,7).betti,(1,7,4,0))
        self.assertFalse(s3_boundary_consequences(2,0).ball_under_hypothesis)
        with self.assertRaises(ValueError):s3_boundary_consequences(0,0)


class PortTests(unittest.TestCase):
    def test_marked_endpoint_partition(self):
        from interface_homology.ports import endpoint_partition
        self.assertEqual(endpoint_partition(3,((0,1<<100),(0b100101,1),(0b011010,1))), (0,1,0,1,1,0))
        for bad in [((3,2),), ((1,1),(3,1)), ((1,1),), ((16,1),)]:
            with self.assertRaises(ValueError): endpoint_partition(1,bad)
        self.assertEqual(endpoint_partition(0,((0,55),)),())

    def test_eight_port_circle(self):
        from interface_homology.ports import Port, assemble_interfaces
        core=Core(1,((0,0),))
        ports=tuple(Port(0,(i,(i+1)%8),0,(1,)if i==7 else ())for i in range(8))
        m=assemble_interfaces(core,(Surface(True,0,1),),ports)
        self.assertEqual(m.surfaces[0].circles,(Loop(0,(1,)),))
        self.assertEqual(condense(m).matrix,((1,),))

    def test_loop_and_interval_ports(self):
        from interface_homology.ports import Port, assemble_interfaces
        core=Core(2,((0,1),(0,0)))
        m=assemble_interfaces(core,(Surface(False,1,2),),(Port(0,(0,0),0,(2,)),Port(0,(1,2),0,(1,))))
        self.assertEqual(m.surfaces[0].circles,(Loop(0,(2,)),))
        self.assertEqual(m.surfaces[0].intervals,(0,))
        self.assertEqual(condense(m).graph_cycle_rank,1)

    def test_port_direction_and_branch_rejection(self):
        from interface_homology.ports import Port, assemble_interfaces
        core=Core(1,((0,0),))
        with self.assertRaises(ValueError):
            assemble_interfaces(core,(Surface(True,0,1),),(Port(0,(0,1),0),Port(0,(1,0),0,orientation=-1)))
        with self.assertRaises(ValueError):
            assemble_interfaces(core,(Surface(True,0,1),),tuple(Port(0,(0,i),0)for i in (1,2,3)))
        m=assemble_interfaces(core,(Surface(True,0,1),),(Port(0,(0,0),0,(1,),-1),))
        self.assertEqual(m.surfaces[0].circles,(Loop(0,(-1,)),))

    def test_random_port_cycles(self):
        from interface_homology.ports import Port, assemble_interfaces, endpoint_partition
        rng=random.Random(2026101206)
        for _ in range(400):
            n=rng.randrange(1,21)
            forward=[rng.choice((True,False))for __ in range(n)]
            values=[rng.choice((-1,1))for __ in range(n)]
            ports=[]; masks=[0]*n
            for i in range(n):
                ends=(i,(i+1)%n)if forward[i]else((i+1)%n,i)
                value=values[i]if forward[i]else-values[i]
                ports.append(Port(0,ends,0,(value,),1 if forward[i]else -1))
                for slot,v in enumerate(ends):masks[v]|=1<<(2*i+slot)
            part=endpoint_partition(n,tuple((mask,1)for mask in masks))
            self.assertEqual(len(set(part)),n)
            model=assemble_interfaces(Core(1,((0,0),)),(Surface(True,0,1),),tuple(ports))
            self.assertEqual(condense(model).matrix,((sum(values),),))

if __name__=='__main__': unittest.main()
