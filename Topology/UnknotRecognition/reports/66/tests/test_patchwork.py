import unittest
from itertools import product
from dataclasses import replace
from unittest.mock import patch
from signed_continuations.patchwork import *
from signed_continuations.surfaces import *
from signed_continuations.core import *

class PatchworkTests(unittest.TestCase):
    def test_every_signature_realized(self):
        for r in range(1,5):
            for p in partitions(r):
                i=inspect(realize_partition(p));self.assertEqual(i.signature,p);self.assertEqual(i.euler,p.blocks)
    def test_barycentric_subdivision(self):
        for s in (fan_disk(3,seams=((0,1),)),annulus(),punctured_torus(),planar_holes()):
            a,b=inspect(s),inspect(barycentric_subdivision(s))
            self.assertEqual((a.euler,a.components,a.orientable,a.boundary_components,a.signature),
                             (b.euler,b.components,b.orientable,b.boundary_components,b.signature))
    def test_complete_small_grid(self):
        system=grid_system(2,2);reduced=solve(system);full=solve(system,reduced=False)
        self.assertEqual(reduced.minimum_cost,full.minimum_cost);self.assertTrue(reduced.disk_exists)
        best=None;tested=0
        for choices in product(*(range(len(opts)) for opts in system.options)):
            info=inspect(assemble(system,choices),require_live=False)
            if info.components==1 and info.orientable:
                value=-info.euler;best=value if best is None else min(best,value)
            tested+=1
        self.assertEqual(tested,297);self.assertEqual(best,reduced.minimum_cost)
        self.assertTrue(verify_witness(system,reduced))
    def test_larger_grids(self):
        for a,b in ((2,4),(3,3)):
            system=grid_system(a,b);small=solve(system);full=solve(system,reduced=False)
            self.assertEqual(small.minimum_cost,full.minimum_cost);self.assertTrue(verify_witness(system,small))
            self.assertTrue(all(h['retained']<=1<<(h['frontier']-1) for h in small.history))
    def test_circle_seams_and_anchor(self):
        # Outer annulus arc stays unglued and anchors the assembled disk.
        a=annulus();a=Surface(a.triangles,((0,1),a.seams[0]))
        b=fan_disk(6,seams=(tuple(range(6))+(0,),))
        system=PatchSystem(((a,),(b,)),(SeamPair((0,1),(1,0)),),(0,0),(0,1))
        out=solve(system);self.assertTrue(out.disk_exists);self.assertTrue(verify_witness(system,out))
    def test_genus_options(self):
        disk=fan_disk(3,seams=((0,1),));torus=punctured_torus()
        system=PatchSystem(((torus,disk),),(),(0,0),(0,))
        out=solve(system);self.assertEqual(out.choices,(1,));self.assertTrue(verify_witness(system,out))
        no=solve(replace(system,options=((torus,),)))
        self.assertFalse(no.disk_exists);self.assertEqual(no.minimum_cost,1)
        self.assertTrue(verify_witness(replace(system,options=((torus,),)),no))
    def test_disconnected_failure(self):
        # A split patch leaves an entire closed-off component at the final seam.
        a=realize_partition(SignedPartition.discrete(2));b=realize_partition(SignedPartition.discrete(1))
        sys=PatchSystem(((a,),(b,)),(SeamPair((0,1),(1,0)),),(0,0),(0,1))
        answer=solve(sys);self.assertIsNone(answer.minimum_cost);self.assertFalse(verify_witness(sys,answer))
    def test_invalid_schema_and_order(self):
        sys=grid_system(2,2)
        with self.assertRaises(ValueError):solve(replace(sys,order=(1,0,2,3)))
        with self.assertRaises(ValueError):solve(replace(sys,pairs=sys.pairs[:-1]))
        with self.assertRaises(ValueError):solve(replace(sys,pairs=sys.pairs+(sys.pairs[0],)))
    def test_geometry_replay_without_algebra(self):
        sys=grid_system(2,3);answer=solve(sys)
        with patch.object(SignedPartition,'join',side_effect=AssertionError('producer disabled')),patch.object(SignedPartition,'add_edge',side_effect=AssertionError('producer disabled')),patch.object(SignedPartition,'vector',side_effect=AssertionError('producer disabled')):
            self.assertTrue(verify_witness(sys,answer))
    def test_witness_mutation(self):
        sys=grid_system(2,2);answer=solve(sys)
        self.assertFalse(verify_witness(sys,replace(answer,minimum_cost=777)))
        self.assertFalse(verify_witness(sys,replace(answer,choices=(999,)*4)))

    def test_resource_failures_are_not_negative_answers(self):
        system=grid_system(2,2)
        with self.assertRaises(BudgetExceeded):solve(system,max_candidates=0)
        with self.assertRaises(BudgetExceeded):solve(system,max_dimension=1)
        with self.assertRaises(TypeError):solve(system,max_candidates=True)
