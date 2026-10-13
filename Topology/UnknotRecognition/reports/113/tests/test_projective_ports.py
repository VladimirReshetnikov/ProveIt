import unittest
from fractions import Fraction as F
from copy import deepcopy
from projective_ports import Block,Prepared,ResourceLimit,enumerate_rays,enumerate_rays_by_zeros,projective_atlas
from projective_ports.exact import nullspace,solve_unique,primitive
from projective_ports.source import (Source,compile_two_block,compile_variable_separator,
    private_components,synchronized_source,extreme_witness)
from projective_ports.verify import verify_vector,verify_synchronized
from projective_ports.fixtures import (sleeve_blocks,sleeve_costs,centroid_blocks,
    false_convexification,solid_torus,capped_solid_torus,matching,euler,nonextreme_assembly)
from experiments.oracle import all_rays,positive,cartesian_modes


class ExactTests(unittest.TestCase):
    def test_rref_degenerate(self):
        self.assertEqual(nullspace(((1,2),(2,4)),2),((-F(2),F(1)),))
    def test_unique_overdetermined(self):
        self.assertEqual(solve_unique(((1,0),(0,1),(1,1)),(2,3,5),2),(2,3))
        self.assertIsNone(solve_unique(((1,0),(0,1),(1,1)),(2,3,6),2))
    def test_primitive(self):
        self.assertEqual(primitive((F(-2,3),F(-4,3)),True),(1,2))
    def test_float_rejection(self):
        with self.assertRaises(ValueError):Block(1,(),((0.5,),))
    def test_dimensions(self):
        with self.assertRaises(ValueError):Block(2,((1,),),((1,0),))
        with self.assertRaises(ValueError):Prepared(())
    def test_nonnegative_ports(self):
        with self.assertRaises(ValueError):Block(1,(),((-1,),))
    def test_conflict_validation(self):
        for c in [((0,0),),((0,2),),((False,1),)]:
            with self.assertRaises(ValueError):Block(2,(),((1,1),),c)
    def test_support_budget(self):
        with self.assertRaises(ResourceLimit):enumerate_rays(Block(3,(),((1,1,1),)),max_supports=1)
    def test_cancellation_callback(self):
        def stop():raise ResourceLimit('cancelled')
        with self.assertRaises(ResourceLimit):Prepared(sleeve_blocks(1),check=stop)
    def test_zero_set_enumerator(self):
        b=Block(5,((1,1,-1,0,0),(0,0,1,-2,-1)),((1,0,0,1,1),),((0,1),))
        self.assertEqual(set(enumerate_rays_by_zeros(b)),set(all_rays(b.n,b.equations,b.conflicts)))
    def test_zero_set_long_nullity_one(self):
        n=40
        rows=tuple(tuple(int(j==i)-int(j==i+1) for j in range(n)) for i in range(n-1))
        b=Block(n,rows,((1,)*n,))
        self.assertEqual(enumerate_rays_by_zeros(b),((1,)*n,))
        self.assertEqual(Prepared((b,),ray_method='zeros').solve(((1,)*n,))['value'],1)
    def test_zero_set_full_rank(self):
        self.assertEqual(enumerate_rays_by_zeros(Block(2,((1,0),(0,1)),((1,1),))),())
    def test_ray_enumeration_independent(self):
        b=Block(5,((1,1,-1,0,0),(0,0,1,-2,-1)),((1,0,0,1,1),),((0,1),))
        self.assertEqual(set(enumerate_rays(b)),set(all_rays(b.n,b.equations,b.conflicts)))


class AtlasTests(unittest.TestCase):
    def test_single_scalar(self):
        p=Prepared((Block(2,(),((2,3),),((0,1),)),))
        a=p.solve(((1,2),));self.assertEqual(a['value'],F(2,3))
    def test_zero_port_positive(self):
        b=(Block(2,(),((0,1),(0,0))),Block(1,(),((0,),(1,))))
        a=Prepared(b).solve(((1,-9),(-9,)))
        self.assertEqual(a['kind'],'zero-port');self.assertTrue(verify_synchronized(b,((1,-9),(-9,)),a))
    def test_zero_port_negative_ignored(self):
        b=Block(2,(),((0,2),(0,1)))
        a=Prepared((b,)).solve(((-100,3),))
        self.assertEqual(a['value'],1)
    def test_zero_port_anchor(self):
        p=Prepared((Block(2,(),((0,1),(0,0))),))
        a=p.solve(((9,-1),),zeros=((0,),));self.assertEqual(a['status'],'NO_POSITIVE')
    def test_false_convexification(self):
        a=Prepared(false_convexification()).solve(((1,1),(1,)))
        self.assertEqual(a['kind'],'no-common-nonzero-port')
    def test_same_slope_incompatible(self):
        p=Prepared((Block(2,(),((1,2),(1,2)),((0,1),)),))
        self.assertEqual(p.solve(((2,8),))['value'],2)
    def test_three_port_new_vertex(self):
        b=centroid_blocks();p=Prepared(b);a=p.solve(((1,1),(1,1)))
        self.assertEqual(a['port'],(F(1,3),)*3)
        self.assertNotIn(a['port'],{r.port for rr in p.rays for r in rr})
    def test_four_port_lower_dimensional(self):
        b=(Block(2,(),((2,0),(0,2),(0,0),(0,0))),
           Block(1,(),((1,),(1,),(0,),(0,))))
        p=Prepared(b);a=p.solve(((1,1),(1,)))
        self.assertEqual(a['port'],(F(1,2),F(1,2),0,0))
    def test_degenerate_point_domains(self):
        b=(Block(1,(),((1,),(2,),(3,))),Block(1,(),((2,),(4,),(6,))))
        a=Prepared(b).solve(((1,),(1,)))
        self.assertEqual(a['port'],(F(1,6),F(1,3),F(1,2)))
    def test_two_port_cartesian(self):
        for m in range(1,8):
            p=Prepared(sleeve_blocks(m));c=sleeve_costs(m)
            self.assertEqual(p.solve(c)['value'],cartesian_modes(c))
            self.assertEqual(len(p.vertices),4)
    def test_anchor_reuse(self):
        p=Prepared(sleeve_blocks(2));identity=id(p.tables)
        for j in range(4):
            a=p.solve(((3,3,3,3),(3,3,3,3)),zeros=((j,),()))
            self.assertEqual(a['status'],'POSITIVE');self.assertFalse(a['vectors'][0][j])
        self.assertEqual(identity,id(p.tables))
    def test_zero_coefficient_anchor(self):
        p=Prepared((Block(2,(),((1,0),(0,1))),))
        a=p.solve(((1,-1),),zeros=((1,),))
        self.assertEqual(a['value'],1)
    def test_large_binary_coefficients(self):
        v=2**240+1
        b=(Block(2,(),((v,0),(0,v))),Block(1,(),((1,),(1,))))
        a=Prepared(b).solve(((v,v),(1,)))
        self.assertEqual(a['value'],F(3,2))
    def test_master_objective(self):
        p=Prepared(sleeve_blocks(1));a=p.solve(((0,0,0,0),),master=(2,-3))
        self.assertEqual(a['value'],2)
    def test_no_positive_zero_reward(self):
        self.assertEqual(Prepared(sleeve_blocks(2)).solve(((0,)*4,)*2)['status'],'NO_POSITIVE')
    def test_invalid_query(self):
        p=Prepared(sleeve_blocks(1))
        with self.assertRaises(ValueError):p.solve(((1,2),))
        with self.assertRaises(ValueError):p.solve(((1,)*4,),zeros=((4,),))
    def test_atlas_cap(self):
        with self.assertRaises(ResourceLimit):Prepared(centroid_blocks(),max_candidates=1)


class SourceTests(unittest.TestCase):
    def test_two_block_equivalence(self):
        s=Source(4,((1,1,-1,-2),),((0,1),(2,3)))
        co=compile_two_block(s,(0,1));p=Prepared(co.blocks);c=(1,-1,2,-2)
        cc,cm,z=co.query(c);a=p.solve(cc,master=cm,zeros=z)
        self.assertEqual(a['status']=='POSITIVE',bool(positive(all_rays(s.n,s.equations,s.conflicts),c)))
    def test_two_block_bad_sign(self):
        with self.assertRaises(ValueError):compile_two_block(Source(4,((1,-1,1,-1),)),(0,1))
    def test_two_block_cross_conflict(self):
        with self.assertRaises(ValueError):compile_two_block(Source(2,((1,-1),),((0,1),)),(0,))
    def test_independent_dummy_port(self):
        co=compile_two_block(Source(2,()),(0,));a=Prepared(co.blocks).solve(((1,),(-1,)))
        self.assertEqual(a['kind'],'zero-port')
    def test_variable_separator_compiler(self):
        s=Source(6,((1,-1,0,0,-1,0),(0,0,1,-2,0,-1)),((0,1),(2,3)))
        self.assertEqual(private_components(s,(4,5)),((0,1),(2,3)))
        co=compile_variable_separator(s,(4,5));c=(1,-2,3,-4,1,1)
        cc,cm,z=co.query(c,(0,));a=Prepared(co.blocks).solve(cc,master=cm,zeros=z)
        self.assertEqual(a['status']=='POSITIVE',bool(positive(all_rays(s.n,s.equations,s.conflicts),c,(0,))))
        if a['status']=='POSITIVE':
            x=co.reconstruct(a['vectors']);self.assertTrue(verify_vector(s.n,s.equations,s.conflicts,c,x,zeros=(0,)))
    def test_master_only_constraints(self):
        s=Source(4,((0,0,1,-1),),((2,3),));co=compile_variable_separator(s,(2,3),((0,),(1,)))
        a=Prepared(co.blocks).solve(((0,1,1),(0,1,1)))
        self.assertEqual(a['status'],'NO_POSITIVE')
    def test_nonlocal_partition_rejected(self):
        s=Source(4,((1,-1,0,0),))
        with self.assertRaises(ValueError):compile_variable_separator(s,(2,3),((0,),(1,)))
    def test_overlap_rejected(self):
        with self.assertRaises(ValueError):compile_two_block(Source(3,()),(0,0))
    def test_atlas_assembly_can_be_nonextreme(self):
        blocks=nonextreme_assembly();costs=((1,)*4,(1,))
        p=Prepared(blocks);a=p.solve(costs)
        s,c,_=synchronized_source(blocks,costs)
        x=tuple(v for b in a['vectors'] for v in b)
        self.assertEqual(primitive(x),(1,3,1,3,2))
        self.assertFalse(verify_vector(s.n,s.equations,s.conflicts,c,primitive(x),extreme=True))
        w=extreme_witness(s,x,c)
        self.assertEqual(len(w['descent']),1)
        self.assertTrue(verify_vector(s.n,s.equations,s.conflicts,c,w['coordinates'],extreme=True))

    def test_source_descent(self):
        s=Source(3,((1,1,-1),));w=extreme_witness(s,(1,2,3),(1,2,0))
        self.assertTrue(w['descent'])
        self.assertTrue(verify_vector(s.n,s.equations,s.conflicts,(1,2,0),w['coordinates'],extreme=True))
    def test_source_descent_preserves_zero(self):
        s=Source(4,((1,1,-1,0),));w=extreme_witness(s,(1,2,3,0),(1,2,0,0))
        self.assertTrue(verify_vector(s.n,s.equations,s.conflicts,(1,2,0,0),w['coordinates'],zeros=(3,),extreme=True))
    def test_certificate_tamper(self):
        s=Source(3,((1,1,-1),));c=(1,2,0)
        self.assertFalse(verify_vector(s.n,s.equations,s.conflicts,c,(1,1,1),extreme=True))
        self.assertFalse(verify_vector(s.n,s.equations,s.conflicts,c,(2,0,2),extreme=True))
        self.assertFalse(verify_vector(s.n,s.equations,s.conflicts,c,(1,1,2),extreme=True))
        self.assertFalse(verify_vector(s.n,s.equations,s.conflicts,c,(1.0,0,1),extreme=True))
    def test_synchronized_tamper(self):
        b=sleeve_blocks(2);c=((3,)*4,)*2;a=Prepared(b).solve(c)
        self.assertTrue(verify_synchronized(b,c,a));a=deepcopy(a);a['value']+=1
        self.assertFalse(verify_synchronized(b,c,a))
    def test_solid_torus_meridian(self):
        tri=solid_torus();s=matching(tri);c=euler(tri)
        x=(1,1,0,0,0,0,1)
        self.assertEqual(sum(a*b for a,b in zip(c,x)),1)
        self.assertTrue(verify_vector(s.n,s.equations,s.conflicts,c,x,zeros=(2,),extreme=True))
    def test_normal_three_ports(self):
        tri=capped_solid_torus();s=matching(tri);co=compile_two_block(s,range(7))
        self.assertEqual(co.blocks[0].d,3)
        p=Prepared(co.blocks);c=euler(tri)
        cc,cm,zz=co.query(c,(2,));a=p.solve(cc,master=cm,zeros=zz)
        w=extreme_witness(s,co.reconstruct(a['vectors']),c)
        self.assertTrue(verify_vector(s.n,s.equations,s.conflicts,c,w['coordinates'],zeros=(2,),extreme=True))
    def test_gluing_reciprocity(self):
        tri=solid_torus();tri['tetrahedra'][0][1]=None
        with self.assertRaises(ValueError):matching(tri)


if __name__=='__main__':unittest.main()
