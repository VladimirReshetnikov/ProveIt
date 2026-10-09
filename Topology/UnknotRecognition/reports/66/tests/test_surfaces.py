import unittest
from itertools import permutations,product
from signed_continuations.surfaces import *
from signed_continuations.core import Candidate,compatible,reduce_family


class SurfaceTests(unittest.TestCase):
    def test_disk_and_punctured_torus(self):
        d=fan_disk(3,seams=((0,1),)); t=punctured_torus()
        self.assertEqual(inspect(d).signature,inspect(t).signature)
        self.assertEqual(inspect(d).euler,1); self.assertEqual(inspect(t).euler,-1)
        c=fan_disk(3,seams=((0,1),))
        self.assertTrue(inspect(glue(d,c),require_live=False).is_disk)
        self.assertFalse(inspect(glue(t,c),require_live=False).is_disk)
        fam=[Candidate(inspect(s).signature,-inspect(s).euler,name,"arc") for s,name in ((d,"disk"),(t,"torus"))]
        self.assertEqual(reduce_family(fam).candidates[0].token,"disk")
    def test_circle_gluing(self):
        a=annulus(); c=fan_disk(6,seams=(tuple(range(6))+(0,),))
        out=inspect(glue(a,c),require_live=False)
        self.assertEqual(out.euler,inspect(a).euler+inspect(c).euler)
        self.assertTrue(out.is_disk)
    def test_pants_two_caps(self):
        a=planar_holes(); c=disjoint_surfaces([fan_disk(4,seams=((0,1,2,3,0),)) for _ in range(2)])
        ai,ci=inspect(a),inspect(c)
        self.assertEqual(ai.euler,-1); self.assertEqual(ci.components,2)
        self.assertTrue(compatible(ai.signature,ci.signature))
        self.assertTrue(inspect(glue(a,c),require_live=False).is_disk)
    def test_orientation_conflict(self):
        a=fan_disk(8,seams=((0,1),(4,5)))
        ann=inspect(glue(a,a,reverse=(False,False)),require_live=False)
        mob=inspect(glue(a,a,reverse=(False,True)),require_live=False)
        self.assertEqual((ann.euler,ann.orientable,ann.boundary_components),(0,True,2))
        self.assertEqual((mob.euler,mob.orientable,mob.boundary_components),(0,False,1))
    def test_genuine_mesh_exhaustive_gluings(self):
        count=0
        for r in range(1,5):
            seams=tuple((3*i,3*i+1) for i in range(r))
            a=fan_disk(3*r+3,seams=seams); ai=inspect(a)
            for perm in permutations(range(r)):
                b=Surface(a.triangles,tuple(seams[i] for i in perm)); bi=inspect(b)
                for rev in product((False,True),repeat=r):
                    out=inspect(glue(a,b,reverse=rev),require_live=False)
                    self.assertEqual(out.euler,2-r)
                    self.assertEqual(out.components==1 and out.orientable,
                                     compatible(ai.signature,adjusted_completion(bi,rev)))
                    count+=1
        self.assertEqual(count,442)
    def test_cyclic_geometry_not_in_signature(self):
        seams=((0,1),(3,4),(6,7)); a=fan_disk(12,seams=seams)
        observed=set()
        for perm in permutations(range(3)):
            b=Surface(a.triangles,tuple(seams[i] for i in perm))
            self.assertEqual(inspect(a).signature,inspect(b).signature)
            out=inspect(glue(a,b),require_live=False)
            self.assertTrue(out.orientable); self.assertEqual(out.euler,-1)
            observed.add(out.boundary_components)
        self.assertEqual(observed,{1,3})
    def test_closed_surface_not_disk(self):
        a=fan_disk(5,seams=((0,1,2,3,4,0),))
        out=inspect(glue(a,a),require_live=False)
        self.assertEqual((out.euler,out.boundary_components),(2,0))
        self.assertFalse(out.is_disk)
    def test_orphan_geometry(self):
        a=disjoint_surfaces([fan_disk(3,seams=((0,1),)),fan_disk(3)])
        with self.assertRaises(ValueError): inspect(a)
    def test_bad_seam(self):
        with self.assertRaises(ValueError): inspect(fan_disk(5,seams=((0,1),(1,2))))
        with self.assertRaises(ValueError): inspect(fan_disk(5,seams=((0,2),)))
    def test_nonmanifold_and_duplicates(self):
        with self.assertRaises(ValueError): inspect(Surface(((0,1,2),(2,1,0))))
        with self.assertRaises(ValueError): inspect(Surface(((0,1,2),(0,1,3),(0,1,4))))
        with self.assertRaises(ValueError): inspect(Surface(((0,1,2),(0,3,4))))
    def test_reversal_mismatch(self):
        a=fan_disk(5,seams=((0,1),))
        with self.assertRaises(ValueError): glue(a,a,reverse=(0,))
