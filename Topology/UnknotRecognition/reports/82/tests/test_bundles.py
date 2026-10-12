import unittest
from corner_kernel import Surface
from corner_kernel.bundles import orientation_bundle_summary as summary

class BundleTests(unittest.TestCase):
    def test_disk_annulus_mobius(self):
        self.assertTrue(summary(Surface(1,1))['is_ball_given_certified_bundle'])
        self.assertEqual(summary(Surface(0,2))['handlebody_genus'],1)
        self.assertEqual(summary(Surface(0,1,False))['handlebody_genus'],1)
    def test_projective_plane_spherical_nonball(self):
        d=summary(Surface(1,0,False))
        self.assertEqual(d['total_boundary_genus_multiplicity'],[(0,1)])
        self.assertIsNone(d['handlebody_genus'])
        self.assertFalse(d['is_ball_given_certified_bundle'])
    def test_closed_orientable(self):
        d=summary(Surface(-2,0))
        self.assertEqual(d['total_boundary_genus_multiplicity'],[(2,2)])
        self.assertFalse(d['is_ball_given_certified_bundle'])

class MixedNamespaceTests(unittest.TestCase):
    def test_silent_interior_orbits_cancel(self):
        from corner_kernel.compiler import compile_boundary,Port,verify_count_transcript
        from corner_kernel.oracles import ExplicitOracle
        from corner_kernel import signature
        # Four boundary vertices, plus ten unrelated interior corner classes.
        v=ExplicitOracle(14,[])
        r=ExplicitOracle(14,[(1,2),(3,0)])
        f=ExplicitOracle(14,[(0,1),(1,2),(2,3),(3,0)])
        ports=[Port('a',0,0,1),Port('b',0,2,3)]
        k,m=compile_boundary([Surface(1,1)],ports,v,r,full_boundary_count=f)
        self.assertEqual(m.passive_boundary,0)
        self.assertEqual(signature(k),((1,1,True),))
        self.assertTrue(verify_count_transcript(m.transcript,v,r,f))
        with self.assertRaises(ValueError): compile_boundary([Surface(1,1)],ports,v,r)
