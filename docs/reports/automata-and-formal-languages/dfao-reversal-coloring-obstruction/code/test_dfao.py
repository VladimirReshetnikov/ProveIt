from __future__ import annotations
import copy
import unittest
from itertools import product
from dfao import (cyclic_membership, landau, missing_certificate, orbital_chromatic,
                  orbital_edges, proper, refine_coloring, reverse_orbit,
                  three_coloring, validate_map)
from certificate_checker import verify


class ExactTests(unittest.TestCase):
    def test_landau(self):
        self.assertEqual([landau(i) for i in range(1, 11)], [1,2,3,4,6,6,12,15,20,30])

    def test_invalid_input(self):
        for invalid in ((), (1,), (0,-1), (0,2), (False,0)):
            with self.assertRaises(ValueError): validate_map(invalid)

    def test_three_state_sharpness(self):
        orbit=reverse_orbit(((1,2,0),(0,0,2)),(0,1,2),3)
        missing=set(product(range(3),repeat=3))-set(orbit)
        self.assertEqual(missing, {(0,2,1),(1,0,2),(2,1,0)})

    def test_rotation_failure(self):
        result=cyclic_membership((1,2,0),(0,1,2),(0,2,1))
        self.assertFalse(result['member'])
        self.assertEqual(result['reason'],'no_rotation')

    def test_incompatible_crt(self):
        result=cyclic_membership((1,0,3,2),(0,1,0,1),(0,1,1,0))
        self.assertFalse(result['member'])
        self.assertEqual(result['reason'],'inconsistent_CRT')

    def test_crt_success(self):
        result=cyclic_membership((1,0,3,4,2),(0,1,0,1,2),(1,0,1,2,0))
        self.assertTrue(result['member'])
        self.assertEqual(result['exponent'],1)

    def test_cross_cycle_graph(self):
        a=(1,0,3,4,2)
        self.assertEqual(len(orbital_edges(a,(0,2))),6)
        self.assertEqual(orbital_chromatic(a,(0,2),3),30)

    def test_odd_cycle_graph(self):
        a=(1,2,3,4,0); edges=orbital_edges(a,(0,1))
        c=three_coloring(5,edges)
        self.assertTrue(proper(c,edges))
        self.assertEqual(set(c),{0,1,2})
        d=refine_coloring(c,5)
        self.assertTrue(proper(d,edges))
        self.assertEqual(len(set(d)),5)

    def test_all_certificate_cases(self):
        for a,b in [((1,2,0),(1,0,2)),((1,2,0),(0,0,2)),((0,0,2),(0,1,1))]:
            cert=missing_certificate(a,b,(0,1,2),3)
            self.assertTrue(verify(cert))
            bad=copy.deepcopy(cert);bad['target']=[0,1,2]
            self.assertFalse(verify(bad))

    def test_orbit_limit_no_partial_answer(self):
        with self.assertRaises(RuntimeError):
            reverse_orbit(((1,2,0),(0,0,2)),(0,1,2),3,max_states=2)


if __name__ == '__main__': unittest.main(verbosity=2)
