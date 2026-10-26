"""Non-Lean model tests: selected packing certificate plus excluded growth comparison.

The symbolic test requires SymPy, already available in this research workspace.
No test in this file checks Lean syntax, elaboration, typeclass resolution or axioms.
"""
import unittest
import sympy as s

class ArithmeticSanityTests(unittest.TestCase):
    def test_exact_signed_polynomial_certificate(self):
        q,C,F,MC,MF,J,beta=s.symbols('q C F MC MF J beta')
        four=(C-1)+(MC*J+1)+q*(F+(MF*J-1))+q**2*(q-C)+q**3*(q-F-1)
        rank=(q*(q-F)-C)*(q**2-1)+(MC+q*(MF+beta))*J
        self.assertEqual(s.expand(four-rank+q*(beta*J+1-q)),0)

    def test_natural_cast_domains_and_packing_samples(self):
        cases=0
        for beta in range(1,9):
            for J in range(1,5):
                q=beta*J+1
                for C in range(1,q):
                    for F in range(q-C):
                        for MC in (0,1,3):
                            for MF in (1,2,5):
                                self.assertTrue(1<=C and 1<=MF*J and C<=q and F<=q and 1<=q-F)
                                four=(C-1)+(MC*J+1)+q*(F+(MF*J-1))+q**2*(q-C)+q**3*(q-F-1)
                                rank=(q*(q-F)-C)*(q**2-1)+(MC+q*(MF+beta))*J
                                self.assertEqual(four,rank)
                                cases+=1
        self.assertEqual(cases,29160)

    def test_missing_high_mask_positive_guard_is_unsound(self):
        q,C,F,MC,MF,beta,J=4,1,0,0,0,3,1
        sub=lambda a,b:max(0,a-b)
        four=sub(C,1)+(MC*J+1)+q*(F+sub(MF*J,1))+q**2*sub(q,C)+q**3*sub(sub(q,F),1)
        rank=(q*(q-F)-C)*(q**2-1)+(MC+q*(MF+beta))*J
        self.assertEqual((four,rank),(241,237))

    def test_cube_growth_including_zero_window(self):
        for u in range(4097):
            self.assertEqual((2**u)**3,2**(3*u))
            self.assertLessEqual(2*u,3*u)
            self.assertLess(3*u,2**(3*u))

if __name__=='__main__':
    unittest.main(verbosity=2)
