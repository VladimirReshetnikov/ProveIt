import unittest
from fractions import Fraction as Q
from observe import obs,compose,companion,matpoly,matmul

class ObserveTests(unittest.TestCase):
    def test_companion(self):
        for f in ([Q(-2),Q(0),Q(1)],[Q(3),Q(-1),Q(4),Q(1)],[Q(-3),Q(1)]):
            self.assertEqual(obs(f,[Q(0),Q(1)]),f)
    def test_square(self):
        for c in range(-5,6):
            f=[Q(-c),Q(0),Q(1)]
            self.assertEqual(obs(f,[Q(0),Q(0),Q(1)]),[Q(c*c),Q(-2*c),Q(1)])
    def test_composition(self):
        f=[Q(-2),Q(0),Q(1)]; g=[Q(1),Q(1)]; h=[Q(3),Q(0),Q(1)]
        self.assertEqual(matpoly(compose(h,g),companion(f)),matpoly(h,matpoly(g,companion(f))))
        self.assertEqual(obs(f,compose(h,g)),obs(f,[Q(4),Q(2),Q(1)]))
    def test_nilpotent(self):
        self.assertEqual(obs([Q(0),Q(0),Q(0),Q(1)],[Q(0),Q(1)]),[Q(0),Q(0),Q(0),Q(1)])

if __name__=='__main__': unittest.main()
