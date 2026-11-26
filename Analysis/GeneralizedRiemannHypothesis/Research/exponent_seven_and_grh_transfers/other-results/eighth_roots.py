"""Exact worst-case torsion specialization at primitive eighth roots.
No dependencies beyond Python 3. Fractions represent normalized 2-adic valuations.
The four test points are the primitive roots x of x^4 + 1, after translating
the variable by 1. Their mutual distances have valuations 1/2 and 1.
For any two centers (roots of the test quadratic), mark a nearest target for
each. An unmarked target can be chosen with the sum of the two distance
valuations at most 3/2 (choose the opposite class mod 4 if the marks agree
mod 4; otherwise choose an unmarked exponent). Thus replacing either
coefficient by a congruent value mod 4 does not change the minimum.
These 16^2 pairs of coefficients in each quadratic integer ring suffice.
The minimum valuation of the roots of a monic quartic with coefficients c_j
in descending powers is min v(c_j)/j by the Newton polygon, zeros omitted.
"""
from fractions import Fraction as F
from itertools import product

D_VALUES = (-1, 2, -2, 3, 5, 10, -10)

def add(x, y):
    return x[0] + y[0], x[1] + y[1]

def scale(n, x):
    return n * x[0], n * x[1]

def mul(x, y, D):
    # Basis 1,w where w^2=D or, for D=5, w^2=w+1.
    c, l = (1, 1) if D == 5 else (D, 0)
    p = x[1] * y[1]
    return x[0] * y[0] + c * p, x[0]*y[1] + x[1]*y[0] + l*p

def valuation(x, D):
    if x == (0, 0):
        return None
    a, b = x
    n = a*a + a*b - b*b if D == 5 else a*a - D*b*b
    return F((abs(n) & -abs(n)).bit_length()-1, 2)

def min_value(a, b, D):
    # Product of Y - (x^2+a*x+b) over x^4+1=0 equals
    # ((Y-b)^2+1)^2 + 4*a^2*(Y-b) + a^4.
    one = (1, 0)
    b2 = mul(b, b, D)
    b21 = add(b2, one)
    a2 = mul(a, a, D)
    cs = (
        scale(-4, b),
        add(scale(6,b2), scale(2,one)),
        scale(4, add(a2, scale(-1,mul(b,b21,D)))),
        add(mul(b21,b21,D), add(scale(-4,mul(a2,b,D)),mul(a2,a2,D)))
    )
    slopes = [v/j for j,c in enumerate(cs, 1) if (v := valuation(c,D)) is not None]
    return min(slopes)

def main():
    print('D   max min valuation   positive-loss threshold   (a,b) in basis 1,w')
    expected = {-1: F(1), 2: F(3,2), -2: F(3,2), 3: F(1),
                5: F(1,2), 10: F(3,2), -10: F(3,2)}
    residues = list(product(range(4), repeat=2))
    for D in D_VALUES:
        best, witness = max((min_value(a,b,D), (a,b)) for a,b in product(residues, repeat=2))
        assert best == expected[D], (D, best, expected[D])
        print(f'{D:3} {str(best):>12} {str(best-F(1,2)):>22}      {witness}')

if __name__ == '__main__':
    main()
