"""Verify the 2-adic disk on cyclic isogenies of degrees 3 and 5.
Requires SymPy. All polynomials and valuations are exact.
"""
import sympy as sp

x, y = sp.symbols("x y")
cubic = x**3 - x
division_3 = 3*x**4 - 6*x**2 - 1
division_5 = 32*cubic**2 * (x**6 - 5*x**4 - 5*x**2 + 1) - division_3**3


def reduce_mod_factor(expression, factor):
    numerator, denominator = sp.fraction(sp.cancel(expression))
    return sp.rem(numerator * sp.invert(denominator, factor, x), factor, x)


def valuation_2(n):
    n = abs(int(n))
    assert n != 0
    return (n & -n).bit_length() - 1


for degree, division_polynomial, expected in [
    (3, division_3, 27*y**2 - 2399040*y - 18593344),
    (5, division_5, y**2 - 25481191680*y - 97863834942720),
]:
    image_factors = set()
    for factor, _ in sp.factor_list(division_polynomial)[1]:
        # Representatives of the nonzero points modulo the involution P -> -P.
        xs = [x]
        if degree == 5:
            xs.append(reduce_mod_factor((x*x+1)**2 / (4*cubic), factor))
        a = reduce_mod_factor(-1 - 10*sum(3*z*z-1 for z in xs), factor)
        b = reduce_mod_factor(-14*sum(z*(5*z*z-3) for z in xs), factor)
        normalized = reduce_mod_factor(-27*b*b / (4*a**3+27*b*b), factor)
        resultant = sp.resultant(factor, y-normalized, x)
        image_factors.update(poly for poly, _ in sp.factor_list(resultant)[1])
    assert image_factors == ({expected} if degree == 3 else {y, expected})
    disc = sp.discriminant(expected, y)
    # The leading coefficient is odd and both normalized j/1728 are units.
    distance = valuation_2(disc)//2
    assert valuation_2(disc) == 2*(4 if degree == 3 else 5)
    print('degree', degree, 'descending quadratic for j/1728 - 1:', expected)
    print('valuation of the difference of its roots:', distance)
