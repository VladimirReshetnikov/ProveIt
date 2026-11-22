"""Exact finite checks for the residue-space certificates. Python 3, standard library."""
from fractions import Fraction
from itertools import product
from math import prod


def residual(coeff, den, target, n):
    return den * target(n) - sum(a * (n % k) for k, a in enumerate(coeff, 2))


def weight_energy(coeff, den, target, n):
    return sum((Fraction(residual(coeff, den, target, i)**2, i * (i + 1))
                for i in range(1, n + 1)), Fraction())


def cleared_energy(coeff, den, target, n):
    factors = [i * (i + 1) for i in range(1, n + 1)]
    p = prod(factors)
    s = sum(residual(coeff, den, target, i)**2 *
            prod(factors[:i - 1] + factors[i:])
            for i in range(1, n + 1))
    return s, p


def test():
    one = lambda n: 1
    delta = lambda n: int(n == 2)
    step = lambda n: int(n >= 2)
    checked = 0
    for coeff in product((-1, 0, 1), repeat=3):
        for d, f in product((1, 2), (one, delta, step)):
            budget = d + sum((i + 1) * abs(a) for i, a in enumerate(coeff))
            prev_upper = Fraction(budget**2)
            for j in range(11):
                s, p = cleared_energy(coeff, d, f, j)
                e = weight_energy(coeff, d, f, j)
                assert e == Fraction(s, p)
                upper = e + Fraction(budget**2, j + 1)
                assert e <= upper <= prev_upper
                prev_upper = upper
                checked += 1
    for m, k, n in product(range(1, 8), range(2, 9), range(100)):
        assert n % (m * k) == n % m + m * ((n // m) % k)
    for m in range(1, 9):
        for j in range(1, 20):
            mass = sum(Fraction(1, n * (n + 1)) for n in range(j*m, (j+1)*m))
            assert mass == Fraction(1, m*j*(j+1))
    s, p = cleared_energy([1], 1, one, 24)
    upper = Fraction(s, p) + Fraction(4, 25)
    assert 2 * upper < 1
    print(f"{checked} finite energies and upper estimates checked")
    print("4,900 dilation identities and 152 block masses checked")
    print(f"constant target, R_2, t=2, J=24: upper = {upper} < 1/2")


if __name__ == "__main__":
    test()
