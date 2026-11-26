"""Check the constructive optimality certificates for selected odd abelian groups.

Only integer arithmetic is used, including evaluation of the rational
cyclotomic sums in the inverse formulas.
"""
from fractions import Fraction
from itertools import product
from math import gcd, lcm, prod


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def mobius_table(n):
    mu = {1: 1}
    for k in range(2, n + 1):
        mu[k] = -sum(mu[d] for d in divisors(k) if d < k)
    return mu


def check_group(moduli):
    exponent = lcm(*moduli)
    points = tuple(product(*(range(n) for n in moduli)))
    zero = tuple(0 for _ in moduli)
    mu = mobius_table(exponent)
    phi = {d: sum(gcd(k, d) == 1 for k in range(1, d + 1))
           for d in divisors(exponent)}

    def phase(a, psi):
        return sum(x*y*(exponent//n) for x, y, n in zip(a, psi, moduli)) % exponent

    def ramanujan(n, k):
        return sum(d*mu[n//d] for d in divisors(gcd(n, k)))

    seen = set()
    for a in points:
        if a == zero or a in seen:
            continue
        order = lcm(*(n//gcd(n, x) for x, n in zip(a, moduli)))
        generators = {tuple(k*x % n for x, n in zip(a, moduli))
                      for k in range(order) if gcd(k, order) == 1}
        assert not (generators & seen)
        seen |= generators
        m = {psi: len(generators) - ramanujan(order, phase(a, psi)*order//exponent)
             for psi in points}
        assert m[zero] == 0 and min(m.values()) >= 0 and max(m.values()) > 0
        for b in points:
            # The m-vector is rational-Galois-invariant. Averaging each
            # character value over the cyclotomic embeddings leaves T_m fixed.
            transform = sum(
                multiplicity * Fraction(ramanujan(exponent, phase(b, psi)), phi[exponent])
                for psi, multiplicity in m.items()
            )
            expected = prod(moduli) * (len(generators)*(b == zero) - (b in generators))
            assert transform == expected
    assert seen == set(points) - {zero}
    count = sum(Fraction(1, phi[lcm(*(n//gcd(n,x) for x,n in zip(a,moduli)))])
                for a in seen)
    print(f"A with cyclic factors {moduli}: {count} generator tests, all witnesses verified.")


if __name__ == "__main__":
    for example in ((5,), (9,), (15,), (3, 3), (3, 9)):
        check_group(example)
