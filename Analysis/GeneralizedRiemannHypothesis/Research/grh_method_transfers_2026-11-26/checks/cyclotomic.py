"""Exact characterwise comparisons for the Voronoi/Kolyvagin argument.

Use: python checks/cyclotomic.py
Requires Python 3.9+ and SymPy. All arithmetic is rational or integral.
"""
from functools import reduce
from itertools import combinations, product
from math import factorial, gcd, lcm
import json

from sympy import Matrix, Poly, QQ, Rational, bernoulli, cyclotomic_poly
from sympy import factorint, invert, primerange, primitive_root, symbols

z = symbols("z")


def character_coordinates(modulus):
    """Return orders of cyclic factors and exponent coordinates of units."""
    units = [u for u in range(modulus) if gcd(u, modulus) == 1]
    coordinates = {u: [] for u in units}
    orders = []
    for p, a in factorint(modulus).items():
        q = p**a
        if q == 2:
            continue
        if p == 2 and a >= 3:
            orders.extend([2, q // 4])
            table = {(-1)**s * pow(5, j, q) % q: (s, j)
                     for s in range(2) for j in range(q // 4)}
        else:
            order = (q // p) * (p - 1)
            generator = int(primitive_root(q))
            orders.append(order)
            table = {pow(generator, j, q): (j,) for j in range(order)}
        for u in units:
            coordinates[u].extend(table[u % q])
    return orders, coordinates


def corrected_determinant(N, e, weights, units):
    def entry(u, v):
        t = (v * pow(u, -1, N)) % N
        return (2 * weights[t] + (-1)**e * int(t == 1 % N)
                + int(t == -1 % N))
    return abs(int(Matrix([[entry(u, v) for v in units] for u in units]).det()))


def scalar(N, e):
    orders, coordinates = character_coordinates(N)
    E = lcm(*orders)
    phi = Poly(cyclotomic_poly(E, z), z, domain=QQ)
    weights = {}
    for u in coordinates:
        b = factorial(e + 2) * N**(e + 1) * bernoulli(e + 1, Rational(u, N))
        assert b.is_Integer
        weights[u] = int(b)
    denominators = []
    for k in product(*(range(order) for order in orders)):
        def exponent(u):
            return sum(j * t * (E // m)
                       for j, t, m in zip(k, coordinates[u], orders)) % E
        # A value at -1 is +1 or -1, with exponent zero in the first case.
        if (exponent((-1) % N) == 0) != ((-1)**(e + 1) == 1):
            continue
        eig = Poly(sum(2 * b * z**exponent(u) for u, b in weights.items()),
                   z, domain=QQ).rem(phi)
        inv = invert(eig, phi)
        assert (eig * inv).rem(phi) == Poly(1, z, domain=QQ)
        denominator = lcm(*(int(t.q) for t in inv.all_coeffs()))
        assert all((denominator * c).is_Integer for c in inv.all_coeffs())
        denominators.append(denominator)
    det = corrected_determinant(N, e, weights, coordinates)
    D = lcm(*denominators)
    assert det % D == 0
    return D, det


def valuation(n, p):
    result = 0
    while n % p == 0:
        result += 1
        n //= p
    return result


def local_cost(N, e):
    M = 1
    for p in {2, *factorint(N), *primerange(3, e + 3)}:
        a = valuation(N, p)
        if p == 2:
            m = (2 * a if a >= 2 else 3) + valuation(e * (e + 1), p)
        elif a:
            m = 2 * a + valuation(e * (e + 1), p)
        else:
            m = sum(1 + valuation(j, p) for j in (e, e + 1)
                    if j % (p - 1) == 0)
        M *= p**m
    return int(M)


def F(c, e):
    return (c**e - 1) * (c**(e + 1) - 1)


def analyze(N, e):
    D, det = scalar(N, e)
    M = local_cost(N, e)
    H = lcm(D, M)
    base = F(N + 1, e) * F(2 * N + 1, e) * det
    fixed = lcm(D, F(N + 1, e), F(2 * N + 1, e))
    assert base % fixed == fixed % H == 0
    # Independently exhibit a finite list of genuine global witnesses with gcd H.
    divis = 0
    certificate = []
    for v in range(2, 501):
        b = 1 + N * v
        for u in range(1, v):
            a = 1 + N * u
            if gcd(a, b) != 1:
                continue
            value = lcm(D, F(a, e), F(b, e))
            assert value % H == 0
            new_divis = gcd(divis, value)
            if new_divis != divis:
                certificate.append([a, b, value])
                divis = new_divis
            if divis == H:
                break
        if divis == H:
            break
    assert divis == H, (N, e, divis, H)
    assert reduce(gcd, [r[2] for r in certificate]) == H
    return dict(N=N, e=e, abs_det=det, character_scalar=D, auxiliary_cost=M,
                upstream=base, fixed_pair=fixed, witness_gcd=H,
                finite_gcd_certificate=certificate)


def check_least_example():
    # Any smaller positive witness has c >= 2 and F(c) <= X.
    N, e, cutoff = 5, 1, 8400
    c = 1 + N
    candidates = []
    while F(c, e) <= cutoff:
        candidates.append(c)
        c += N
    assert candidates == [6, 11, 16]
    for X in range(1, cutoff + 1):
        eligible = [c for c in candidates if X % F(c, e) == 0]
        if reduce(gcd, eligible, 0) == 1:
            assert X == cutoff
            return
    raise AssertionError("the exhibited witness did not pass")


if __name__ == "__main__":
    check_least_example()
    cases = [(1, 11), (5, 1), (5, 2), (7, 2), (8, 1), (9, 3),
             (12, 2), (15, 1)]
    print(json.dumps([analyze(*case) for case in cases], indent=2))
