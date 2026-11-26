"""Exact examples for the all-witness Stickelberger gcd. Run with Python 3 + SymPy."""
from itertools import product
from math import factorial, gcd, lcm
import json

from sympy import Poly, QQ, Rational, Symbol, bernoulli, cyclotomic_poly, factorint, invert, primerange

z = Symbol("z")


def character_tables(modulus):
    """Construct characters by extending homomorphisms to a cyclic enlargement."""
    units = [a for a in range(modulus) if gcd(a, modulus) == 1]
    identity = 1 % modulus
    orders = []
    for a in units:
        u = a
        order = 1
        while u != identity:
            u = u * a % modulus
            order += 1
        orders.append(order)
    exponent = lcm(*orders)
    tables = [{identity: 0}]
    for a in units:
        if a in tables[0]:
            continue
        cosets = [identity]
        u = a
        while u not in tables[0]:
            cosets.append(u)
            u = u * a % modulus
        extended = []
        for table, image in product(tables, range(exponent)):
            if (image * len(cosets) - table[u]) % exponent:
                continue
            extended.append({b * v % modulus: (h + i * image) % exponent
                             for b, h in table.items() for i, v in enumerate(cosets)})
        tables = extended
    assert len(tables) == len(units)
    for table in tables:
        assert all((table[a * b % modulus] - table[a] - table[b]) % exponent == 0
                   for a in units for b in units)
    return exponent, tables


def denominator(poly):
    return lcm(*(int(t.q) for t in poly.all_coeffs()))


def check_characters(n, e):
    exponent, tables = character_tables(n)
    phi = Poly(cyclotomic_poly(exponent, z), z, domain=QQ)
    roots = [Poly(z**j, z, domain=QQ).rem(phi) for j in range(exponent)]
    zero = Poly(0, z, domain=QQ)
    one = Poly(1, z, domain=QQ)
    const = factorial(e + 2) * (e + 1) * n
    old_denoms, new_denoms = [], []
    samples = 0
    for chi in tables:
        if (chi[-1 % n] == 0) != (e % 2 == 1):
            continue
        bsum = sum((factorial(e + 2) * n**(e + 1)
                    * bernoulli(e + 1, Rational(a, n)) * roots[j]
                    for a, j in chi.items()), zero)
        inverse = invert(2 * bsum, phi)
        assert (2 * bsum * inverse).rem(phi) == one
        old_denoms.append(denominator(inverse))
        new_denoms.append(denominator(const * inverse))
        # Test the original floor congruence directly, including composite m
        # and m sharing normalization factors. The proof covers all moduli.
        x = new_denoms[-1]
        for c in (1 + n, 1 + 2 * n, 1 + 4 * n):
            w = const * c**e * x * inverse
            assert denominator(w) == 1
            for m in range(2, 25):
                if gcd(c, m) != 1:
                    continue
                totals = [0 for _ in roots]
                for a in range(n * m):
                    if a % n in chi:
                        totals[chi[a % n]] += (c * a // (n * m)) * a**e
                floor_sum = sum((v * root for v, root in zip(totals, roots)), zero)
                error = ((c**(e + 1) - 1) * x * one - 2 * w * floor_sum).rem(phi)
                assert all(int(t) % m == 0 and t.is_Integer for t in error.all_coeffs())
                samples += 1
    d = lcm(*old_denoms)
    q = lcm(*new_denoms)
    assert q == d // gcd(d, const)
    return d, q, samples


def val(n, p):
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def auxiliary_gcd(n, e):
    powers = {}
    for p in {2, *factorint(n), *primerange(3, e + 3)}:
        a = val(n, p)
        if p == 2:
            powers[p] = val(e * (e + 1), 2) + (2 * a if a >= 2 else 3)
        elif a:
            powers[p] = val(e * (e + 1), p) + 2 * a
        else:
            powers[p] = sum(1 + val(j, p) for j in (e, e + 1) if j % (p - 1) == 0)
    m = 1
    for p, h in powers.items():
        m *= p**h
    return int(m)


def f(c, e):
    return (c**e - 1) * (c**(e + 1) - 1)


def least_witness(n, e, q):
    # Subsets of all eligible c, keeping only the (gcd of c, lcm of costs).
    bound = lcm(q, f(n + 1, e), f(2 * n + 1, e))
    states = {(0, q)}
    candidates = []
    c = n + 1
    while f(c, e) <= bound:
        cost = f(c, e)
        states |= {(gcd(g, c), new_value) for g, value in states
                   if (new_value := lcm(value, cost)) <= bound}
        candidates.append(c)
        c += n
    best = min(value for g, value in states if g == 1)
    eligible = [c for c in candidates if best % f(c, e) == 0]
    assert gcd(*eligible) == 1
    return best, eligible


def case(n, e):
    d, q, count = check_characters(n, e)
    m = auxiliary_gcd(n, e)
    g = lcm(q, m)
    current = 0
    certificates = []
    for j in range(2, 501):
        b = 1 + n * j
        for i in range(1, j):
            a = 1 + n * i
            if gcd(a, b) == 1:
                x = lcm(q, f(a, e), f(b, e))
                assert x % g == 0
                if gcd(current, x) != current:
                    current = gcd(current, x)
                    certificates.append([a, b, x])
        if current == g:
            break
    assert current == gcd(*(row[2] for row in certificates)) == g
    least, eligible = least_witness(n, e, q)
    return dict(N=n, e=e, M=m, primitive_denominator=q, old_gcd=lcm(d, m), exact_gcd=g,
                least_witness=least, eligible_auxiliaries_at_least=eligible,
                gcd_certificate=certificates, direct_congruences=count)


if __name__ == "__main__":
    cases = [(1, 2), (1, 11), (3, 9), (5, 1), (5, 2), (7, 2), (8, 2),
             (9, 3), (11, 1), (12, 2), (15, 1)]
    print(json.dumps([case(*arg) for arg in cases], indent=2))
