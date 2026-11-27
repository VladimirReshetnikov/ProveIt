"""Checks for the sparse-prime reconstruction note. Python 3, mpmath.

Use: python check_mellin.py
The first two checks are exact. The last one evaluates a finite truncation
of the meromorphic continuation of the q=1 ordinary-prime Dirichlet series.
"""
from fractions import Fraction
from itertools import permutations
from math import gcd, prod
from mpmath import mp


def check_central_evaluation():
    """Verify the cardinal-polynomial calculation over the rational numbers."""
    count = 0
    for degree_radius in (1, 3, 8, 15):
        nodes = list(range(-degree_radius, degree_radius + 1))
        for numerator in (0, 1, 4, 6):
            theta = Fraction(numerator, 7)
            weights = [
                prod((theta - j) / (i - j) for j in nodes if j != i)
                for i in nodes
            ]
            assert sum(abs(w) for w in weights) <= len(nodes) * (degree_radius + 1)
            for exponent in range(len(nodes)):
                assert sum(w * i**exponent for w, i in zip(weights, nodes)) == theta**exponent
                count += 1
    print(f"{count} exact polynomial reconstruction checks passed")


def mobius(n):
    sign = 1
    factor = 2
    while factor * factor <= n:
        if n % factor == 0:
            n //= factor
            if n % factor == 0:
                return 0
            sign = -sign
        factor += 1
    return sign if n == 1 else -sign


def check_prime_power_removal():
    """At p^r, every divisor k|r contributes mu(k) * 1_{p^r=1 mod q}."""
    count = 0
    for modulus in range(1, 41):
        for unit in range(1, modulus + 1):
            if gcd(unit, modulus) != 1:
                continue
            for r in range(1, 31):
                coefficient = sum(
                    mobius(k) for k in range(1, r + 1)
                    if r % k == 0 and pow(pow(unit, r // k, modulus), k, modulus) == 1 % modulus
                )
                assert coefficient == int(r == 1 and unit % modulus == 1 % modulus)
                count += 1
    print(f"{count} exact residue-class prime-power cancellations passed")


def compose(g, h):
    return tuple(g[a] for a in h)


def check_square_class_identity():
    count = 0
    for n in range(2, 6):
        identity = tuple(range(n))
        group = list(permutations(identity))
        involutions = [g for g in group if g != identity and compose(g, g) == identity]
        coset_families = []
        for c in involutions:
            coset_families.append([
                (x, compose(x, c)) for x in group if x < compose(x, c)
            ])
        for g in group:
            fixed = sum(compose(g, x) in (x, y) for family in coset_families for x, y in family)
            regular = len(group) if g == identity else 0
            assert len(group) * (compose(g, g) == identity) == 2 * fixed + (1-len(involutions))*regular
            count += 1
    print(f"{count} exact permutation-character checks passed in S2 through S5")


def finite_splitting_example():
    # t=4 belongs to the prescribed grid. For the cubic splitting field and
    # p>3, the cubic has three roots iff p=1 mod 3 and 2 is a cubic residue.
    t = 4
    mp.dps = 30
    upper = int(mp.exp(2*t))
    split = []
    for p in range(5, upper + 1):
        if any(p % d == 0 for d in range(2, int(p**0.5) + 1)):
            continue
        if p % 3 == 1 and pow(2, (p-1)//3, p) == 1:
            split.append(p)
    for p in split:
        assert sum(pow(r, 3, p) == 2 for r in range(p)) == 3
    def weight(p):
        u = t - mp.log(p)
        return mp.exp(u) * mp.besselk(mp.j * u, 1).real / mp.pi
    observed = 6 * mp.fsum(mp.log(p) * weight(p) for p in split) - mp.exp(t-1)
    print(f"S3 example at t=4: {len(split)} split primes in [1, floor(exp(8))],")
    print("  first five:", split[:5], "centered finite sample:", mp.nstr(observed, 12))


def prime_log_series(s, cutoff=100):
    """A_1(s) = sum_k mu(k) (-zeta'/zeta)(ks), truncated after cutoff."""
    terms = []
    for k in range(1, cutoff + 1):
        coefficient = mobius(k)
        if coefficient:
            point = k * s
            terms.append(-coefficient * mp.zeta(point, derivative=1) / mp.zeta(point))
    return mp.fsum(terms)


def check_residues():
    mp.dps = 35
    center = mp.mpf(1) / 2
    for point, target in [(center, -center), (mp.zetazero(1), -1)]:
        displacement = mp.mpf("0.000001")
        approximation = displacement * prime_log_series(point + displacement)
        print("q=1, pole near", mp.nstr(point, 10), "estimated residue", mp.nstr(approximation, 10))
        assert abs(approximation - target) < mp.mpf("0.00002")


if __name__ == "__main__":
    check_central_evaluation()
    check_prime_power_removal()
    check_square_class_identity()
    finite_splitting_example()
    check_residues()
