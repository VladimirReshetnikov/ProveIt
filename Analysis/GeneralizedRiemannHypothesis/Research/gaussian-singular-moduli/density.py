#!/usr/bin/env python3
"""Exact densities for the factorial-window tests on Gaussian prime conductors.

The probabilities refer to arithmetic tests, independent of the proof that a
particular test implies full support. All endpoints are rational. Pass
--fractions to print the exact endpoints of each joint interval.
"""
import argparse
from fractions import Fraction

PARAMETERS = ((2, 4, 25), (3, 3, 16), (7, 2, 10))
SOURCE_FINITE = {
    2: Fraction(65963232382760376856543, 75557863725914323419136),
    3: Fraction(68736524642595367189, 72945992754341572806),
    7: Fraction(9528160153068835, 9770481587462694),
}


def finite_density(p, b, radius, sign):
    """Density of passing every interval through h of lengths 1,...,radius."""
    offsets = range(1 - radius, radius)
    intervals = [(radius - 1 - a, radius + c, a + c + 1)
                 for a in range(radius) for c in range(radius - a)]

    def visit(residue, modulus, depth):
        # A zero residue in this window represents a valuation at least depth.
        prefix = [0]
        unresolved = False
        for j in offsets:
            n = (residue + j) % modulus
            value = 0
            if n == 0:
                value = depth
                unresolved = True
            else:
                while n % p == 0:
                    value += 1
                    n //= p
            prefix.append(prefix[-1] + value)
        if any(prefix[right] - prefix[left] >= b * length
               for left, right, length in intervals):
            return Fraction(0)
        if not unresolved:
            return Fraction(1)
        assert depth < b * radius
        return sum(visit(residue + k * modulus, p * modulus, depth + 1)
                   for k in range(p)) / p

    # For p=2 the sign fixes l mod 4, hence h is even. For odd p remove
    # the unique class in which 2h+sign is divisible by p.
    admissible = ([0] if p == 2 else
                  [a for a in range(p) if (2 * a + sign) % p])
    return sum(visit(a, p, 1) for a in admissible) / len(admissible)


def tail(p, b, cutoff):
    """Union bound on failures at lengths strictly larger than cutoff."""
    def event(r):
        exponent = ((b * (p - 1) - 1) * r + p - 2) // (p - 1)
        return Fraction(2 * r - 1, (p - 1) * p ** (exponent - 1))
    first = cutoff + 1
    step = p - 1
    ratio = event(first + step) / event(first)
    assert ratio < 1
    return sum(event(r) for r in range(first, first + step)) / (1 - ratio)


def combine(bounds):
    """Independent local tests, union over p. Endpoints are inclusive."""
    fail_lower = Fraction(1)
    fail_upper = Fraction(1)
    for lower, upper in bounds:
        fail_lower *= 1 - upper
        fail_upper *= 1 - lower
    return 1 - fail_upper, 1 - fail_lower


def digits(x, places, upper=False):
    scale = 10 ** places
    n = x.numerator * scale
    q = -(-n // x.denominator) if upper else n // x.denominator
    return f"{q // scale}.{q % scale:0{places}d}"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fractions', action='store_true')
    args = parser.parse_args()
    strict = {}
    augmented = {}
    for p, b, radius in PARAMETERS:
        finite = finite_density(p, b, radius, 1)
        assert finite == finite_density(p, b, radius, -1) == SOURCE_FINITE[p]
        strict[p] = (finite - tail(p, b, radius), finite)
        # Given either Gaussian sign, v_p(h)=b has mass 1/p^b.
        # For odd p this is 1/phi(p^b) - 1/phi(p^(b+1)). At p=2
        # this is the law of the valuation conditional on h being even.
        # For r<=p^b the unique multiple of p^b in an interval through
        # h is h itself. For r>=2 its sum is <= b+(r-1)(b-1)<br.
        mass = Fraction(1, p ** b)
        loss = tail(p, b, p ** b)
        assert 0 < loss < mass
        augmented[p] = (strict[p][0] + mass - loss, strict[p][1] + mass)
        print(f"p={p}: finite strict={finite}, additional mass={mass}, "
              f"additional tail <= {loss}")
    for label, primes in (("strict", set()), ("augment 7", {7}),
                          ("augment 3 and 7", {3, 7}),
                          ("augment 2, 3 and 7", {2, 3, 7})):
        lower, upper = combine([augmented[p] if p in primes else strict[p]
                                for p, _, _ in PARAMETERS])
        assert 0 < lower <= upper < 1
        print(f"{label}: [{digits(lower, 22)}, {digits(upper, 22, True)}]")
        if args.fractions:
            print(f"  exact [{lower}, {upper}]")
    # This final arithmetic predicate also includes v2(h)=5, disjoint from
    # the strict p=2 branch and the exact valuation 4 branch.
    additional = Fraction(1, 32)
    # For r<=32 the sum of valuations away from h is <=v2((r-1)!).
    # Thus 5+v2((r-1)!)<=r+3<4r for r>=2 here.
    loss = tail(2, 4, 32)
    assert 0 < loss < additional
    d2lo, d2hi = augmented[2]
    lower, upper = combine([(d2lo + additional - loss, d2hi + additional),
                            augmented[3], augmented[7]])
    print(f"dyadic valuation 5: additional mass={additional}, "
          f"additional tail <= {loss}")
    print(f"augment 2, 3 and 7, with dyadic valuation 5: "
          f"[{digits(lower, 22)}, {digits(upper, 22, True)}]")
    if args.fractions:
        print(f"  exact [{lower}, {upper}]")


if __name__ == '__main__':
    main()
