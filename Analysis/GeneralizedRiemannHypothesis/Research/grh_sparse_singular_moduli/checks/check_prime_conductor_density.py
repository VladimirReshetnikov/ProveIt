"""Exact cylinder masses and a geometric upper bound for the omitted radii."""
from fractions import Fraction

P = 7


def truncated_valuation(value, max_power):
    v = 0
    while v < max_power and value % P == 0:
        v += 1
        value //= P
    return v


def classification(h, depth, radius):
    # In class h mod 7^depth all displayed valuations are known lower bounds.
    # A term truncated at depth may become arbitrarily large among the lifts.
    unresolved = False
    for offsets in (range(0, -radius, -1), range(1, radius + 1)):
        total = 0
        ambiguous = False
        for r, j in enumerate(offsets, 1):
            v = truncated_valuation(h + j, depth)
            total += v
            ambiguous |= v == depth
            if total >= r:
                return "bad"
            unresolved |= ambiguous
    return "split" if unresolved else "good"


def exact_finite_density(radius):
    good = Fraction(0)
    for sign in (-1, 1):
        # When f ranges over primes congruent to sign mod 4, f=2h+sign.
        waiting = [(h, 1, Fraction(1, 12)) for h in range(P)
                   if (2 * h + sign) % P]
        while waiting:
            h, depth, mass = waiting.pop()
            status = classification(h, depth, radius)
            if status == "good":
                good += mass
            elif status == "split":
                assert depth < radius
                modulus = P ** depth
                waiting.extend((h + c * modulus, depth + 1, mass / P)
                               for c in range(P))
    return good


def tail_bound(radius):
    # Group terms with the same residue modulo 6. u(r+6)/u(r)=
    # (1+6/r)/7^5 with u(r)=2r/phi(7^ceil(5r/6)).
    start = radius + 1
    ratio = Fraction(start + 6, start * P ** 5)
    return sum(Fraction(2*r, 6 * P**((5*r+5)//6 - 1))
               for r in range(start, start+6)) / (1 - ratio)


if __name__ == "__main__":
    for R in [1, 6, 10, 20, 40]:
        density = exact_finite_density(R)
        error = tail_bound(R)
        print(f"R={R}: exact initial density {density}, "
              f"{float(density):.16f}, omitted <= {float(error):.4g}")
