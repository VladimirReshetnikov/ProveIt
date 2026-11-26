"""Run with Python 3.8+; no external packages. Certifies the explicit Rankin perturbation."""
from fractions import Fraction
from itertools import product
from math import isqrt, prod


def primes_through(n):
    flags = bytearray([1]) * (n + 1)
    flags[:2] = bytes(2)
    for p in range(2, isqrt(n) + 1):
        if flags[p]:
            flags[p*p::p] = bytes((n-p*p)//p + 1)
    return [p for p in range(2, n + 1) if flags[p]]


def check_local_model(markers):
    """Test all mixed progressions in a truncated three-coordinate version."""
    def rankin_exponent(n):
        while n:
            n, digit = divmod(n, 3)
            if digit == 2:
                return False
        return True

    old_exponents = [n for n in range(42) if rankin_exponent(n)]
    double = {2*k for k in markers}
    retained = set()
    for t, q, r in product(old_exponents, repeat=3):
        exceptions = [e for e in (q, r) if e != 1]
        central_deletion = not exceptions and t > 0
        satellite_deletion = exceptions == [4] or (exceptions == [3] and t in double)
        if not central_deletion and not satellite_deletion:
            retained.add((t, q, r))
    new = {(k, q, r) for k in markers for q, r in
           ((1, 1), (2, 1), (1, 2), (4, 1), (1, 4))}
    family = retained | new
    for point in new:
        for other in family - {point}:
            beyond_point = tuple(2*b-a for a, b in zip(other, point))
            beyond_other = tuple(2*b-a for a, b in zip(point, other))
            assert beyond_point not in family and beyond_other not in family
    print("Mixed progressions excluded in the three-coordinate box through exponent 41.")


def verify():
    y = 1427
    primes = primes_through(y)
    odd_primes = primes[1:]
    q_product = prod(odd_primes)
    assert len(odd_primes) == 224
    assert 10**590 < q_product < 3 * 10**590
    weight_at_two = Fraction(3, 2) * Fraction(9, 8) * Fraction(513, 512) + Fraction(1, 2**26)
    markers = [2, 5, 11, 14]
    assert all((2*v - u) not in markers for u in markers for v in markers if u != v)
    check_local_model(markers)
    odd_new = {1, 2, 4}
    assert all((2*v - u) not in odd_new for u in odd_new for v in odd_new if u != v)
    marker_mass = sum(Fraction(1, 2**k) for k in markers)
    cost_at_three = sum(Fraction(1, 2**(2*k)) for k in markers)
    # A lower bound for Q times the change in the smooth reciprocal sum.
    surplus = marker_mass - (weight_at_two - 1)
    for q in odd_primes:
        surplus += marker_mass/q - cost_at_three/(q*q) - (weight_at_two - marker_mass)/(q**3)
    assert surplus > Fraction(9, 10**5)
    # Outside primes contribute >= product_{n>y} (1 - n^{-2}) = y/(y+1).
    rough = Fraction(y * prod(p-1 for p in primes), (y+1) * prod(primes))
    assert rough > Fraction(1, 15)
    assert Fraction(9, 10**5) / (15 * 3 * 10**590) > Fraction(1, 10**596)
    print("odd primes:", len(odd_primes))
    print("10^590 < Q < 3*10^590")
    print("Q times reciprocal mass gain > 9/100000")
    print("rough-part density > 1/15")
    print("natural-density improvement > 10^(-596)")


if __name__ == "__main__":
    verify()
