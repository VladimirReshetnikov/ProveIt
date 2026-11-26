#!/usr/bin/env python3
"""Arithmetic-only checks for the signed-spectrum reconstruction example.

Run with Python 3.8+ and no external dependencies. No L-function zeros or
spectral observations are used. All assertions use integers or fractions.
Floating-point formatting occurs only after the bounds have been checked.
"""

from fractions import Fraction
from math import comb, factorial, gcd, isqrt


def prime_factors(n):
    factors = {}
    candidate = 2
    while candidate * candidate <= n:
        while n % candidate == 0:
            factors[candidate] = factors.get(candidate, 0) + 1
            n //= candidate
        candidate = 3 if candidate == 2 else candidate + 2
    if n > 1:
        factors[n] = 1
    return factors


def divisors(n):
    values = [1]
    for p, exponent in prime_factors(n).items():
        values = [v * p**k for v in values for k in range(exponent + 1)]
    return sorted(values)


def totient(n):
    value = n
    for p in prime_factors(n):
        value = (value // p) * (p - 1)
    return value


def log_interval(n, terms=30):
    """Enclose log n by reducing to [1,2] and using the atanh series."""
    def near_one(x):
        z = (x - 1) / (x + 1)
        assert 0 <= z <= Fraction(1, 3)
        lower = 2 * sum(z**(2*j+1) / (2*j+1) for j in range(terms))
        tail = 2 * z**(2*terms+1) / ((2*terms+1) * (1-z*z))
        return lower, lower + tail

    power = n.bit_length() - 1
    lo2, hi2 = near_one(Fraction(2))
    lo, hi = near_one(Fraction(n, 2**power))
    return power * lo2 + lo, power * hi2 + hi


def derivative_l1_bound(radius, order):
    """Coefficientwise integral bound for (d/dt)^order (1-(t/radius)^2)_+^8."""
    total = Fraction(0)
    for j in range(9):
        power = 2*j
        if power >= order:
            term = Fraction(comb(8, j) * factorial(power),
                            factorial(power - order) * (power - order + 1))
            total += term
    return 2 * radius**(1-order) * total


def kernel_fourth_bound(radius):
    # g = (f'' - f/4)/(f''(0)-1/4), with f''(0)=-16/radius^2.
    return ((derivative_l1_bound(radius, 6) + derivative_l1_bound(radius, 4)/4)
            / (16/radius**2 + Fraction(1, 4)))


def tail_bound(radius, height, weight):
    return weight * kernel_fourth_bound(radius) * Fraction(1 + height**2, height**4)


def spline_tail_bound(radius, height, weight):
    # w is the k-fold convolution of the uniform density on [-b/k,b/k],
    # divided by its value at zero. This value before normalization is at
    # least 1/(2b). The two translated terms that annihilate the pole give
    # a Fourier multiplier of modulus at most 2.
    k = int(radius * height / 2)
    assert k >= 4
    # On the tail, |sinc(b*gamma/k)|^k <= 2^(-k)*(T/|gamma|)^k.
    return k, 4 * radius * (1 + height**2) * weight / (2**k)


def main():
    d, p = 109909799, 34945681
    double = 2*(d+1)
    assert prime_factors(d) == {d: 1} and prime_factors(p) == {p: 1}
    candidates = [q for q in divisors(double) if q % 18480 == 0 and d % q == q//2-1]
    assert len(candidates) == 16
    phi_groups = {}
    print("Admissible q and phi(q)")
    for q in candidates:
        h = totient(q)
        phi_groups.setdefault(h, []).append(q)
        print(q, h)
    ties = {h: qs for h, qs in phi_groups.items() if len(qs) > 1}
    assert ties == {230400: [1127280, 1201200], 691200: [3381840, 3603600]}
    print("All totient ties:", ties)
    q1, q2 = ties[230400]
    assert gcd(p-1, double) == q1 and gcd(p, d*double) == 1
    assert pow(p, (d-1)//2, d) == d-1
    assert p % q1 == 1 and p % q2 != 1
    print("Prime witness:", p, "residues", p % q1, p % q2, "Legendre symbol -1")

    d_lower, d_upper = log_interval(d)
    assert d_upper - d_lower < Fraction(1, 10**25)
    weight = Fraction(9, 4) * d_upper + 7
    origin_height = 500_000_000
    prime_height = 300_000_000_000_000_000
    origin_error = tail_bound(Fraction(1, 2), origin_height, weight)
    prime_error = tail_bound(Fraction(1, 3*(p+1)), prime_height, weight)
    assert origin_error < Fraction(1, 4*d)
    assert prime_error < Fraction(1, 1000)
    p_lower, _ = log_interval(p)
    jump_lower = 2*p_lower/(isqrt(p)+1)
    assert jump_lower > Fraction(5, 1000) > 2*prime_error
    print("Weight upper bound:", float(weight))
    print("Origin tail at T =", origin_height, "is <=", float(origin_error))
    print("Prime tail at T =", prime_height, "is <=", float(prime_error))
    print("Positive jump at the probe prime exceeds", float(jump_lower))
    # For the origin, 3b = 1/2 < log 2. Around log p, log(1+1/p)
    # is greater than 1/(p+1), which exceeds 3b with the chosen b.
    assert log_interval(2)[0] > Fraction(1, 2) and weight < 49
    k0, origin_spline = spline_tail_bound(Fraction(1, 6), 768, 49)
    kp, prime_spline = spline_tail_bound(Fraction(1, 10*(p+1)), 60_000_000_000, 49)
    assert k0 == 64 and kp == 85
    assert origin_spline < Fraction(1045, 10**15) < Fraction(1, 4*d)
    assert prime_spline < Fraction(522, 10**13) < jump_lower / 2
    print("Spline tail, origin: T=768, k=64, bound", float(origin_spline))
    print("Spline tail, prime: T=60000000000, k=85, bound", float(prime_spline))
    print("Arithmetic checks passed. No finite zero packet has been computed.")


if __name__ == "__main__":
    main()
