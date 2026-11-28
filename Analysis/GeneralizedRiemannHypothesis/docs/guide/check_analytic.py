"""Exact checks of the residue example and the integrated prime-count identity."""

from fractions import Fraction as F
from math import gcd, isqrt


def prime_powers(limit):
    """Yield each integer p**k <= limit with its prime base and exponent."""
    for p in range(2, limit + 1):
        if any(p % divisor == 0 for divisor in range(2, isqrt(p) + 1)):
            continue
        n = p
        exponent = 1
        while n <= limit:
            yield n, p, exponent
            n *= p
            exponent += 1


def legendre(n, prime):
    residue = pow(n % prime, (prime - 1) // 2, prime)
    return -1 if residue == prime - 1 else residue


def check_residue():
    sigma, tau = F(3, 4), F(2)
    real = sigma * (1 - sigma) + tau**2
    imaginary = tau * (1 - 2 * sigma)
    assert (real, imaginary) == (F(67, 16), -1)
    # Squared constants for one zero, before dividing by phi(Q)^2.
    modulus_squared = real**2 + imaginary**2
    assert 1 / modulus_squared == F(16**2, 4745)
    assert (1 - sigma) ** 2 / modulus_squared == F(4**2, 4745)


def check_count_identity():
    # Small analytic example. The geometric construction uses larger moduli.
    modulus, auxiliary_prime = 8, 7
    full_modulus = modulus * auxiliary_prime
    inert_classes = {
        n for n in range(full_modulus)
        if gcd(n, full_modulus) == 1
        and n % modulus == 1
        and legendre(n, auxiliary_prime) == -1
    }
    assert inert_classes == {17, 33, 41}
    start, stop = 48, 182
    terms = []
    for n, p, exponent in prime_powers(stop):
        weight = (n % modulus == 1) * (1 - legendre(n, auxiliary_prime))
        if p != auxiliary_prime and exponent % 2 == 0:
            assert weight == 0
        if exponent == 1:
            assert weight == 2 * (p % full_modulus in inert_classes)
        if weight:
            terms.append((n, p, weight))
    assert (49, 7, 1) in terms  # The ramified square has weight log(7).

    def smoothed(n, cutoff):
        return max(F(0), F(1, n) - F(1, cutoff))

    # Compare coefficients of log(p), keeping the calculation rational.
    # Centering contributes the same explicit log(stop/start)/phi(Q)
    # on the sum and on the integral, so it cancels from this check.
    for p in {base for _, base, _ in terms}:
        powers = [(n, weight) for n, base, weight in terms if base == p]
        difference = sum(
            weight * (smoothed(n, stop) - smoothed(n, start))
            for n, weight in powers
        )
        integral = sum(
            sum(weight for n, weight in powers if n <= k)
            * (F(1, k) - F(1, k + 1))
            for k in range(start, stop)
        )
        assert difference == integral


if __name__ == "__main__":
    check_residue()
    check_count_identity()
    print("Verified the proposed-zero constants, inert classes, and finite integral identity.")
