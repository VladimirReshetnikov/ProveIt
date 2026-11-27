#!/usr/bin/env python3
"""Numerical example for the heat-smoothed race 3 minus 1 modulo 4.

Run: python verify.py  (requires Python 3.9+ and mpmath 1.3.0).
Only the zero search uses mpmath. All arithmetic sums use exact integer
primes/prime powers, binary64 Gaussian weights and math.fsum.
"""

import math
from array import array
from itertools import compress

import mpmath as mp


H = 0.04
TIMES = (6, 8, 10, 12, 14)
CUTOFF = math.ceil(math.exp(max(TIMES) + 3))
ZERO_HEIGHT = 32


def primes_through(n):
    """Return a compact integer array of primes <= n by Eratosthenes."""
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, math.isqrt(n) + 1):
        if sieve[p]:
            count = (n - p * p) // p + 1
            sieve[p * p :: p] = b"\x00" * count
    return array("I", compress(range(n + 1), sieve))


def coefficients(primes, n):
    """Yield log(n), signed Lambda(n)/sqrt(n), is_prime for odd prime powers."""
    for p in primes:
        if p == 2:
            continue
        k = p
        log_p = math.log(p)
        while k <= n:
            sign = 1 if k % 4 == 3 else -1
            yield math.log(k), sign * log_p / math.sqrt(k), k == p
            k *= p


def arithmetic_sums(primes, t):
    scale = 1 / math.sqrt(4 * math.pi * H)
    # Group terms into small batches to bound the storage and retain fsum's
    # cancellation accuracy. Both columns use the same kernel.
    prime_groups = []
    higher_groups = []
    batch = []
    higher = []
    for u, coefficient, is_prime in coefficients(primes, CUTOFF):
        term = scale * coefficient * math.exp(-(t - u) ** 2 / (4 * H))
        if is_prime:
            batch.append(term)
        else:
            higher.append(term)
        if len(batch) == 8192:
            prime_groups.append(math.fsum(batch))
            higher_groups.append(math.fsum(higher))
            batch.clear()
            higher.clear()
    prime_sum = math.fsum(prime_groups + [math.fsum(batch)])
    higher_sum = math.fsum(higher_groups + [math.fsum(higher)])
    return prime_sum + higher_sum, prime_sum


def arithmetic_tail_bound(t):
    """Integral majorant for the absolute contribution from all integers n>N."""
    mu = t + H
    z = (math.log(CUTOFF) - mu) / (2 * math.sqrt(H))
    return math.exp(t / 2 + H / 4) * (
        mu * math.erfc(z) / 2 + math.sqrt(H / math.pi) * math.exp(-z * z)
    )


def beta_hardy(gamma):
    # The completed odd primitive beta function has root number +1, so
    # rotating by the phase of its completion makes beta real on the line.
    s = mp.mpf("0.5") + mp.j * gamma
    phase = (s.imag * mp.log(4 / mp.pi) / 2 + mp.loggamma((s + 1) / 2).imag)
    return (mp.exp(mp.j * phase) * mp.dirichlet(s, [0, 1, 0, -1])).real


def find_ordinates():
    """Locate sign changes; this numerical scan does not certify completeness."""
    mp.mp.dps = 30
    roots = []
    left = mp.mpf(0)
    left_value = beta_hardy(left)
    for j in range(1, 8 * ZERO_HEIGHT + 1):
        right = mp.mpf(j) / 8
        right_value = beta_hardy(right)
        if left_value * right_value < 0:
            root = mp.findroot(beta_hardy, (left, right), solver="anderson")
            if not left < root < right or abs(beta_hardy(root)) > mp.mpf("1e-24"):
                raise ArithmeticError("unresolved root bracket")
            roots.append(float(root))
        left, left_value = right, right_value
    return roots


def main():
    primes = primes_through(CUTOFF)
    roots = find_ordinates()
    print("Dirichlet beta; direction = class 3 minus class 1 modulo 4")
    print(f"h = {H}, n <= {CUTOFF}, positive ordinates scanned up to {ZERO_HEIGHT}")
    print("Positive sign-changing roots found by numerical scan:")
    print(", ".join(f"{root:.10f}" for root in roots))
    print()
    print("  t     powers P(t)       zero sum Z(t)     P-Z          primes B(t)     B-Z-1/2")
    for t in TIMES:
        powers, primes_only = arithmetic_sums(primes, t)
        zeros = 2 * math.fsum(
            math.exp(-H * g * g) * math.cos(g * t) for g in roots
        )
        print(f"{t:3d}  {powers: .10f}    {zeros: .10f}    {powers-zeros: .2e}"
              f"   {primes_only: .10f}   {primes_only-zeros-0.5: .3e}")
    print()
    print("Maximum analytic absolute majorant for the arithmetic cutoff tail:",
          f"{max(arithmetic_tail_bound(t) for t in TIMES):.2e}")
    print("The prime powers use Lambda(n)/sqrt(n) times the normalized heat kernel.")
    print("The prime-only column uses exactly the terms n=p.")
    print("Z(t) = 2 sum_{gamma>0} exp(-h gamma^2) cos(gamma t), truncated as above.")
    print("The finite-t errors include the remainder from the explicit formula and,")
    print("for primes only, the error in replacing the contribution of higher powers")
    print("by its limit. Sign changes and floating-point values are illustrative.")
    assert max(arithmetic_tail_bound(t) for t in TIMES) < 1e-18


if __name__ == "__main__":
    main()
