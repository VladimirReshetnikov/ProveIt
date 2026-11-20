#!/usr/bin/env python3
"""Exact checker for individual dyadic Chebyshev packets, using Python's stdlib.

Run without arguments for cross-checks and examples. Supply d H u v n to
check one polynomial packet. The result is an exact integer comparison.
"""
from argparse import ArgumentParser
from dataclasses import dataclass
from itertools import product
from math import isqrt


def polynomial(d, height, positive, negative):
    """Decode a monic polynomial, smallest-degree coefficient first."""
    if d < 1 or min(height, positive, negative) < 0:
        raise ValueError("degree must be positive; other parameters must be natural")
    base = height + 2
    coefficients = []
    for _ in range(d):
        positive, a = divmod(positive, base)
        negative, b = divmod(negative, base)
        coefficients.append(a - b)
    return tuple(coefficients + [1])


def normalize(coefficients, p):
    out = [c % p for c in coefficients]
    while out and out[-1] == 0:
        out.pop()
    return tuple(out)


def remainder(a, b, p):
    """Euclidean polynomial remainder over F_p."""
    if not b:
        raise ZeroDivisionError("polynomial divisor is zero")
    a = list(normalize(a, p))
    inverse = pow(b[-1], -1, p)
    while len(a) >= len(b):
        shift = len(a) - len(b)
        factor = a[-1] * inverse % p
        for i, c in enumerate(b):
            a[i + shift] = (a[i + shift] - factor * c) % p
        while a and a[-1] == 0:
            a.pop()
    return tuple(a)


def gcd_degree(a, b, p):
    while b:
        a, b = b, remainder(a, b, p)
    return len(a) - 1


def multiply_mod(a, b, modulus, p):
    if not a or not b:
        return ()
    coefficients = [0] * (len(a) + len(b) - 1)
    for i, c in enumerate(a):
        for j, e in enumerate(b):
            coefficients[i + j] += c * e
    return remainder(coefficients, modulus, p)


def power_mod(a, exponent, modulus, p):
    value = (1,)
    while exponent:
        if exponent & 1:
            value = multiply_mod(value, a, modulus, p)
        exponent //= 2
        if exponent:
            a = multiply_mod(a, a, modulus, p)
    return value


def h_value(f, p, k):
    """deg gcd(F, X^(p^k)-X) via binary exponentiation in F_p[X]/(F)."""
    if k < 1:
        raise ValueError("prime-power exponent must be positive")
    modulus = normalize(f, p)
    power = list(power_mod((0, 1), p**k, modulus, p))
    power.extend([0] * max(0, 2 - len(power)))
    power[1] -= 1
    return gcd_degree(modulus, normalize(power, p), p)


def primes_through(x):
    sieve = bytearray([1]) * (x + 1)
    for p in range(2, isqrt(x) + 1):
        if sieve[p]:
            sieve[p*p : x+1 : p] = bytes((x - p*p) // p + 1)
    return (p for p in range(2, x + 1) if sieve[p])


def euler_product(f, x):
    """Integer A_F(x); bit_length()-1 gives its base-two log floor."""
    if x < 0:
        raise ValueError("x must be natural")
    value = 1
    for p in primes_through(x):
        prime_power, k = p, 1
        while prime_power <= x:
            value *= p ** h_value(f, p, k)
            prime_power *= p
            k += 1
    return value


@dataclass(frozen=True)
class Packet:
    b_n: int
    b_twice_n: int
    difference: int
    left: int
    right: int

    @property
    def accepted(self):
        return self.left <= self.right


def check_packet(d, height, positive, negative, n):
    if n < 100:
        raise ValueError("dyadic packet checks start at n=100")
    f = polynomial(d, height, positive, negative)
    b_n = euler_product(f, n).bit_length() - 1
    b_twice_n = euler_product(f, 2*n).bit_length() - 1
    difference = b_twice_n - 2*b_n
    scale = 1000 * (d+1)**4 * (height+2)**2 * (2*n).bit_length()**2
    return Packet(b_n, b_twice_n, difference, difference**2, n * scale**2)


def brute_h(f, p, k):
    """Independent small-instance oracle enumerating distinct irreducible factors."""
    modulus = normalize(f, p)
    degree = len(modulus) - 1
    total = 0
    for e in range(1, degree + 1):
        if k % e:
            continue
        for coefficients in product(range(p), repeat=e):
            g = coefficients + (1,)
            if remainder(modulus, g, p):
                continue
            if all(remainder(g, c + (1,), p)
                   for j in range(1, e//2 + 1)
                   for c in product(range(p), repeat=j)):
                total += e
    return total


def self_test():
    from math import lcm

    # Each possible divisor of X^(p^k)-X occurs exactly once, even if F repeats it.
    tests = 0
    polynomials = [(0, 1), (1, 0, 1), (-1, 0, 1), (1, -2, 1),
                   (-2, 0, 0, 1), (1, 1, 1, 1, 1)]
    for f in polynomials:
        for p in (2, 3, 5):
            for k in range(1, 7):
                assert h_value(f, p, k) == brute_h(f, p, k)
                tests += 1
    assert polynomial(2, 1, 1, 6) == (1, -2, 1)
    assert polynomial(3, 1, 0, 2) == (-2, 0, 0, 1)

    # F=X gives h=1, so A_X(x) is lcm(1,...,x). Repeated roots give the same h.
    running_lcm = 1
    for x in range(121):
        if x:
            running_lcm = lcm(running_lcm, x)
        assert euler_product((0, 1), x) == running_lcm
        assert euler_product((1, -2, 1), x) == running_lcm

    # For Q(i), p=2 ramifies, p=1 mod 4 splits, p=3 mod 4 has residue degree 2.
    for p in primes_through(120):
        for k in range(1, 5):
            expected = 1 if p == 2 else (2 if p % 4 == 1 or k % 2 == 0 else 0)
            assert h_value((1, 0, 1), p, k) == expected

    print(f"Passed {tests} comparisons with factor enumeration, "
          "LCM tests through 120, and Gaussian splitting tests.")
    for label, code in [
        ("X", (1, 0, 0, 0, 100)),
        ("X^2+1", (2, 0, 1, 0, 100)),
        ("X^3-2", (3, 1, 0, 2, 100)),
        ("Phi_5", (4, 0, 15, 0, 256)),
    ]:
        result = check_packet(*code)
        assert result.accepted
        print(f"{label:7} n={code[-1]:3}: {result}")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("parameters", type=int, nargs="*", metavar="N")
    args = parser.parse_args()
    if not args.parameters:
        self_test()
    elif len(args.parameters) == 5:
        packet = check_packet(*args.parameters)
        print(packet)
        print("accepted" if packet.accepted else "counterexample")
    else:
        parser.error("supply five numbers: d H u v n")
