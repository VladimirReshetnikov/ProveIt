#!/usr/bin/env python3
"""Verify the maximal sparse-place cutoff in the q0=18480, s=44 example.

Python 3 standard library. Run normally or with -O; explicit checks are retained.
"""

from collections import Counter
from itertools import product
from math import gcd, isqrt, prod


def check(condition, message):
    if not condition:
        raise ArithmeticError(message)


def trial_prime(number):
    return number >= 2 and all(number % d for d in range(2, isqrt(number) + 1))


def prime_certificate(number):
    """Use the complete factorization of number - 1 and the Lucas criterion."""
    factors = {2: 1, 3: 6, 11: 1, 74413: 1, 15264089: 1}
    check(all(trial_prime(p) for p in factors), "factor of p-1 is composite")
    check(prod(p**e for p, e in factors.items()) == number - 1, "wrong factorization")
    check(pow(3, number - 1, number) == 1, "Lucas power test failed")
    for p in factors:
        check(gcd(pow(3, (number - 1) // p, number) - 1, number) == 1,
              "Lucas order test failed")


def main():
    q0, s, h = 18480, 44, 2187
    modulus = q0 * 3 * h * 2**s
    two_part = modulus & -modulus
    check(h == 3**7 and 3**3 <= s < 3**4, "wrong h")
    check(two_part == 2**48, "wrong 2-primary component")
    obstruction = 18216708648992767
    height_bound = (h - 1) // 2
    stride = two_part // (1 << (height_bound.bit_length() - 1))
    check(stride == 2**38, "progression stride")
    check(pow(4, h, 3*h) == 1 and pow(4, h//3, 3*h) != 1,
          "2-primary multiplier exclusion")

    # Enumerate integers whose projective order on the 2-component can fit.
    # A prime excluded for sharing a factor with the modulus would be 3, 5, 7
    # or 11. These small odd primes already fail the stride condition.
    nonprime_witnesses = {
        1020346790576129: 157,
        2185829116018687: 101999,
        3870280929771521: 1663,
        6412351813189631: 17,
        9399724905857023: 23,
        17099604835172353: 13,
    }
    low_order = []
    candidates = coprime = 0
    for k in range(1, (obstruction + 1) // stride + 1):
        for value in (k * stride - 1, k * stride + 1):
            if value > obstruction:
                continue
            candidates += 1
            if gcd(value, modulus) != 1:
                continue
            coprime += 1
            delta = value - 1 if value % 4 == 1 else value + 1
            dyadic_order = max(1, two_part // (delta & -delta))
            for d in range(dyadic_order, height_bound + 1, dyadic_order):
                if pow(value, d, modulus) in (1, modulus - 1):
                    low_order.append((value, d))
                    break

    check([value for value, _ in low_order] ==
          [*sorted(nonprime_witnesses), obstruction], "list of short orders")
    for value, factor in nonprime_witnesses.items():
        check(1 < factor < value and value % factor == 0, "composite witness")
    prime_certificate(obstruction)
    check(low_order[-1][1] == 864, "first prime has wrong order")

    # Construct the places and check the advertised radius, cardinality and
    # distinctness directly. The general proof checks all prime-power triples.
    H, dimensions = 12, 3
    base = (h - 1) * (H - 1) + 1
    check(base**dimensions <= 2**s, "digit carry may escape the modulus")
    radii = Counter()
    exponents = []
    for digits in product(range(H), repeat=dimensions):
        radius = sum((2 * a - H + 1)**2 for a in digits)
        radii[radius] += 1
        if radius == 131:
            exponents.append(sum(a * base**j for j, a in enumerate(digits)))
    g = 1 + 3*h*q0
    places = {-pow(g, e, modulus) % modulus for e in exponents}
    check(len(places) == radii[131] == max(radii.values()) == 120, "shell count")
    check(all(x % q0 == q0 - 1 for x in places), "bad place class")

    print(f"q1 = {modulus}; h = {h}; digit base = {base}")
    print(f"centered shell radius = 131; distinct places = {len(places)}")
    print(f"stride candidates = {candidates}; coprime = {coprime}")
    print("candidates of sufficiently small projective order:")
    for value, order in low_order:
        status = (f"divisible by {nonprime_witnesses[value]}"
                  if value in nonprime_witnesses else "certified prime")
        print(f"  {value}: order {order}, {status}")
    print(f"largest admissible integer cutoff = {obstruction - 1}")


if __name__ == "__main__":
    main()
