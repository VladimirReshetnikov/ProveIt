#!/usr/bin/env python3
"""Verify rational Hamming-ball certificates and enumerate a prime-sign example.

Run with Python 3.10 or newer. Only the standard library is required.
The finite certificates were found by linear programming and are checked here
over the rationals. The prime enumeration uses Euler's criterion.
"""
from fractions import Fraction
from math import comb, isqrt


def moment(n, j, d):
    """Value of the j-th normalized Krawtchouk polynomial on layer d."""
    low = max(0, j - (n - d))
    high = min(d, j)
    value = sum((-1)**i * comb(d, i) * comb(n-d, j-i)
                for i in range(low, high + 1))
    return Fraction(value, comb(n, j))


def certify(n, radius, coefficients, layer_masses):
    """Verify the two inequalities of weak duality, then equality of costs.

    F(d) = 1 + sum_j b_j K_j(d)/binom(n,j). Its Walsh norm is 1+sum |b_j|.
    The dual y_d is the total mass uniformly spread over all words of layer d.
    """
    b = {j: Fraction(v) for j, v in coefficients.items()}
    y = {d: Fraction(v) for d, v in layer_masses.items() if v}
    assert all(1 <= j <= n for j in b)
    assert all(radius < d <= n and v >= 0 for d, v in y.items())
    assert all(1 + sum(v * moment(n, j, d) for j, v in b.items()) <= 0
               for d in range(radius + 1, n + 1))
    assert all(abs(sum(v * moment(n, j, d) for d, v in y.items())) <= 1
               for j in range(1, n + 1))
    optimum = 1 + sum(map(abs, b.values()))
    assert optimum == 1 + sum(y.values())
    return optimum


# Each tuple contains n, a, normalized nonconstant Fourier coefficients b_j,
# and the masses of the dual measure on the forbidden distance layers.
CASES = [
    (8, "1/2", {1: 4, 7: -4, 8: -1}, {4: 5, 5: 4}),
    (8, "3/2", {1: "32/5", 2: "84/5", 3: "112/5", 4: 14, 6: "-28/5",
                7: "-16/5", 8: "-3/5"},
     {2: "35/4", 3: "35/2", 4: "35/2", 5: 14, 6: "35/4", 7: "5/2"}),
    (12, "1/2", {1: 6, 11: -6, 12: -1}, {6: 7, 7: 6}),
    (12, "3/2", {1: "15/2", 2: "33/2", 3: "55/2", 9: "-55/2", 10: "-33/2",
                 11: "-15/2", 12: -1},
     {4: "315/16", 5: "63/2", 6: "105/8", 7: "45/4", 8: "315/16", 9: "35/4"}),
    (17, "1/2", {1: "3808/405", 2: "5576/405", 4: "-476/81",
                 14: "136/81", 16: "-697/405", 17: "-224/405"},
     {8: "255/16", 9: "255/16", 16: "17/16", 17: "1/16"}),
    (17, "3/2", {1: "544/53", 2: "1768/53", 3: "10880/159", 4: "3570/53",
                 6: "-4420/159", 12: "2210/159", 14: "-1020/53",
                 15: "-2176/159", 16: "-221/53", 17: "-32/53"},
     {6: "162435/3392", 7: "255255/3392", 8: "25415/3392", 9: "25415/3392",
      10: "60775/848", 11: "38675/848", 14: "9265/3392", 15: "1853/3392",
      16: "425/3392", 17: "25/3392"}),
]


def score_radius(n, a):
    """Largest d with n-2d > a sqrt(n) using exact integer comparisons."""
    return max(d for d in range(n + 1)
               if n - 2*d > 0 and (n-2*d)**2 > a*a*n)


def large_ball(n, offset):
    """Certify the ball defined on the sign cube by S > -offset."""
    first_forbidden = (n + offset) // 2
    denominator = offset + 1
    phase = (-1)**(first_forbidden + 1)
    coefficients = {1: Fraction(n, denominator)}
    # The full parity and the linear term coincide in dimension one.
    coefficients[n] = coefficients.get(n, 0) + Fraction(phase, denominator)
    masses = {first_forbidden: Fraction(first_forbidden+1, denominator),
              first_forbidden+1: Fraction(n-first_forbidden, denominator)}
    expected = 1 + Fraction(n+1, denominator)
    assert certify(n, first_forbidden-1, coefficients, masses) == expected


def primes_upto(limit):
    sieve = bytearray([1]) * (limit+1)
    sieve[:2] = bytes(2)
    for p in range(2, isqrt(limit)+1):
        if sieve[p]:
            for j in range(p*p, limit+1, p):
                sieve[j] = 0
    return [p for p in range(2, limit+1) if sieve[p]]


def prime_covering(limit):
    moduli = primes_upto(41)[1:]  # The twelve odd primes from 3 to 41.
    n = len(moduli)
    distances = [n+1] * (1 << n)
    old_radius = n+1
    drops = []
    for p in primes_upto(limit):
        if p in moduli:
            continue
        word = sum(1 << i for i, q in enumerate(moduli)
                   if pow(p, (q-1)//2, q) == q-1)
        for target, previous in enumerate(distances):
            distances[target] = min(previous, (target ^ word).bit_count())
        radius = max(distances)
        if radius < old_radius:
            drops.append((p, radius))
            old_radius = radius
    return moduli, drops


def main():
    print("Exact radial Fourier certificates")
    print("k  a    max distance  Fourier norm/mean  reciprocal nonconstant cost")
    for n, threshold, b, y in CASES:
        a = Fraction(threshold)
        radius = score_radius(n, a)
        norm = certify(n, radius, b, y)
        print(f"{n:2} {threshold:4} {radius:12}  {str(norm):17}  {1/(norm-1)}")
    count = 0
    for n in range(1, 65):
        for offset in range(n % 2, n + 1, 2):
            large_ball(n, offset)
            count += 1
    print(f"Exact formula 1+(n+1)/(a+1) checked on {count} balls S > -a,")
    print("for every allowed offset and every dimension from 1 through 64.")
    moduli, drops = prime_covering(700)
    expected = [(2, 12), (43, 9), (47, 8), (53, 7), (61, 6),
                (79, 5), (229, 4), (691, 3)]
    assert drops == expected
    print("Legendre moduli:", *moduli)
    print("Every drop in the covering radius for primes <=700 coprime to the moduli:")
    print("prime  radius")
    for p, r in drops:
        print(f"{p:5}  {r:6}")
    print("All checks passed.")


if __name__ == "__main__":
    main()
