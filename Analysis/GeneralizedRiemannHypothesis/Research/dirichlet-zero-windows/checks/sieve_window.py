#!/usr/bin/env python3
"""Finite prime-side illustration of degree-one zero spectrum separation.

All logs are natural. For a prime p in [X,2X], compare the local error
sum in the report with the main term at p, using the order-four character
modulo 5 with chi(2)=i and the quadratic character modulo 3. Include every
prime power n in [X/2,4X] other than p. The normalized fourfold convolution
of uniform probability densities on [-1/4,1/4] has Fourier transform
sinc(v/4)^4. The additional analytic smoothing factor has modulus at most
one, so it can be omitted from this upper bound. We sum absolute values
before any cancellation. This illustrates the finite local cross-terms.
The analytic and out-of-range terms in the proof are outside this check.
"""

from dataclasses import dataclass
from math import ceil, isclose, isqrt, log, sin, sqrt
from statistics import median


def character_difference(n):
    quartic_mod_five = (0, 1, 1j, -1j, -1)
    quadratic_mod_three = (0, 1, -1)
    return quartic_mod_five[n % 5] - quadratic_mod_three[n % 3]


def primes_up_to(limit):
    marks = bytearray([1]) * (limit + 1)
    marks[:2] = bytes(2)
    for p in range(2, isqrt(limit) + 1):
        if marks[p]:
            marks[p*p::p] = bytes(1 + (limit - p*p) // p)
    return [p for p in range(2, limit + 1) if marks[p]]


def sinc_four(t):
    if t == 0:
        return 1.0
    return (sin(t) / t) ** 4


@dataclass(frozen=True)
class Atom:
    n: int
    prime: bool
    log_n: float
    weight: float


def atoms_in_range(x):
    atoms = []
    for base in primes_up_to(4 * x):
        n = base
        while n <= 4 * x:
            if 2*n >= x:
                weight = log(base) * abs(character_difference(n)) / sqrt(n)
                atoms.append(Atom(n, n == base, log(n), weight))
            n *= base
    return sorted(atoms, key=lambda atom: atom.n)


def row(center, atoms, bandwidth):
    prime_sum = 0.0
    higher_power_sum = 0.0
    for atom in atoms:
        if atom.n == center.n:
            continue
        kernel = sinc_four(bandwidth * (atom.log_n - center.log_n) / 4)
        contribution = atom.weight * kernel / center.weight
        if atom.prime:
            prime_sum += contribution
        else:
            higher_power_sum += contribution
    return prime_sum, higher_power_sum


def prime_power_base(n):
    """Trial division used only by the independent check for the first row."""
    for d in range(2, isqrt(n) + 1):
        if n % d:
            continue
        cofactor = n
        while cofactor % d == 0:
            cofactor //= d
        return d if cofactor == 1 else 0
    return n


def verify_row(x, p, bandwidth, result):
    expected = [0.0, 0.0]
    diagonal = log(p) * abs(character_difference(p)) / sqrt(p)
    for n in range(ceil(x/2), 4*x + 1):
        if n == p:
            continue
        base = prime_power_base(n)
        if base:
            weight = log(base) * abs(character_difference(n)) / sqrt(n)
            expected[int(base != n)] += (
                weight * sinc_four(bandwidth * log(n / p) / 4) / diagonal
            )
    for direct, calculated in zip(expected, result):
        if not isclose(direct, calculated, rel_tol=1e-11, abs_tol=1e-14):
            raise ValueError(f"Independent enumeration disagrees at p={p}")


def run():
    print("chi_5(2)=i, chi_3(2)=-1. All logarithms natural.")
    print("Rows include p in [X,2X] with |chi_5(p)-chi_3(p)| >= 1.")
    print("Neighbors are prime powers in [X/2,4X] other than p.")
    print("R is the absolute sum over neighbors divided by the diagonal; "
          "R_pp uses only proper powers.")
    print()
    print(f"{'X':>5} {'b':>3} {'B=bX/logX':>11} {'rows':>6} "
          f"{'R<=1/4':>8} {'median R':>11} {'max R':>10} {'mean R_pp':>11}")
    for x in (250, 1000, 4000):
        atoms = atoms_in_range(x)
        centers = [a for a in atoms if a.prime and x <= a.n <= 2*x
                   and abs(character_difference(a.n)) >= 1]
        for factor in (2, 8, 32):
            bandwidth = factor * x / log(x)
            sums = [row(p, atoms, bandwidth) for p in centers]
            ratios = [primes + powers for primes, powers in sums]
            small_count = sum(r <= 0.25 for r in ratios)
            mean_power = sum(powers for _, powers in sums) / len(sums)
            print(f"{x:5d} {factor:3d} {bandwidth:11.3f} {len(sums):6d} "
                  f"{small_count:8d} {median(ratios):11.6g} "
                  f"{max(ratios):10.6g} {mean_power:11.6g}")
            if x == 250 and factor == 2:
                witness = centers[0]
                check = sums[0]
                verify_row(x, witness.n, bandwidth, check)
    print()
    print(f"Independent integer-by-integer check passed for X=250, b=2, "
          f"p={witness.n}: prime part {check[0]:.12g}, proper-power part "
          f"{check[1]:.12g}.")


if __name__ == "__main__":
    run()
