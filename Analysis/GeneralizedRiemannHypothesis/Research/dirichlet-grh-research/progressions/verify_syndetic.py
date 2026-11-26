#!/usr/bin/env python3
"""Exhaustively check one periodic set for all ratios and six exponent pairs."""
from collections import defaultdict
from itertools import combinations, product
from math import gcd, isqrt


def require(condition, message):
    if not condition:
        raise ValueError(message)


def largest_digit_sphere(side, dimension, base):
    spheres = defaultdict(list)
    for digits in product(range(side), repeat=dimension):
        norm_squared = sum(digit * digit for digit in digits)
        exponent = sum(digit * base**k for k, digit in enumerate(digits))
        spheres[norm_squared].append(exponent)
    radius = min(spheres, key=lambda r: (-len(spheres[r]), r))
    return radius, sorted(spheres[radius])


def maximum_gap(residues, modulus):
    ordered = sorted(residues)
    return max(b - a for a, b in zip(ordered, ordered[1:] + [ordered[0] + modulus]))


def main():
    prime, generator = 65_537, 3
    dimension, side, limit = 4, 4, 4
    base = limit * side
    require(all(prime % q for q in range(2, isqrt(prime) + 1)), "composite modulus")
    require(prime - 1 == 2**16 and pow(generator, (prime - 1)//2, prime) == prime - 1,
            "generator order certificate failed")
    require(base**dimension <= prime - 1, "digit box wraps")
    radius, exponents = largest_digit_sphere(side, dimension, base)
    raw = [pow(generator, exponent, prime) for exponent in exponents]
    require(len(raw) == len(set(raw)), "residue collision")
    best_gap, best_t = min(
        (maximum_gap([t*v % prime for v in raw], prime), t) for t in range(1, prime)
    )
    chosen = sorted(best_t*v % prime for v in raw)
    occupied = set(chosen)
    print(f"p={prime}, generator={generator}, L={limit}, n={dimension}, H={side}")
    print(f"squared_radius={radius}, occupied_classes={len(chosen)}")
    print(f"best_dilation={best_t}, maximum_circular_gap={best_gap}")
    print("residues=" + ",".join(map(str, chosen)))
    for i, j in combinations(range(1, limit + 1), 2):
        admissible = []
        for ratio in range(prime):
            first, second = pow(ratio, i, prime), pow(ratio, j, prime)
            found = any(a*first % prime in occupied and a*second % prime in occupied
                        for a in chosen)
            expected = pow(ratio, gcd(i, j), prime) == 1
            require(found == expected, f"ratio mismatch at i={i}, j={j}, r={ratio}")
            if found:
                admissible.append(ratio)
        print(f"shape=(0,{i},{j}): " + ",".join(map(str, admissible)))
    print(f"All {prime * (limit * (limit - 1) // 2)} shape/ratio tests passed.")


if __name__ == "__main__":
    main()
