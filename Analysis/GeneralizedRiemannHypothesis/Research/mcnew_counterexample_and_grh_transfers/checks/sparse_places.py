#!/usr/bin/env python3
"""Exact finite checks for sparse sets of places. Run with Python 3.8+."""

from collections import defaultdict
from itertools import product
from math import gcd


def ceil_ratio(a, b):
    return (a + b - 1) // b


def tower_window(s):
    value = 81
    while s >= 3:
        s //= 3
        value *= 3
    return value


def strip_prime(number, p):
    while number % p == 0:
        number //= p
    return number


def signed_order(base, modulus):
    assert modulus > 2 and gcd(base, modulus) == 1
    residue = 1
    for k in range(1, modulus + 1):
        residue = base * residue % modulus
        if residue == 1:
            return k, 1
        if residue == modulus - 1:
            return k, -1
    raise ArithmeticError("No signed order found")


def order_in_prime_power_kernel(unit, modulus, p, bound):
    # The reduction kernel has p-power order 'bound'.
    assert pow(unit, bound, modulus) == 1
    order = bound
    while order % p == 0 and pow(unit, order // p, modulus) == 1:
        order //= p
    return order


def cycle_capacity(length, width):
    return min(length, 2 * length // width)


def marked_positions(length, width):
    total = cycle_capacity(length, width)
    return {i for i in range(length)
            if (i + 1) * total // length > i * total // length}


def cycle_formula(q0, s, p):
    z = tower_window(s)
    growth = 3 * z if p == 2 else 2 ** s
    kernel_prime = 3 if p == 2 else 2
    base_modulus = strip_prime(q0, p)
    modulus = base_modulus * growth
    step, sign = signed_order(p, base_modulus)
    unit = sign * pow(p, step, modulus) % modulus
    order = order_in_prime_power_kernel(unit, modulus, kernel_prime, growth)
    width = ceil_ratio(z, step)
    capacity = growth // order * cycle_capacity(order, width)
    return modulus, base_modulus, unit, order, width, capacity


def cyclic_support(q0, s, p):
    modulus, base, unit, order, width, capacity = cycle_formula(q0, s, p)
    left = set(range(base - 1, modulus, base))
    selected = set()
    positions = marked_positions(order, width)
    while left:
        first = min(left)
        residue = first
        for i in range(order):
            left.remove(residue)
            if i in positions:
                selected.add(residue)
            residue = residue * unit % modulus
        assert residue == first
    assert len(selected) == capacity
    return modulus, selected


def check_signed_triples(selected, p, modulus, z):
    # Direct test of the source predicate on a projected support.
    # Positions may repeat as residues, and signs are independent.
    for first in selected:
        residue = first
        hits = 0
        for i in range(1, z):
            residue = residue * p % modulus
            if residue in selected or (-residue) % modulus in selected:
                hits += 1
                assert hits <= 1, (p, first, i)


def exhaustive_cycle_checks():
    tests = 0
    for length in range(1, 10):
        for width in range(1, 2 * length + 3):
            best = 0
            for mask in range(1 << length):
                size = bin(mask).count('1')
                if size <= best:
                    continue
                ok = all(sum((mask >> ((i + j) % length)) & 1
                             for j in range(width)) <= 2 for i in range(length))
                if ok:
                    best = size
            assert best == cycle_capacity(length, width)
            assert len(marked_positions(length, width)) == best
            tests += 1
    return tests


def largest_digit_sphere(z, side, dimension):
    groups = defaultdict(list)
    base = (z - 1) * side
    for digits in product(range(side), repeat=dimension):
        squared_length = sum(x*x for x in digits)
        groups[squared_length].append(sum(x * base**i for i, x in enumerate(digits)))
    return max(groups.values(), key=len)


def check_product():
    q0, s, L = 18480, 40, 19
    z = tower_window(s)
    dimension, side = 2, 40
    two_modulus = (q0 // strip_prime(q0, 2)) * 2**s
    assert ((z-1) * side)**dimension <= 2**s
    assert (L+1) * (z-1) < two_modulus
    exponents = largest_digit_sphere(z, side, dimension)
    projected = {-pow(17, e, two_modulus) % two_modulus for e in exponents}
    assert len(exponents) == len(projected)
    for p in (3, 5, 7, 11, 13, 17, 19):
        check_signed_triples(projected, p, two_modulus, z)
    odd_modulus, odd_part = cyclic_support(q0, s, 2)
    check_signed_triples(odd_part, 2, odd_modulus, z)
    return len(exponents), len(odd_part), len(exponents) * len(odd_part)


def main():
    print("Exhaustive cyclic-window optima checked:", exhaustive_cycle_checks())
    q0 = 18480
    print("q0 = 18480; columns s, z, width, projected cap at 2, projected cap at 3")
    for s in (1, 3, 9, 27, 40, 81, 243):
        z = tower_window(s)
        row2, row3 = [cycle_formula(q0, s, p) for p in (2, 3)]
        assert row2[3] == z and row3[3] == 2**s and row2[4] == row3[4]
        print(s, z, row2[4], row2[5], row3[5])
        if s <= 81:
            modulus, support = cyclic_support(q0, s, 2)
            check_signed_triples(support, 2, modulus, z)
        if s <= 9:
            modulus, support = cyclic_support(q0, s, 3)
            check_signed_triples(support, 3, modulus, z)
    e, a, prod = check_product()
    print(f"All-prime CRT example for s=40 and L=19: {e} x {a} = {prod} places.")
    print("All checks passed.")


if __name__ == "__main__":
    main()
