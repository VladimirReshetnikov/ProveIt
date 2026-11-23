#!/usr/bin/env python3
"""Finite exact checks for the algebraic, p-adic, and partition chapter.

These are reproducible numerical regression checks, not proofs in Lean or
iPRA. The universal arguments and explicit bounds are in algebraic.tex.
"""
import itertools
import json
from collections import Counter
from math import isqrt


def ring_mul(u, v):
    a, b = u
    c, d = v
    return a * c - 5 * b * d, a * d + b * c


def ring_norm(u):
    a, b = u
    return a * a + 5 * b * b


def valuation(p, k, a):
    result = 0
    power = 1
    for j in range(1, k + 1):
        power *= p
        if a % power != 0:
            break
        result = j
    return result


def poly_eval(coefficients, a):
    result = 0
    for c in reversed(coefficients):
        result = result * a + c
    return result


def derivative(coefficients):
    return [j * coefficients[j] for j in range(1, len(coefficients))]


def hensel_digit(coefficients, p, k, a):
    modulus = p ** k
    value = poly_eval(coefficients, a)
    slope = poly_eval(derivative(coefficients), a)
    assert k >= 1 and 0 <= a < modulus
    assert value % modulus == 0 and slope % p != 0
    inverse = next(u for u in range(p) if u * slope % p == 1)
    t = (-(value // modulus) * inverse) % p
    candidates = [digit for digit in range(p)
                  if poly_eval(coefficients, a + digit * modulus)
                  % (p * modulus) == 0]
    assert candidates == [t]
    b = a + t * modulus
    assert 0 <= b < p * modulus
    return t, b


def partitions(n, largest=None):
    """Enumerate explicit nonincreasing tuples, including the empty partition."""
    if n == 0:
        return [()]
    if largest is None:
        largest = n
    out = []
    for first in range(min(n, largest), 0, -1):
        out.extend((first,) + rest for rest in partitions(n - first, first))
    return out


def conjugate(partition):
    if not partition:
        return ()
    return tuple(sum(part >= j for part in partition)
                 for j in range(1, partition[0] + 1))


def odd_to_distinct(partition):
    assert all(part % 2 for part in partition)
    out = []
    for part, count in Counter(partition).items():
        for j in range(count.bit_length()):
            if (count >> j) & 1:
                out.append(part * 2 ** j)
    return tuple(sorted(out, reverse=True))


def distinct_to_odd(partition):
    assert len(set(partition)) == len(partition)
    out = []
    for part in partition:
        odd_part, exponent = part, 0
        for _ in range(part.bit_length()):
            if odd_part % 2:
                break
            odd_part //= 2
            exponent += 1
        out.extend([odd_part] * 2 ** exponent)
    return tuple(sorted(out, reverse=True))


def main():
    counts = {}
    pairs = list(itertools.product(range(-4, 5), repeat=2))
    count = 0
    for u in pairs:
        a, b = u
        square = ring_mul(u, u)
        norm = ring_norm(u)
        assert (square[0] - 2 * a * a + norm,
                square[1] - 2 * a * b) == (0, 0)
        assert (norm == 0) == (u == (0, 0))
        for v in pairs:
            assert ring_norm(ring_mul(u, v)) == norm * ring_norm(v)
            count += 1
    counts["quadratic_norm_products"] = count
    counts["monic_polynomial_substitutions"] = len(pairs)

    small = [u for u in itertools.product(range(-3, 4), repeat=2)
             if ring_norm(u) <= 9]
    assert [u for u in small if ring_norm(u) == 1] == [(-1, 0), (1, 0)]
    assert not any(ring_norm(u) in (2, 3) for u in small)
    targets = [(2, 0), (3, 0), (1, 1), (1, -1)]
    count = 0
    actual_factorizations = 0
    for target in targets:
        N = ring_norm(target)
        for u in small:
            for v in small:
                if ring_norm(u) <= N and ring_norm(v) <= N:
                    count += 1
                    if ring_mul(u, v) == target:
                        assert ring_norm(u) == 1 or ring_norm(v) == 1
                        actual_factorizations += 1
    assert ring_mul((2, 0), (3, 0)) == (6, 0)
    assert ring_mul((1, 1), (1, -1)) == (6, 0)
    assert any(coord % 2 for coord in (1, 1))
    assert any(coord % 2 for coord in (1, -1))
    counts["bounded_irreducibility_factor_pairs"] = count
    counts["factorizations_confirmed_to_have_a_unit"] = actual_factorizations

    count = unequal = zero_cases = capped_cases = 0
    for p in (2, 3, 5, 7):
        for k in range(7):
            for a in range(-24, 25):
                r = valuation(p, k, a)
                for b in range(-24, 25):
                    s = valuation(p, k, b)
                    product = valuation(p, k, a * b)
                    added = valuation(p, k, a + b)
                    assert product == min(k, r + s)
                    assert added >= min(r, s)
                    if r != s:
                        assert added == min(r, s)
                        unequal += 1
                    if a == 0 or b == 0:
                        zero_cases += 1
                    if k > 0 and (r == k or s == k):
                        capped_cases += 1
                    count += 1
    counts["truncated_valuation_pairs"] = count

    polynomials = [
        [-2, 0, 1], [-2, 0, 0, 1], [-1, -1, 1],
        [1, 1, 0, 1], [1, 2], [1, 0, 1],
    ]
    lift_count = root_count = taylor_count = 0
    example = None
    for coefficients in polynomials:
        deriv = derivative(coefficients)
        for p in (2, 3, 5, 7, 11, 13):
            for a1 in range(p):
                if poly_eval(coefficients, a1) % p != 0:
                    continue
                if poly_eval(deriv, a1) % p == 0:
                    continue
                root_count += 1
                a = a1
                history = [(1, a)]
                for k in range(1, 6):
                    modulus = p ** k
                    for t in range(p):
                        difference = (
                            poly_eval(coefficients, a + t * modulus)
                            - poly_eval(coefficients, a)
                            - t * modulus * poly_eval(deriv, a))
                        assert difference % (p * modulus) == 0
                        taylor_count += 1
                    digit, b = hensel_digit(coefficients, p, k, a)
                    for old_k, old_a in history:
                        assert (b - old_a) % p ** old_k == 0
                    assert poly_eval(deriv, b) % p == poly_eval(deriv, a1) % p
                    history.append((k + 1, b))
                    a = b
                    lift_count += 1
                if coefficients == [-2, 0, 1] and p == 7 and a1 == 3:
                    example = [{"precision": k, "modulus": 7 ** k,
                                "residue": a} for k, a in history]
    assert [item["residue"] for item in example[:3]] == [3, 10, 108]
    counts["hensel_simple_initial_roots"] = root_count
    counts["hensel_unique_lift_steps"] = lift_count
    counts["finite_taylor_congruences"] = taylor_count

    table = [partitions(n) for n in range(13)]
    expected = [1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42, 56, 77]
    assert [len(row) for row in table] == expected
    partition_count = bijection_count = conjugacy_count = recursion_count = 0
    for n, row in enumerate(table):
        assert len(set(row)) == len(row)
        for partition in row:
            assert sum(partition) == n
            assert all(partition[i] >= partition[i + 1]
                       for i in range(len(partition) - 1))
            transposed = conjugate(partition)
            assert sum(transposed) == n and conjugate(transposed) == partition
            assert (transposed[0] if transposed else 0) == len(partition)
            partition_count += 1
        odd = {part for part in row if all(x % 2 for x in part)}
        distinct = {part for part in row if len(set(part)) == len(part)}
        assert {odd_to_distinct(part) for part in odd} == distinct
        assert {distinct_to_odd(part) for part in distinct} == odd
        for part in odd:
            assert distinct_to_odd(odd_to_distinct(part)) == part
            bijection_count += 1
        for part in distinct:
            assert odd_to_distinct(distinct_to_odd(part)) == part
            bijection_count += 1
        for k in range(n + 2):
            by_count = sum(len(part) == k for part in row)
            by_maximum = sum((part[0] if part else 0) == k for part in row)
            assert by_count == by_maximum
            conjugacy_count += 1
        for m in range(1, n + 2):
            left = sum(all(x <= m for x in part) for part in row)
            right = sum(all(x < m for x in part) for part in row)
            if n >= m:
                right += sum(all(x <= m for x in part) for part in table[n - m])
            assert left == right
            recursion_count += 1
    counts["explicit_partitions_and_conjugation"] = partition_count
    counts["odd_distinct_inverse_checks"] = bijection_count
    counts["fixed_part_count_conjugation_identities"] = conjugacy_count
    counts["partition_recurrence_cases"] = recursion_count

    count = 0
    for N in range(13):
        coefficients = [1] + [0] * N
        for j in range(1, N + 1):
            coefficients = [
                sum(coefficients[k - j * e] for e in range(k // j + 1))
                for k in range(N + 1)]
        for n in range(N + 1):
            assert coefficients[n] == len(table[n])
            count += 1
    counts["finite_generating_product_coefficients"] = count

    result = {
        "status": "all finite checks passed",
        "scope": "Exact finite regression checks, not Lean or iPRA derivations.",
        "counts": counts,
        "total_checks": sum(counts.values()),
        "valuation_coverage": {
            "primes": [2, 3, 5, 7], "precision_range": [0, 6],
            "integer_range": [-24, 24],
            "unequal_valuation_cases": unequal,
            "cases_with_a_zero_input": zero_cases,
            "cases_with_a_capped_valuation_at_positive_precision": capped_cases,
        },
        "partition_counts_n_0_through_12": expected,
        "hensel_x_squared_minus_two_from_3_mod_7": example,
        "nonufd_small_norm_search": {
            "norm_bound": 9, "no_elements_of_norm": [2, 3],
            "units_found": [[-1, 0], [1, 0]],
            "irreducibles_checked": [[2, 0], [3, 0], [1, 1], [1, -1]],
        },
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
