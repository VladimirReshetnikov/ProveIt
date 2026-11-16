#!/usr/bin/env python3
"""Exact finite diagnostics for the Bell-number report.

These checks are not a proof checker and do not certify iPRA derivations.
They independently exercise the stated identities and explicit bijections.
Only Python's standard library is used.
"""

from fractions import Fraction
from itertools import permutations, product
from math import comb, factorial, isqrt
import json


def bell_table(n):
    values = [1]
    for r in range(n):
        values.append(sum(comb(r, k) * values[k] for k in range(r + 1)))
    return values


def stirling_table(n):
    rows = [[1] + [0] * n]
    for r in range(n):
        previous = rows[-1]
        rows.append([0] + [k * previous[k] + previous[k - 1]
                          for k in range(1, n + 1)])
    return rows


def falling_polynomial(n):
    coefficients = [1]
    for j in range(n):
        new = [0] * (len(coefficients) + 1)
        for i, coefficient in enumerate(coefficients):
            new[i] -= j * coefficient
            new[i + 1] += coefficient
        coefficients = new
    return coefficients


def determinant(matrix):
    """Fraction-free Bareiss elimination, with explicit row pivoting."""
    a = [list(row) for row in matrix]
    n = len(a)
    sign = 1
    previous = 1
    for k in range(n - 1):
        if a[k][k] == 0:
            pivot = next((i for i in range(k + 1, n) if a[i][k]), None)
            if pivot is None:
                return 0
            a[k], a[pivot] = a[pivot], a[k]
            sign = -sign
        pivot_value = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                numerator = a[i][j] * pivot_value - a[i][k] * a[k][j]
                assert numerator % previous == 0
                a[i][j] = numerator // previous
        for i in range(k + 1, n):
            a[i][k] = 0
        previous = pivot_value
    return sign * a[-1][-1]


def restricted_growth_words(n):
    if n == 0:
        yield ()
        return
    def extend(prefix, largest):
        if len(prefix) == n:
            yield tuple(prefix)
            return
        for value in range(largest + 2):
            yield from extend(prefix + [value], max(largest, value))
    yield from extend([0], 0)


def blocks(word):
    if not word:
        return []
    return [[i for i, label in enumerate(word) if label == j]
            for j in range(max(word) + 1)]


def avoids_1_23(p):
    return all(not (p[i] < p[j] < p[j + 1])
               for j in range(1, len(p) - 1) for i in range(j))


def avoids_1_32(p):
    return all(not (p[i] < p[j + 1] < p[j])
               for j in range(1, len(p) - 1) for i in range(j))


def extends_every_321(p):
    n = len(p)
    return all(any(p[l] > p[i] for l in range(j + 1, k))
               for i in range(n) for j in range(i + 1, n)
               for k in range(j + 1, n) if p[i] > p[j] > p[k])


def partition_permutations(word):
    bs = blocks(word)
    minimum_order = sorted(bs, key=min, reverse=True)
    first = tuple(v for b in minimum_order
                  for v in [min(b)] + sorted(b[1:], reverse=True))
    second = tuple(v for b in minimum_order for v in sorted(b))
    third = tuple(v for b in sorted(bs, key=max)
                  for v in [max(b)] + sorted(b[:-1]))
    return first, second, third


def count_return_shuffles(n):
    original = tuple(range(n))
    count = 0
    for positions in product(range(n), repeat=n):
        deck = list(original)
        for position in positions:
            top = deck.pop(0)
            deck.insert(position, top)
        count += tuple(deck) == original
    return count


def first_state_period(modulus, values, cap):
    coefficients = falling_polynomial(modulus)
    coefficients[0] -= 1
    initial = tuple(b % modulus for b in values[:modulus])
    state = initial
    for period in range(1, cap + 1):
        appended = (state[0] - sum(coefficients[j] * state[j]
                                  for j in range(1, modulus))) % modulus
        state = state[1:] + (appended,)
        if state == initial:
            return period
    raise AssertionError(("No return before diagnostic cap", modulus, cap))


def multiply_mod_touchard(a, b, p):
    """Multiply degree-<p polynomials modulo p and X^p-X-1."""
    coefficients = [0] * (2 * p - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            coefficients[i + j] = (coefficients[i + j] + x * y) % p
    for degree in range(2 * p - 2, p - 1, -1):
        coefficients[degree - p] = (coefficients[degree - p] + coefficients[degree]) % p
        coefficients[degree - p + 1] = (coefficients[degree - p + 1] + coefficients[degree]) % p
    return coefficients[:p]


def power_of_x_mod_touchard(exponent, p):
    result = [1] + [0] * (p - 1)
    power = [0, 1] + [0] * (p - 2)
    while exponent:
        if exponent % 2:
            result = multiply_mod_touchard(result, power, p)
        power = multiply_mod_touchard(power, power, p)
        exponent //= 2
    return result


def main():
    B = bell_table(40)
    S = stirling_table(40)
    assert all(B[n] == sum(S[n]) for n in range(41))
    for n in range(12):
        for k in range(12):
            assert factorial(k) * S[n][k] == sum(
                (-1) ** (k - i) * comb(k, i) * i ** n for i in range(k + 1))
    for n in range(11):
        for m in range(11):
            assert B[n + m] == sum(comb(n, k) * S[m][j] * j ** (n - k) * B[k]
                                     for k in range(n + 1) for j in range(m + 1))
    a = [Fraction(B[n], factorial(n)) for n in range(len(B))]
    def A(n):
        return a[n] if n >= 0 else Fraction(0)
    def X(n):
        return Fraction(1) if n == 0 else Fraction(1, factorial(n - 1))
    for m in range(1, 20):
        for n in range(m, 20):
            lhs = m * (n + 1) * (A(m) * A(n) - A(m - 1) * A(n + 1))
            rhs = sum((X(j) * X(k - 1) - X(j - 1) * X(k)) *
                      (A(m - j) * A(n + 1 - k) - A(m - k) * A(n + 1 - j))
                      for j in range(1, n + 2) for k in range(j + 1, n + 2))
            assert lhs == rhs and lhs >= 0
    for n in range(1, 40):
        assert B[n] ** 2 < B[n - 1] * B[n + 1]
        assert n * B[n - 1] * B[n + 1] <= (n + 1) * B[n] ** 2
    for n in range(11):
        expected = 1
        for j in range(n + 1):
            expected *= factorial(j)
        assert determinant([[B[i + j] for j in range(n + 1)]
                            for i in range(n + 1)]) == expected

    for n in range(8):
        words = list(restricted_growth_words(n))
        assert len(words) == B[n]
        images = [set(), set(), set()]
        for word in words:
            triple = partition_permutations(word)
            for i, image in enumerate(triple):
                images[i].add(image)
        targets = [set(), set(), set()]
        for p in permutations(range(n)):
            for i, predicate in enumerate((avoids_1_23, avoids_1_32,
                                            extends_every_321)):
                if predicate(p):
                    targets[i].add(p)
        assert images == targets
        assert all(len(image) == B[n] for image in images)

    shuffle_counts = {n: count_return_shuffles(n) for n in range(1, 7)}
    assert all(value == B[n] for n, value in shuffle_counts.items())

    periods = {1: 1, 2: 3, 3: 13, 4: 12, 5: 781, 6: 39,
               7: 137257, 8: 24, 9: 39, 10: 2343, 12: 156}
    for modulus, expected in periods.items():
        assert first_state_period(modulus, B, expected) == expected
        q = falling_polynomial(modulus)
        q[0] -= 1
        for n in range(41 - modulus):
            assert sum(q[j] * B[n + j] for j in range(modulus + 1)) % modulus == 0

    # Certify the large prime-modulus period by excluding its maximal proper divisors.
    p = 11
    prime_factors = [15797, 1806113]
    N = sum(p ** j for j in range(p))
    assert prime_factors[0] * prime_factors[1] == N == 28531167061
    assert all(all(q % d for d in range(2, isqrt(q) + 1)) for q in prime_factors)
    assert power_of_x_mod_touchard(N, p) == [1] + [0] * (p - 1)
    period_11_certificate = {"period": N, "prime_factors": prime_factors,
                             "failed_candidate_periods": []}
    for q in prime_factors:
        exponent = N // q
        remainder = power_of_x_mod_touchard(exponent, p)
        residue = sum(remainder[j] * B[j] for j in range(p)) % p
        assert residue != B[0] % p
        period_11_certificate["failed_candidate_periods"].append({
            "candidate": exponent, "remainder_coefficients": remainder,
            "B_candidate_mod_11": residue, "B_0_mod_11": B[0] % p,
        })

    report = {
        "status": "all exact diagnostic checks passed",
        "not_a_formal_proof": True,
        "stirling_and_bell_tables": "n <= 40",
        "inclusion_exclusion": "n,k <= 11",
        "spivey": "m,n <= 10",
        "paired_logconcavity_identity": "1 <= m <= n < 20",
        "logarithmic_inequalities": "1 <= n < 40",
        "hankel_determinants": "matrix sizes 1 through 11",
        "three_permutation_bijections": "complete image equality, n <= 7",
        "return_shuffle_counts": shuffle_counts,
        "least_periods_checked_by_full_state_return": periods,
        "least_period_11_by_polynomial_certificate": period_11_certificate,
        "initial_bell_numbers": B[:16],
    }
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
