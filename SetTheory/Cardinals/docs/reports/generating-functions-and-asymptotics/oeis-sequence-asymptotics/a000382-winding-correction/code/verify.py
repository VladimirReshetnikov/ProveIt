#!/usr/bin/env python3
"""Exact checks for the restricted-permutation correction report.

The script uses only the Python standard library.  Its independent permanent
calculation is a row-by-row subset dynamic program; no recurrence from the
article is used in that calculation.
"""

from __future__ import annotations

from collections import defaultdict
from decimal import Decimal, getcontext
from typing import Dict


def permanent_winding_sectors(n: int, r: int = 4) -> Dict[int, int]:
    """Return winding-sector counts for displacements 0,...,r-1 on Z/nZ.

    A state is (used-column mask, total integer displacement).  At the end the
    total displacement is a multiple of n, and its quotient is the winding
    sector.  Complexity is O(r*n*2^n) up to a modest polynomial factor.
    """
    if not (1 <= r <= n):
        raise ValueError("the verifier assumes 1 <= r <= n")

    states: dict[tuple[int, int], int] = {(0, 0): 1}
    for i in range(n):
        nxt: defaultdict[tuple[int, int], int] = defaultdict(int)
        for (mask, displacement_sum), count in states.items():
            for d in range(r):
                j = (i + d) % n
                bit = 1 << j
                if mask & bit:
                    continue
                nxt[(mask | bit, displacement_sum + d)] += count
        states = dict(nxt)

    full = (1 << n) - 1
    sectors: defaultdict[int, int] = defaultdict(int)
    for (mask, displacement_sum), count in states.items():
        if mask != full:
            continue
        assert displacement_sum % n == 0
        sectors[displacement_sum // n] += count
    return dict(sorted(sectors.items()))


def composition_counts(limit: int, max_part: int = 3) -> list[int]:
    """F[m] = number of linear tilings/compositions of m with allowed parts."""
    f = [0] * (limit + 1)
    f[0] = 1
    for m in range(1, limit + 1):
        f[m] = sum(f[m - j] for j in range(1, max_part + 1) if m >= j)
    return f


def cyclic_tilings_123(n: int, f: list[int]) -> int:
    return f[n - 1] + 2 * f[n - 2] + 3 * f[n - 3]


def true_phi(n: int, f: list[int]) -> int:
    return 2 * (cyclic_tilings_123(n, f) + 1)


def mendelsohn_formula_quarter(n: int, f: list[int]) -> int:
    """Quarter of the right side of Mendelsohn's displayed equation (4)."""
    if n == 4:
        return 6
    if n < 5:
        raise ValueError("this tail is used only for n >= 4")
    return f[n - 1] + f[n - 3] + f[n - 4] + 1


def inverse_denominator_coefficients(limit: int) -> list[int]:
    """Coefficients of 1/(1-2z+z^4)."""
    u = [0] * (limit + 1)
    for m in range(limit + 1):
        u[m] = (1 if m == 0 else 0)
        if m >= 1:
            u[m] += 2 * u[m - 1]
        if m >= 4:
            u[m] -= u[m - 4]
    return u


def tribonacci_lucas(limit: int) -> list[int]:
    c = [3, 1, 3]
    while len(c) <= limit:
        c.append(c[-1] + c[-2] + c[-3])
    return c[: limit + 1]


def decimal_tribonacci_constant() -> Decimal:
    getcontext().prec = 80
    x = Decimal("1.84")
    for _ in range(30):
        p = x**3 - x**2 - x - 1
        dp = 3 * x**2 - 2 * x - 1
        x -= p / dp
    return +x


def main() -> None:
    max_n = 16
    f = composition_counts(max_n + 5)
    lucas = tribonacci_lucas(max_n)

    print("Independent subset-DP permanent checks")
    print(" n | sectors q=0,1,2,3       | total | 2(C_n+1)")
    print("---+---------------------------+-------+----------")
    true_values: dict[int, int] = {}
    for n in range(4, max_n + 1):
        sectors = permanent_winding_sectors(n, 4)
        c = cyclic_tilings_123(n, f)
        predicted = 2 * (c + 1)
        assert sectors == {0: 1, 1: c, 2: c, 3: 1}
        assert sum(sectors.values()) == predicted
        assert c == lucas[n]
        true_values[n] = predicted
        print(f"{n:2d} | {str(sectors):25s} | {predicted:5d} | {predicted:8d}")

    # The affine and homogeneous recurrences for the true count.
    for n in range(7, max_n + 1):
        assert true_values[n] == (
            true_values[n - 1] + true_values[n - 2] + true_values[n - 3] - 4
        )
    for n in range(8, max_n + 1):
        assert true_values[n] == 2 * true_values[n - 1] - true_values[n - 4]

    # A000382/Mendelsohn-formula tail and its now-provable recurrence.
    ghost = {n: mendelsohn_formula_quarter(n, f) for n in range(4, max_n + 1)}
    for n in range(8, max_n + 1):
        assert ghost[n] == ghost[n - 1] + ghost[n - 2] + ghost[n - 3] - 2
    for n in range(9, max_n + 1):
        assert ghost[n] == 2 * ghost[n - 1] - ghost[n - 4]

    # Exact correction kernel: true quarter minus A000382.
    kernel = inverse_denominator_coefficients(max_n)
    print("\nCorrection to A000382 (true quarter minus listed value)")
    print(" n | true/4 | A000382-tail | correction")
    print("---+--------+---------------+-----------")
    for n in range(4, max_n + 1):
        quarter = true_values[n] // 4
        delta = quarter - ghost[n]
        expected = 0 if n < 8 else kernel[n - 8]
        cumulative = 0 if n < 8 else sum(f[: n - 7])
        assert delta == expected == cumulative
        print(f"{n:2d} | {quarter:6d} | {ghost[n]:13d} | {delta:9d}")

    # Numerator checks for the two shifted ordinary generating functions.
    # For a sequence a_m, multiplying by 1-2z+z^4 gives the listed numerator.
    true_tail = [true_values[n] // 4 for n in range(4, max_n + 1)]
    ghost_tail = [ghost[n] for n in range(4, max_n + 1)]

    def numerator_prefix(a: list[int]) -> list[int]:
        out = []
        for m, value in enumerate(a):
            coeff = value
            if m >= 1:
                coeff -= 2 * a[m - 1]
            if m >= 4:
                coeff += a[m - 4]
            out.append(coeff)
        return out

    assert numerator_prefix(true_tail)[:8] == [6, -1, -2, -4, 0, 0, 0, 0]
    assert numerator_prefix(ghost_tail)[:9] == [6, -1, -2, -4, -1, 0, 0, 0, 0]

    # High-precision root and nearest-integer identity.
    alpha = decimal_tribonacci_constant()
    print("\nTribonacci constant alpha =")
    print(alpha)
    getcontext().prec = 70
    c = tribonacci_lucas(100)
    for n in range(4, 101):
        nearest = int((alpha**n + Decimal("0.5")).to_integral_value(rounding="ROUND_FLOOR"))
        assert nearest == c[n]
        quarter_nearest = int(
            (((alpha**n + 1) / 2) + Decimal("0.5")).to_integral_value(
                rounding="ROUND_FLOOR"
            )
        )
        assert quarter_nearest == (c[n] + 1) // 2

    print("\nAll exact identities, recurrences, generating-function prefixes,")
    print("sector counts, and nearest-integer checks passed.")


if __name__ == "__main__":
    main()
