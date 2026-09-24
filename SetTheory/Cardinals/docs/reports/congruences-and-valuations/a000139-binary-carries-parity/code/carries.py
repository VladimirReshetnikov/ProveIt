#!/usr/bin/env python3
"""Exact arithmetic for A000139 and its binary-valuation distribution.

Only the Python standard library is required. Polynomial coefficient lists
are in increasing degree order. A histogram includes n=0, where a(0)=2.
All bounds are exclusive. No floating-point arithmetic is used here.
"""
from __future__ import annotations

import argparse
import json
from math import comb
from typing import Sequence


def _nat(n: int, name: str = "n") -> None:
    if not isinstance(n, int) or isinstance(n, bool) or n < 0:
        raise ValueError(f"{name} must be a nonnegative integer")


def a000139(n: int) -> int:
    """Return 2 (3n)! / ((n+1)! (2n+1)!), with an integrality check."""
    _nat(n)
    q, r = divmod(2 * comb(3 * n, n), (n + 1) * (2 * n + 1))
    if r:
        raise ArithmeticError("Unexpected nonintegral factorial quotient")
    return q


def v2(n: int) -> int:
    """The exponent of 2 in a positive integer."""
    _nat(n)
    if n == 0:
        raise ValueError("v2(0) is not finite")
    return (n & -n).bit_length() - 1


def valuation(n: int) -> int:
    """v2(a000139(n)), from the proved binary-digit-sum formula."""
    _nat(n)
    return n.bit_count() + (n + 1).bit_count() - (3 * n).bit_count()


def is_odd_term(n: int) -> bool:
    """True precisely for odd n having no adjacent binary ones."""
    _nat(n)
    return bool(n & 1) and (n & (n << 1)) == 0


def carry_count(n: int) -> int:
    """Direct column-by-column count of carries in n + 2n.

    This deliberately does not use the digit-sum identity. The final
    zero columns are processed too, so a carry above the top bit counts.
    """
    _nat(n)
    a, b, incoming, count = n, 2 * n, 0, 0
    while a or b or incoming:
        outgoing = ((a & 1) + (b & 1) + incoming) // 2
        count += outgoing
        a >>= 1
        b >>= 1
        incoming = outgoing
    return count


# State order S, U, W, A, B, C. Entries are (next_state, exponent_of_y).
# Input digits are read from least to most significant.
TRANSITIONS = (
    ((3, 1), (1, 0)),  # S: no digits read
    ((3, 0), (2, 0)),  # U: initial run is exactly one 1
    ((4, 1), (2, 0)),  # W: initial run has at least two 1s
    ((3, 0), (4, 0)),  # A: previous bit 0, carry 0
    ((3, 0), (5, 1)),  # B: (previous bit, carry) = (1,0) or (0,1)
    ((4, 1), (5, 1)),  # C: previous bit 1, carry 1
)
TERMINAL_EXPONENT = (1, 0, 1, 0, 0, 1)


def automaton_valuation(n: int) -> int:
    """Evaluate the six-state nonnegative weighted automaton."""
    _nat(n)
    state, exponent = 0, 0
    while n:
        state, weight = TRANSITIONS[state][n & 1]
        exponent += weight
        n >>= 1
    return exponent + TERMINAL_EXPONENT[state]


def _add_shift(dst: list[int], src: Sequence[int], shift: int, scale: int = 1) -> None:
    if len(dst) < len(src) + shift:
        dst.extend([0] * (len(src) + shift - len(dst)))
    for i, x in enumerate(src):
        dst[i + shift] += scale * x


def _trim(p: list[int]) -> list[int]:
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def dyadic_histograms(max_m: int) -> list[list[int]]:
    """Return V_0(y),...,V_max_m(y) by the proved order-three recurrence.

    This takes O(max_m**2) integer coefficient updates. The recurrence
    has signed terms, but each resulting coefficient is nonnegative.
    """
    _nat(max_m, "max_m")
    polynomials = [[0, 1], [1, 1], [1, 3], [2, 5, 0, 1]]
    for m in range(4, max_m + 1):
        p: list[int] = [0]
        _add_shift(p, polynomials[m - 1], 0)
        _add_shift(p, polynomials[m - 1], 1)
        _add_shift(p, polynomials[m - 2], 0)
        _add_shift(p, polynomials[m - 2], 1, -1)
        _add_shift(p, polynomials[m - 2], 2)
        _add_shift(p, polynomials[m - 3], 1, -1)
        _add_shift(p, polynomials[m - 3], 2, -1)
        if any(x < 0 for x in p):
            raise ArithmeticError("Unexpected negative histogram entry")
        polynomials.append(_trim(p))
    return polynomials[:max_m + 1]


def histogram_below(bound: int) -> list[int]:
    """Histogram of v2(a(n)) for 0 <= n < bound, without enumeration.

    Read n and bound from right to left. When the current bits differ,
    their comparison overrides the comparison of the lower bits. This
    makes the six-state automaton into an 18-state digit dynamic program.
    Complexity: O(log(bound)**2) integer coefficient updates and
    O(log(bound)) stored integer coefficients (constant number of states).
    """
    _nat(bound, "bound")
    if bound == 0:
        return [0]
    # Keys are (automaton_state, comparison of processed low-bit strings).
    dp: dict[tuple[int, int], list[int]] = {(0, 0): [1]}
    for i in range(bound.bit_length()):
        upper_bit = (bound >> i) & 1
        ndp: dict[tuple[int, int], list[int]] = {}
        for (state, relation), p in dp.items():
            for bit in (0, 1):
                ns, shift = TRANSITIONS[state][bit]
                nr = relation if bit == upper_bit else (-1 if bit < upper_bit else 1)
                target = ndp.setdefault((ns, nr), [0])
                _add_shift(target, p, shift)
        dp = ndp
    result = [0]
    for (state, relation), p in dp.items():
        if relation == -1:
            _add_shift(result, p, TERMINAL_EXPONENT[state])
    result = _trim(result)
    if sum(result) != bound:
        raise ArithmeticError("Digit-DP cardinality check failed")
    return result


def fibonacci(n: int) -> int:
    _nat(n)
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def least_positive_index(r: int) -> int:
    """Least positive n with v2(a(n))=r, from the proved exact formula."""
    _nat(r, "r")
    if r < 3:
        return (1, 2, 13)[r]
    return (2 ** (r + 1) + 6 + 4 * (-1) ** r) // 3


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--n", type=int, help="evaluate one index")
    group.add_argument("--bound", type=int, help="histogram for 0 <= n < bound")
    group.add_argument("--dyadic", type=int, help="histogram for 0 <= n < 2**m")
    group.add_argument("--least", type=int, help="least positive index of valuation r")
    args = parser.parse_args()
    try:
        if args.n is not None:
            n = args.n
            result = {"n": n, "valuation": valuation(n),
                      "automaton_valuation": automaton_valuation(n),
                      "odd": is_odd_term(n), "binary": format(n, "b")}
            if n <= 1000:
                result["a_n"] = str(a000139(n))
        elif args.bound is not None:
            result = {"bound": args.bound, "counts_by_valuation": histogram_below(args.bound)}
        elif args.dyadic is not None:
            result = {"m": args.dyadic,
                      "counts_by_valuation": dyadic_histograms(args.dyadic)[-1]}
        else:
            result = {"r": args.least, "least_positive_index": least_positive_index(args.least)}
    except ValueError as exc:
        parser.error(str(exc))
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
