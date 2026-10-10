#!/usr/bin/env python3
"""Exact formal classification for the Herglotz companion J(p/q).

This classifies reduction in the rationalized five-term calculus. It does
not decide arbitrary identities between evaluated transcendental numbers.
"""
from __future__ import annotations
import argparse
import json
from math import gcd


def classify(p: int, q: int) -> dict:
    if isinstance(p, bool) or isinstance(q, bool) or not isinstance(p, int) or not isinstance(q, int):
        raise TypeError("p and q must be integers")
    if p <= 0 or q <= 0:
        raise ValueError("p and q must be positive")
    d = gcd(p, q)
    p, q = p // d, q // d
    result = {"p": p, "q": q, "formal_logarithmic": False,
              "formal_rational_dilogarithmic": False}
    if p == q == 1:
        result.update(formal_logarithmic=True, formal_rational_dilogarithmic=True,
                      reason="J(1) = log(2)^2/2")
    elif p % 2 and q % 2:
        ok = p in (1, 3, 5) and q in (1, 3, 5)
        result.update(formal_rational_dilogarithmic=ok,
                      reason="odd/odd: both reduced entries must lie in {1,3,5}",
                      rational_boundary="<2> wedge <p/q>")
    else:
        e, o = (p, q) if p % 2 == 0 else (q, p)
        first = pow(e, 2, o) in {1 % o, (-1) % o}
        second = pow(o, 2, 2 * e) == 1
        ok = first and second
        result.update(formal_logarithmic=ok, formal_rational_dilogarithmic=ok,
                      even=e, odd=o, odd_conductor_test=first,
                      new_dyadic_layer_test=second,
                      reason="e^2 = +/-1 (mod o) and o^2 = 1 (mod 2e)")
    return result


def recurrence_pairs(bound: int) -> dict[tuple[int, int], list[dict]]:
    """Unordered coprime logarithmically reducible pairs with max <= bound.

    The exceptional ratio 1 is not included. Different families share seeds.
    """
    if bound < 1:
        raise ValueError("bound must be positive")
    found: dict[tuple[int, int], list[dict]] = {}
    for c in range(2, bound + 1, 2):
        for sign in (-1, 1):
            a, b, j = 1, c, 0
            while b <= bound:
                found.setdefault((a, b), []).append({"coefficient": c,
                                                     "sign": sign, "index": j})
                a, b, j = b, c * b + sign * a, j + 1
    return found


def count_pairs(bound: int) -> int:
    """Count without storing pairs. Seeds common to both signs counted once."""
    if bound < 1:
        raise ValueError("bound must be positive")
    total = bound // 2
    # c=2, minus: all consecutive pairs after the seed (1,2).
    total += max(0, bound - 2)
    for sign in (-1, 1):
        c = 4 if sign == -1 else 2
        while c * c + sign <= bound:
            a, b = c, c * c + sign
            while b <= bound:
                total += 1
                a, b = b, c * b + sign * a
            c += 2
    return total


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("p", type=int)
    parser.add_argument("q", type=int)
    args = parser.parse_args()
    try:
        result = classify(args.p, args.q)
    except (TypeError, ValueError) as exc:
        parser.error(str(exc))
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()
