#!/usr/bin/env python3
"""A natural-number-only executable specification of the iPRA target.

Fractions are pairs (numerator, positive denominator), without normalization.
All loops have a supplied natural-number bound.  The intended functions are
primitive recursive.  This program evaluates instances; it is not a proof
checker and does not establish the universally quantified theorem.

For S_n=u/v and P_k=a/b, the target is exactly

  n >= 2^(2k+7) -> 2^k * |6*u*b^2 - a^2*v| <= v*b^2.

P_k is 4 times the even Gregory partial sum at N(k)=2^(2k+7).
Pairing neighboring terms allows P_k to be computed with natural numbers only.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import json


@dataclass(frozen=True)
class NatFraction:
    numerator: int
    denominator: int


def add(x: NatFraction, y: NatFraction) -> NatFraction:
    return NatFraction(
        x.numerator * y.denominator + y.numerator * x.denominator,
        x.denominator * y.denominator,
    )


def cutoff(k: int) -> int:
    return 2 ** (2 * k + 7)


def square_partial(n: int) -> NatFraction:
    answer = NatFraction(0, 1)
    for j in range(1, n + 1):
        answer = add(answer, NatFraction(1, j * j))
    return answer


def pi_partial(k: int) -> NatFraction:
    # 4(1/(4j+1)-1/(4j+3)) = 8/((4j+1)(4j+3)).
    answer = NatFraction(0, 1)
    for j in range(cutoff(k) // 2):
        answer = add(answer, NatFraction(8, (4 * j + 1) * (4 * j + 3)))
    return answer


def natural_distance(x: int, y: int) -> int:
    return (x - y) if y <= x else (y - x)


def target(k: int, n: int) -> bool:
    if n < cutoff(k):
        return True  # The implication has a false antecedent.
    zeta, pi = square_partial(n), pi_partial(k)
    assert zeta.denominator > 0 and pi.denominator > 0
    left = 2**k * natural_distance(
        6 * zeta.numerator * pi.denominator**2,
        pi.numerator**2 * zeta.denominator,
    )
    right = zeta.denominator * pi.denominator**2
    return left <= right


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--k", type=int, default=0)
    parser.add_argument("--n", type=int, help="Default: N(k).")
    args = parser.parse_args()
    if args.k < 0 or (args.n is not None and args.n < 0):
        parser.error("Inputs represent natural numbers and must be nonnegative.")
    n = cutoff(args.k) if args.n is None else args.n
    result = target(args.k, n)
    print(json.dumps({
        "k": args.k, "n": n, "cutoff": cutoff(args.k),
        "target_holds": result,
        "arithmetic": "unreduced natural fractions; no gcd, floating point, or real-number library",
        "status": "evaluated instance, not a universal proof",
    }, indent=2))
    if not result:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
