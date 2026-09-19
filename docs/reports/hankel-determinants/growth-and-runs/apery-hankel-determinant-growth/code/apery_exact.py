#!/usr/bin/env python3
"""Exact Apéry moments and leading Hankel determinants (Python 3.10+).

No third-party dependencies. Fractions and modular elimination in verify.py
provide checks independent of the fraction-free elimination used here.
"""
from __future__ import annotations

import argparse
import math
import operator
import sys
from pathlib import Path
from typing import Sequence

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


def apery_binomial(n: int) -> int:
    """A_n from its defining sum, independent of the recurrence."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    return sum((math.comb(n, k) * math.comb(n + k, k)) ** 2
               for k in range(n + 1))


def apery_moments(last: int) -> list[int]:
    """Return A_0, ..., A_last using the classical exact recurrence."""
    if last < 0:
        raise ValueError("last must be nonnegative")
    values = [1]
    if last == 0:
        return values
    values.append(5)
    for n in range(1, last):
        numerator = ((2 * n + 1) * (17 * n * n + 17 * n + 5) * values[n]
                     - n ** 3 * values[n - 1])
        quotient, remainder = divmod(numerator, (n + 1) ** 3)
        if remainder:
            raise ArithmeticError(f"nonexact Apéry recurrence at n={n}")
        values.append(quotient)
    return values


def leading_hankel(moments: Sequence[int], n: int) -> list[int]:
    """Leading determinants of orders 1 through n+1, without pivoting.

    Requires positive leading pivots. This holds for the Apéry moment matrices
    and all nonnegative integer shifts/positive integer strides used here.
    Every division is checked. O(n^3) integer operations; not a bit-cost bound.
    """
    if n < 0 or len(moments) < 2 * n + 1:
        raise ValueError("need n >= 0 and at least 2*n+1 moments")
    a = [[operator.index(moments[i + j]) for j in range(n + 1)]
         for i in range(n + 1)]
    previous = 1
    determinants: list[int] = []
    for k in range(n):
        pivot = a[k][k]
        if pivot <= 0:
            raise ArithmeticError(f"nonpositive leading pivot at k={k}")
        determinants.append(pivot)
        for i in range(k + 1, n + 1):
            aik = a[i][k]
            for j in range(i, n + 1):
                numerator = pivot * a[i][j] - aik * a[k][j]
                value, remainder = divmod(numerator, previous)
                if remainder:
                    raise ArithmeticError(f"nonexact Bareiss division {(k,i,j)}")
                a[i][j] = a[j][i] = value
        for i in range(k + 1, n + 1):
            a[i][k] = a[k][i] = 0
        previous = pivot
    if a[n][n] <= 0:
        raise ArithmeticError("nonpositive final pivot")
    determinants.append(a[n][n])
    return determinants


def apery_hankel(n: int, stride: int = 1, shift: int = 0) -> list[int]:
    """Return det(A_{stride*(i+j)+shift})_{i,j=0..k}, k=0..n."""
    if n < 0 or stride < 1 or shift < 0:
        raise ValueError("need n>=0, stride>=1, shift>=0")
    values = apery_moments(2 * stride * n + shift)
    selected = [values[stride * j + shift] for j in range(2 * n + 1)]
    return leading_hankel(selected, n)


def read_table(path: Path) -> list[int]:
    """Read consecutive 'index integer' records (comments allowed)."""
    out: list[int] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        fields = line.split()
        if len(fields) != 2:
            raise ValueError(f"malformed record in {path}")
        n, value = map(int, fields)
        if n != len(out) or value <= 0:
            raise ValueError(f"nonconsecutive index or nonpositive value in {path}")
        out.append(value)
    if not out:
        raise ValueError(f"empty table: {path}")
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, default=32, help="largest determinant index")
    parser.add_argument("--stride", type=int, default=1)
    parser.add_argument("--shift", type=int, default=0)
    parser.add_argument("--output", type=Path, help="otherwise write to stdout")
    args = parser.parse_args()
    try:
        values = apery_hankel(args.n, args.stride, args.shift)
    except (ValueError, ArithmeticError) as exc:
        parser.exit(2, f"error: {exc}\n")
    text = "# index exact_determinant\n" + "".join(
        f"{n} {value}\n" for n, value in enumerate(values))
    if args.output is None:
        sys.stdout.write(text)
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")


if __name__ == "__main__":
    main()
