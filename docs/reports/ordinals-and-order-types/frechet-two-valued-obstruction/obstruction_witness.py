#!/usr/bin/env python3
"""Exact arithmetic certificates for the two-valued Frechet obstruction.

This module does not represent arbitrary infinite filters or prove the sheaf
axiom computationally. It extracts the explicit integer at the final step of
the paper's contradiction, given the alleged cofinite cutoffs.

Only Python's standard library is used. Python 3.9+ is sufficient.
"""
from __future__ import annotations

import argparse
import json
from typing import Dict


def _natural(value: int, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(f"{name} must be an integer (not a boolean)")
    if value < 0:
        raise ValueError(f"{name} must be nonnegative")
    return value


def row_index(j: int) -> int:
    """Return the unique n for which j = 2**n * (2*k+1) - 1."""
    j = _natural(j, "j")
    t = j + 1
    return (t & -t).bit_length() - 1


def in_row(j: int, n: int) -> bool:
    _natural(n, "n")
    return row_index(j) == n


def in_tail(j: int, m: int) -> bool:
    _natural(j, "j")
    _natural(m, "m")
    return (j + 1) % (1 << m) == 0


def contradiction_witness(m: int, cutoff_zero: int, cutoff_one: int) -> Dict[str, int]:
    """Find least j >= both cutoffs in row B_m, hence also in tail T_m.

    A putative amalgam would have f(j)=a0 by its row condition and f(j)=a1
    by its tail condition. These cannot both hold for distinct a0 and a1.
    Integer arithmetic is exact; there is no floating-point calculation.
    """
    m = _natural(m, "m")
    n0 = _natural(cutoff_zero, "cutoff_zero")
    n1 = _natural(cutoff_one, "cutoff_one")
    threshold = max(n0, n1)
    residue = (1 << m) - 1
    period = 1 << (m + 1)
    q = max(0, (threshold - residue + period - 1) // period)
    j = residue + period * q
    return {"m": m, "cutoff_zero": n0, "cutoff_one": n1,
            "j": j, "row_parameter": q, "period": period}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("m", type=int)
    parser.add_argument("cutoff_zero", type=int)
    parser.add_argument("cutoff_one", type=int)
    args = parser.parse_args()
    try:
        result = contradiction_witness(args.m, args.cutoff_zero, args.cutoff_one)
    except (TypeError, ValueError) as exc:
        parser.error(str(exc))
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
