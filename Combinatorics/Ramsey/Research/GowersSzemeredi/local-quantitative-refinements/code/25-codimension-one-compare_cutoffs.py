#!/usr/bin/env python3
"""Reproduce the illustrative d=8 cutoff table (standard library only).

The mathematical thresholds use exact integers. Their base-10 logarithms
are ordinary double-precision approximations, used only for presentation.
"""
from __future__ import annotations

import json
import math
from pathlib import Path


def main() -> None:
    d = 8
    reciprocal_tau = 10**6
    central_trinomial = sum(
        math.comb(2*d, j)*math.comb(2*d-j, j) for j in range(d+1)
    )
    hyperplanes = (central_trinomial-2*math.comb(2*d, d)+1)//2
    rows = []
    for k in range(1, 5):
        n = 2*d*2**k
        leading = k+hyperplanes
        residual = (3**n-3**(2*d))//2
        old = math.log10(k*3**n*reciprocal_tau)
        first = math.log10(2*leading*reciprocal_tau)
        second = 0.5*math.log10(2*residual*reciprocal_tau)
        rows.append({
            "k": k, "n": n,
            "old_log10": old,
            "first_log10": first,
            "second_log10": second,
            "new_log10": max(first, second),
            "controlling_term": "first-order" if first >= second else "second-order",
        })
    result = {
        "d": d, "tau": "1/1000000", "rows": rows,
        "note": "Sufficient criteria, not minimal sizes; logarithms are approximate."
    }
    target = Path(__file__).resolve().parents[1]/"data"/"cutoff_comparison.json"
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    for row in rows:
        print(f"k={row['k']}: old log10={row['old_log10']:.3f}, "
              f"new log10={row['new_log10']:.3f} ({row['controlling_term']})")


if __name__ == "__main__":
    main()
