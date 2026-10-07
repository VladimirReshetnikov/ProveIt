#!/usr/bin/env python3
"""Exhaustive integer diagnostic for scalar graph energy on Z/13Z.

Translation of target values lets us normalize f(0)=0.  Thus 3**12
functions represent all 3**13 ternary functions.  The mathematical
proof in rigidity.tex does not depend on this finite verification.
"""
from collections import Counter
from pathlib import Path
import json
import numpy as np


def main():
    n = 13
    total = 3 ** (n - 1)
    batch_size = 16384
    histogram = Counter()
    equality_count = 0
    checked = 0
    max_nonconstant = 0
    for start in range(0, total, batch_size):
        ids = np.arange(start, min(start + batch_size, total), dtype=np.int64)
        values = np.zeros((len(ids), n), dtype=np.int16)
        remaining = ids.copy()
        for column in range(1, n):
            values[:, column] = remaining % 3
            remaining //= 3
        energy = np.full(len(ids), n * n, dtype=np.int64)
        for shift in range(1, (n + 1) // 2):
            differences = (np.roll(values, -shift, axis=1) - values) % 3
            c0 = np.count_nonzero(differences == 0, axis=1)
            c1 = np.count_nonzero(differences == 1, axis=1)
            c2 = n - c0 - c1
            energy += 2 * (c0 * c0 + c1 * c1 + c2 * c2)
        nonconstant = np.any(values != 0, axis=1)
        if nonconstant.any():
            max_nonconstant = max(max_nonconstant, int(energy[nonconstant].max()))
        for level, count in zip(*np.unique(energy, return_counts=True)):
            histogram[int(level)] += int(count)
        equality = energy == 1645
        equality_count += int(equality.sum())
        for row in values[equality]:
            frequencies = np.bincount(row, minlength=3)
            assert int(frequencies.max()) == 12
        checked += len(ids)
    assert checked == 531441
    assert max_nonconstant == 1645
    assert equality_count == 26
    assert histogram[2197] == 1
    result = {
        "status": "all exact checks passed",
        "normalized_functions_checked": checked,
        "all_functions_represented": 3 * checked,
        "maximum_nonconstant_energy": max_nonconstant,
        "maximizers_after_normalizing_f0_to_zero": equality_count,
        "all_maximizers_are_one_point_modifications": True,
        "largest_energy_levels": sorted(histogram.items(), reverse=True)[:8],
        "method": "integer derivative-color counts; target translations normalized",
    }
    destination = Path(__file__).with_name("order13_certificate.json")
    destination.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
