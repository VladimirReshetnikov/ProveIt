#!/usr/bin/env python3
"""Finite integer verification of the elliptic duplication resultant identity.

Each nonzero Sylvester entry is a single monomial c*A^i*B^j. Expanding its
8x8 determinant over all 8! permutations and collecting integer coefficients
therefore verifies a polynomial identity, not merely sampled evaluations.
"""

from itertools import permutations
from math import factorial


def symbolic_duplication_resultant() -> dict:
    # A monomial is (integer coefficient, exponent of A, exponent of B).
    zero = (0, 0, 0)
    f = [(1, 0, 0), zero, (-2, 1, 0), (-8, 0, 1), (1, 2, 0)]
    g = [zero, (4, 0, 0), zero, (4, 1, 0), (4, 0, 1)]
    matrix = [[zero] * 8 for _ in range(8)]
    for j in range(4):
        for k in range(5):
            matrix[j + k][j] = f[k]
            matrix[j + k][4 + j] = g[k]
    coefficients = {}
    nonzero_terms = 0
    for permutation in permutations(range(8)):
        coefficient, ea, eb = 1, 0, 0
        for row, column in enumerate(permutation):
            c, a, b = matrix[row][column]
            coefficient *= c
            ea += a
            eb += b
            if coefficient == 0:
                break
        if coefficient == 0:
            continue
        nonzero_terms += 1
        inversions = sum(permutation[i] > permutation[j]
                         for i in range(8) for j in range(i + 1, 8))
        if inversions % 2:
            coefficient = -coefficient
        coefficients[(ea, eb)] = coefficients.get((ea, eb), 0) + coefficient
    coefficients = {power: c for power, c in coefficients.items() if c}
    target = {(6, 0): 4096, (3, 2): 55296, (0, 4): 186624}
    return {
        "identity": "det(S) = 256*(4*A^3+27*B^2)^2 = discriminant^2",
        "permutations_checked": factorial(8),
        "nonzero_permutation_terms": nonzero_terms,
        "coefficient_order": "[exponent_of_A, exponent_of_B, integer_coefficient]",
        "computed_coefficients": [[a, b, coefficients[(a, b)]] for a, b in sorted(coefficients)],
        "target_coefficients": [[a, b, target[(a, b)]] for a, b in sorted(target)],
        "verified": coefficients == target,
        "scope": "exact polynomial coefficient identity; ordinary Python computation, not a Lean proof object",
    }


if __name__ == "__main__":
    import json
    report = symbolic_duplication_resultant()
    print(json.dumps(report, indent=2))
    raise SystemExit(0 if report["verified"] else 1)
