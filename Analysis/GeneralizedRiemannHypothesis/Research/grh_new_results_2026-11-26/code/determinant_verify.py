#!/usr/bin/env python3
"""Exact checks for arithmetic determinant amplification.

No third-party dependencies. This does not replace the mathematical proof.
Run from any directory; output defaults to ../artifacts/determinant_results.json.
"""

from fractions import Fraction
from functools import reduce
from itertools import combinations
from math import comb, gcd
from pathlib import Path
import json


def determinant(matrix):
    """Exact Gaussian elimination over rationals, returning an integer."""
    n = len(matrix)
    work = [[Fraction(x) for x in row] for row in matrix]
    result = Fraction(1)
    for j in range(n):
        pivot = next((i for i in range(j, n) if work[i][j]), None)
        if pivot is None:
            return 0
        if pivot != j:
            work[j], work[pivot] = work[pivot], work[j]
            result = -result
        value = work[j][j]
        result *= value
        for i in range(j + 1, n):
            ratio = work[i][j] / value
            for k in range(j + 1, n):
                work[i][k] -= ratio * work[j][k]
    assert result.denominator == 1
    return int(result)


def analyze(matrix):
    r, n = len(matrix), len(matrix[0])
    minors = [determinant([[matrix[i][j] for j in subset] for i in range(r)])
              for subset in combinations(range(n), r)]
    D = reduce(gcd, (abs(v) for v in minors), 0)
    assert D > 0
    gram = [[sum(matrix[i][k] * matrix[j][k] for k in range(n))
             for j in range(r)] for i in range(r)]
    gram_determinant = determinant(gram)
    assert gram_determinant == sum(v * v for v in minors)
    N, z = comb(n, r), minors.count(0)
    S = Fraction(gram_determinant, D * D)
    bounds = [Fraction(N - z), Fraction(8 * N, 5) - 4 * z,
              Fraction(12 * N, 5) - 12 * z]
    assert S >= max(bounds)
    return {
        "matrix": matrix, "rank": r, "columns": n,
        "minor_count": N, "zero_minors": z, "minor_gcd": D,
        "signed_maximal_minors": minors, "gram": gram,
        "gram_determinant": gram_determinant,
        "normalized_determinant": str(S),
        "three_lower_bounds": [str(x) for x in bounds],
        "attained_bounds": [i + 1 for i, x in enumerate(bounds) if x == S],
    }


def finite_gap_check():
    """Exhaust the unit-minor normal form with determinant less than 36.

    If all 10 minors are nonzero and S < 36, a minor has magnitude 1,
    since otherwise S >= 40. Normalize that pair to e1,e2. Every other
    column has two nonzero integer coordinates. Flip its sign to make
    its first coordinate positive. Since S=1+sum column norms squared
    +sum of three other minor squares, both coordinates have magnitude
    at most 5. Permuting the final three columns lets us use combinations.
    """
    vectors = [(x, y) for x in range(1, 6) for y in range(-5, 6) if y]
    examined = 0
    full_spark = 0
    below_36 = []
    for triple in combinations(vectors, 3):
        examined += 1
        pair_minors = [a[0] * b[1] - a[1] * b[0]
                       for a, b in combinations(triple, 2)]
        if 0 in pair_minors:
            continue
        full_spark += 1
        S = 1 + sum(x * x + y * y for x, y in triple)
        S += sum(d * d for d in pair_minors)
        if S < 36:
            assert S == 24
            below_36.append({"remaining_columns": triple, "determinant": S})
    assert len(below_36) == 14
    return {
        "normal_form": "[e1,e2,(x1,y1),(x2,y2),(x3,y3)], 1<=xi<=5, 1<=abs(yi)<=5",
        "candidate_triples_examined": examined,
        "full_spark_triples_examined": full_spark,
        "below_36_count": len(below_36),
        "determinants_below_36": sorted({row["determinant"] for row in below_36}),
        "below_36_examples": below_36,
        "role": "Exact optional finite gap check; not needed for the theorem proof.",
    }


def main():
    matrices = {
        "no_zero_minor": [[1, 0, 1, 1, 1], [0, 1, 1, -1, 2]],
        "one_zero_minor": [[1, 1, 0, 1, 1], [0, 0, 1, 1, -1]],
        "two_zero_minors": [[1, 1, 0, 0, 1], [0, 0, 1, 1, 1]],
        "three_zero_minors": [[1, 1, 1, 0, 1], [0, 0, 0, 1, 1]],
        "rank_three_dual": [[-1, -1, 1, 0, 0], [-1, 1, 0, 1, 0],
                            [-1, -2, 0, 0, 1]],
    }
    examples = {name: analyze(matrix) for name, matrix in matrices.items()}
    assert [examples[name]["gram_determinant"] for name in matrices] == [24, 12, 8, 7, 24]
    results = {
        "theorem": "S >= max(N-z, 8*N/5-4*z, 12*N/5-12*z)",
        "assumptions": "A integer full row rank r, n>=5, 2<=r<=n-2; N=choose(n,r); D=gcd(nonzero maximal minors); S=det(AA^T)/D^2",
        "examples": examples, "optional_finite_gap_check": finite_gap_check(),
        "status": "All exact checks passed.",
    }
    output = Path(__file__).resolve().parents[1] / "artifacts" / "determinant_results.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(results, indent=2) + "\n")
    print(f"All exact checks passed; {len(examples)} equality examples.")
    print(f"Optional finite check: {results['optional_finite_gap_check']['candidate_triples_examined']} triples; only determinant 24 below 36.")
    print(output)


if __name__ == "__main__":
    main()
