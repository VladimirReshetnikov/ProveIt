"""Independent exhaustive validation of the joint Gram nullity first moment.

Uses elementary prime-field elimination and Fraction; no project code imports.
Run: python3 independent_moment_check.py > independent_moment_results.json
This is finite validation, not the proof of the general theorem.
"""

from fractions import Fraction
from itertools import product
import json


def rank_mod(matrix, q):
    a = [row[:] for row in matrix]
    n = len(a)
    m = len(a[0]) if n else 0
    rank = 0
    for c in range(m):
        pivot = next((i for i in range(rank, n) if a[i][c] % q), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        inv = pow(a[rank][c] % q, -1, q)
        a[rank] = [(x * inv) % q for x in a[rank]]
        for i in range(rank + 1, n):
            scale = a[i][c] % q
            if scale:
                a[i] = [(x - scale * y) % q for x, y in zip(a[i], a[rank])]
        rank += 1
        if rank == n:
            break
    return rank


def check_case(q, dimensions, half_ranks):
    D = sum(dimensions)
    block, starts = [], []
    for i, d in enumerate(dimensions):
        starts.append(len(block))
        block.extend([i] * d)
    cross = [(i, j) for i in range(D) for j in range(i + 1, D)
             if block[i] != block[j]]
    base = [[0] * D for _ in range(D)]
    for start, s in zip(starts, half_ranks):
        for j in range(s):
            base[start + 2*j][start + 2*j + 1] = 1
            base[start + 2*j + 1][start + 2*j] = q - 1
    tally = 0
    for values in product(range(q), repeat=len(cross)):
        matrix = [row[:] for row in base]
        for (i, j), value in zip(cross, values):
            matrix[i][j], matrix[j][i] = value, (-value) % q
        tally += q ** (D - rank_mod(matrix, q))
    actual = Fraction(tally, q ** len(cross))
    predicted = 1 + Fraction(q**D - 1 - sum(q**d - 1 for d in dimensions),
                             q ** (D - 1))
    predicted += sum(Fraction(q**(d - 2*s) - 1, q**(D - d))
                     for d, s in zip(dimensions, half_ranks))
    assert actual == predicted, (q, dimensions, half_ranks, actual, predicted)
    return {"q": q, "dimensions": dimensions, "half_ranks": half_ranks,
            "matrices": q ** len(cross), "mean_kernel_size": str(actual)}


def main():
    configurations = [(2, (1, 1, 1)), (2, (2, 1, 1)), (2, (2, 2, 1)),
                      (2, (2, 2, 2)), (2, (1, 1, 1, 1)),
                      (3, (1, 1, 1)), (3, (2, 1, 1)), (3, (2, 2, 1))]
    results = []
    for q, dimensions in configurations:
        for half_ranks in product(*(range(d // 2 + 1) for d in dimensions)):
            results.append(check_case(q, dimensions, half_ranks))
    print(json.dumps({"status": "all passed", "passed": len(results),
                      "matrix_evaluations": sum(r["matrices"] for r in results),
                      "cases": results}, indent=2))


if __name__ == "__main__":
    main()
