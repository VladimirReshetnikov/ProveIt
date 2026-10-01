#!/usr/bin/env python3
"""Exact integer-coefficient certificate for the three-left-vertex marginal.

No third-party packages are used. The output contains the complete degree-six
determinant expansion and a canonical SHA-256 digest of its coefficient list.
"""
from itertools import permutations
from pathlib import Path
import hashlib
import json

N = 11
ZERO = (0,) * N
NAMES = ["x1", "x2", "x4", "y3", "z3", "y5", "z5", "y6", "z6", "y7", "z7"]

def var(i):
    e = list(ZERO); e[i] = 1
    return {tuple(e): 1}

def add(*args):
    out = {}
    for p in args:
        for e, c in p.items(): out[e] = out.get(e, 0) + c
    return {e: c for e, c in out.items() if c}

def scale(p, c): return {e: c * v for e, v in p.items() if c * v}

def mul(p, q):
    out = {}
    for e, c in p.items():
        for f, d in q.items():
            ef = tuple(x + y for x, y in zip(e, f))
            out[ef] = out.get(ef, 0) + c * d
    return {e: c for e, c in out.items() if c}

def determinant(m):
    terms = []
    for p in permutations(range(3)):
        sign = (-1) ** sum(p[i] > p[j] for i in range(3) for j in range(i + 1, 3))
        terms.append(scale(mul(mul(m[0][p[0]], m[1][p[1]]), m[2][p[2]]), sign))
    return add(*terms)

def main():
    mass = {1: var(0), 2: var(1), 4: var(2)}
    second = {}
    for mask, i in zip((3, 5, 6, 7), (3, 5, 7, 9)):
        mass[mask] = add(var(i), var(i + 1))
        second[mask] = mul(var(i), var(i))
    c = [add(*(mass[s] for s in mass if s & (1 << i))) for i in range(3)]
    matrix = [[{} for _ in range(3)] for _ in range(3)]
    for i in range(3):
        matrix[i][i] = scale(mul(c[i], c[i]), 4)
        for j in range(i):
            both = (1 << i) | (1 << j)
            s = add(*(mass[m] for m in mass if m & both == both))
            p2 = add(*(second[m] for m in second if m & both == both))
            matrix[i][j] = matrix[j][i] = add(scale(mul(c[i], c[j]), -2), scale(add(mul(s, s), p2), 3))
    det = determinant(matrix)
    if not det or any(c <= 0 for c in det.values()):
        raise RuntimeError("The determinant certificate has a nonpositive coefficient")
    if any(sum(e) != 6 for e in det):
        raise RuntimeError("Unexpected determinant degree")
    records = [[list(e), c] for e, c in sorted(det.items())]
    canonical = json.dumps(records, separators=(",", ":"))
    result = {
        "variables": NAMES,
        "coefficient_count": len(records),
        "minimum_coefficient": min(det.values()),
        "maximum_coefficient": max(det.values()),
        "canonical_sha256": hashlib.sha256(canonical.encode()).hexdigest(),
        "all_coefficients_positive": True,
        "coefficients": records,
    }
    target = Path(__file__).parents[1] / "data" / "determinant.json"
    if target.exists():
        previous = json.loads(target.read_text())
        if result != previous:
            raise RuntimeError("Generated determinant differs from the certificate")
    else:
        target.write_text(json.dumps(result, separators=(",", ":")) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "coefficients"}, indent=2))

if __name__ == "__main__": main()
