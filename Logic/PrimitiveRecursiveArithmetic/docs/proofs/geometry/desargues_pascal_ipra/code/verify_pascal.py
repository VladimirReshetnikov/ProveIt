#!/usr/bin/env python3
"""Exact, dependency-free polynomial certificates for constructive Pascal.

The coefficient ring is Z. A polynomial is a finite dictionary from a tuple of
variable indices (with repetition, sorted) to its nonzero integer coefficient.
All loops are over explicit finite ranges. This checks mathematical identities;
it is not a claim that an iPRA derivation or a Lean proof has been compiled.

Run: python3 verify_pascal.py
"""
from itertools import permutations
from hashlib import sha256
import json


def clean(p):
    return {m: c for m, c in p.items() if c}


def const(c):
    return {(): c} if c else {}


def var(i):
    return {(i,): 1}


def add(*polys):
    out = {}
    for p in polys:
        for m, c in p.items():
            out[m] = out.get(m, 0) + c
    return clean(out)


def scale(c, p):
    return clean({m: c * a for m, a in p.items()})


def sub(p, q):
    return add(p, scale(-1, q))


def mul(*polys):
    out = const(1)
    for p in polys:
        nxt = {}
        for m, c in out.items():
            for n, d in p.items():
                key = tuple(sorted(m + n))
                nxt[key] = nxt.get(key, 0) + c * d
        out = clean(nxt)
    return out


def cross(u, v):
    return [sub(mul(u[1], v[2]), mul(u[2], v[1])),
            sub(mul(u[2], v[0]), mul(u[0], v[2])),
            sub(mul(u[0], v[1]), mul(u[1], v[0]))]


def sign(p):
    inversions = sum(p[i] > p[j] for i in range(len(p))
                     for j in range(i + 1, len(p)))
    return -1 if inversions % 2 else 1


def det(rows):
    n = len(rows)
    return add(*(scale(sign(p), mul(*(rows[i][p[i]] for i in range(n))))
                 for p in permutations(range(n))))


def det3_columns(a, b, c):
    return det([[a[i], b[i], c[i]] for i in range(3)])


def veronese(p):
    x, y, z = p
    return [mul(x, x), mul(y, y), mul(z, z), mul(x, y),
            mul(x, z), mul(y, z)]


def digest(p):
    canonical = json.dumps([[list(m), c] for m, c in sorted(p.items())],
                           separators=(",", ":")).encode("ascii")
    return sha256(canonical).hexdigest()


def check(name, lhs, rhs):
    residual = sub(lhs, rhs)
    if residual:
        raise AssertionError((name, "nonzero residual", residual))
    return {"identity": name, "checked": True,
            "lhs_monomials": len(lhs), "rhs_monomials": len(rhs),
            "residual_monomials": 0, "common_polynomial_sha256": digest(lhs)}


def main():
    points = [[var(3 * i + j) for j in range(3)] for i in range(6)]
    a, b, c, d, e, f = points
    x = cross(cross(a, b), cross(d, e))
    y = cross(cross(b, c), cross(e, f))
    z = cross(cross(c, d), cross(f, a))
    pascal = det3_columns(x, y, z)
    matrix = [veronese(p) for p in points]
    conic_det = det(matrix)

    def br(i, j, k):
        return det3_columns(points[i - 1], points[j - 1], points[k - 1])

    bracket = sub(mul(br(1, 2, 5), br(1, 3, 4), br(2, 3, 6), br(4, 5, 6)),
                  mul(br(1, 2, 3), br(1, 4, 5), br(2, 5, 6), br(3, 4, 6)))
    checks = [check("Pascal determinant equals Veronese determinant",
                    pascal, conic_det),
              check("Two-term bracket formula", pascal, bracket),
              check("Plucker for determinant expansion 1",
                    sub(mul(br(1, 2, 5), br(1, 4, 6)),
                        mul(br(1, 2, 4), br(1, 5, 6))),
                    mul(br(1, 2, 6), br(1, 4, 5))),
              check("Plucker for determinant expansion 2",
                    sub(mul(br(1, 2, 6), br(2, 3, 5)),
                        mul(br(1, 2, 5), br(2, 3, 6))),
                    scale(-1, mul(br(1, 2, 3), br(2, 5, 6)))),
              check("Plucker for swap 1",
                    sub(mul(br(1, 3, 4), br(2, 3, 6)),
                        mul(br(2, 3, 4), br(1, 3, 6))),
                    mul(br(1, 2, 3), br(3, 4, 6))),
              check("Plucker for swap 2",
                    sub(mul(br(2, 4, 5), br(1, 5, 6)),
                        mul(br(1, 4, 5), br(2, 5, 6))),
                    scale(-1, mul(br(1, 2, 5), br(4, 5, 6))))]

    # Six explicit ideal-membership certificates. The input coefficients q_j
    # are variables 18,...,23. The conic evaluations are linear combinations
    # of the six quadratic monomials at each vertex.
    coeffs = [var(18 + j) for j in range(6)]
    evaluations = [add(*(mul(matrix[i][j], coeffs[j]) for j in range(6)))
                   for i in range(6)]
    for j in range(6):
        rhs = {}
        for i in range(6):
            minor = [[matrix[r][s] for s in range(6) if s != j]
                     for r in range(6) if r != i]
            cofactor = scale((-1) ** (i + j), det(minor))
            rhs = add(rhs, mul(cofactor, evaluations[i]))
        checks.append(check("Conic cofactor certificate for coefficient %d" % j,
                            mul(pascal, coeffs[j]), rhs))

    print(json.dumps({
        "description": "Exact universal identities over Z; no numerical sampling",
        "coordinate_variables": 18,
        "conic_coefficient_variables": 6,
        "pascal_degree": 12,
        "pascal_monomial_count": len(pascal),
        "pascal_coefficients": sorted(set(pascal.values())),
        "certificates": checks,
        "status": "all identities verified",
        "limitation": "This checker is not a compiled iPRA or Lean proof object."
    }, indent=2))


if __name__ == "__main__":
    main()
