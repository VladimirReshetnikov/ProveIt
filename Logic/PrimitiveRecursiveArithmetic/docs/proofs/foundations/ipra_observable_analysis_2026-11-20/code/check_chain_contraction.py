#!/usr/bin/env python3
"""Exact rational regression for the normed chain-complex repair theorem.

The tested 4-by-4 example has h*h != 0 and h*R != R*h, so the
identities do not accidentally rely on those unnecessary hypotheses.
This is an example check, not a proof of the general theorem.
"""
from fractions import Fraction as Q
import json
from pathlib import Path


def zero(n):
    return [[Q(0) for _ in range(n)] for _ in range(n)]


def eye(n):
    a = zero(n)
    for i in range(n):
        a[i][i] = Q(1)
    return a


def add(a, b):
    return [[x + y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def sub(a, b):
    return [[x - y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def mul(a, b):
    n = len(a)
    return [[sum((a[i][k] * b[k][j] for k in range(n)), Q(0))
             for j in range(n)] for i in range(n)]


def norm1(a):
    """Exact operator norm induced by the l1 vector norm."""
    return max(sum(abs(a[i][j]) for i in range(len(a)))
               for j in range(len(a)))


def powersum(a, n):
    """Sequential reference returning (a**n, sum_{j<n} a**j)."""
    p, s = eye(len(a)), zero(len(a))
    for _ in range(n):
        s = add(s, p)
        p = mul(p, a)
    return p, s


def inverse(a):
    """Independent exact Gauss-Jordan inverse; only for this finite test."""
    n = len(a)
    ident = eye(n)
    b = [a[i][:] + ident[i] for i in range(n)]
    for col in range(n):
        pivot = next(i for i in range(col, n) if b[i][col] != 0)
        b[col], b[pivot] = b[pivot], b[col]
        v = b[col][col]
        b[col] = [x / v for x in b[col]]
        for i in range(n):
            if i != col:
                v = b[i][col]
                b[i] = [x - v*y for x, y in zip(b[i], b[col])]
    return [row[n:] for row in b]


def main():
    n = 4
    z, ident = zero(n), eye(n)
    # Degrees: e0 has degree 0; e1,e2 degree 1; e3 degree 2.
    d = zero(n)
    d[0][1] = d[2][3] = Q(1)
    h = zero(n)
    h[1][0] = h[3][2] = Q(3, 4)
    h[2][0] = Q(1, 16)
    h[3][1] = Q(1, 8)
    r = sub(sub(ident, mul(d, h)), mul(h, d))
    assert mul(d, d) == z
    assert mul(h, h) != z
    assert mul(h, r) != mul(r, h)
    assert mul(d, r) == mul(r, d)
    assert norm1(r) == Q(7, 16)
    assert norm1(h) == Q(13, 16)
    exact = mul(h, inverse(sub(ident, r)))
    assert add(mul(d, exact), mul(exact, d)) == ident
    records = []
    for count in [0, 1, 2, 3, 8, 17]:
        p, s = powersum(r, count)
        h_n = mul(h, s)
        residual = sub(ident, add(mul(d, h_n), mul(h_n, d)))
        assert residual == p
        assert mul(sub(ident, r), s) == sub(ident, p)
        assert mul(s, sub(ident, r)) == sub(ident, p)
        tail_bound = norm1(h) * Q(1, 2)**count / (1 - Q(1, 2))
        actual_error = norm1(sub(exact, h_n))
        assert actual_error <= tail_bound
        records.append({"N": count, "residual_norm": str(norm1(residual)),
                        "actual_error_norm": str(actual_error),
                        "certified_tail_bound": str(tail_bound)})
    schedule_records = []
    # s=1, c=0 and N(k)=2**s*(k+s+c+2).
    for k in range(9):
        count = 2*(k+3)
        _, s = powersum(r, count)
        error = norm1(sub(exact, mul(h, s)))
        target = Q(1, 2)**(k+2)
        assert error <= target
        schedule_records.append({"precision": k, "N": count,
                                 "error": str(error), "target": str(target)})
    result = {
        "status": "passed",
        "arithmetic": "fractions.Fraction (exact rational)",
        "dimension": n,
        "d_squared_zero": True,
        "h_squared_nonzero": True,
        "h_and_defect_do_not_commute": True,
        "candidate_h_norm": str(norm1(h)),
        "defect_norm": str(norm1(r)),
        "finite_identities": records,
        "precision_schedule": schedule_records,
        "scope": "finite rational example; general identity is proved in Lean and in the report"
    }
    output = Path(__file__).resolve().parents[1] / "evidence" / "chain_contraction_check.json"
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "output": str(output),
                      "finite_cases": len(records), "precision_cases": len(schedule_records)}))


if __name__ == "__main__":
    main()
