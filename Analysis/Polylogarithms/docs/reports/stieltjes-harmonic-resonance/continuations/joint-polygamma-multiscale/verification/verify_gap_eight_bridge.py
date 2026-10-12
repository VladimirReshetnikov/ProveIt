"""Independent exact rational checks of the finite-field certificate bridge.

Requires SymPy. The all-index proof is in the accompanying article; finite rational
nonvanishing is certified by verify_gap_eight.cpp and its JSON output.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import math
from pathlib import Path

import sympy as sp

ROOT = Path(__file__).resolve().parent
MODULUS = 2147483647


def fundamental(m: int, limit: int):
    beta = [sp.S(0)] + [
        2 * abs(sp.bernoulli(2 * n)) / sp.factorial(2 * n)
        for n in range(1, limit)
    ]
    a = [sp.S(0)] * (limit + 1)
    d = [sp.S(0)] * (limit + 1)
    r = [[sp.S(0)] * m for _ in range(limit + 1)]
    for n in range(1, m + 1):
        r[n][n - 1] = sp.S(1)
    for n in range(m + 1, limit + 1):
        a[n] = sp.factorial(2 * n) / sp.factorial(2 * n - 2 * m)
        b = sp.factorial(2 * n - 1) / sp.factorial(2 * n - 2 * m - 1)
        d[n] = 2 * (a[n] + b)
        for j in range(m):
            r[n][j] = sum(
                beta[n - u] * (b + a[u]) * r[u][j]
                for u in range(1, n)
            ) / d[n]
    return r, d


def late_matrix(m: int, b: int):
    p, q = 2 * b - 2 * m, 2 * b

    def entry(row, k):
        degree = 2 * (b + row) + 1
        exponent = degree - p - q + 2 * k + 1
        if exponent < 0:
            return sp.S(0)
        total = sp.S(0)
        for upper, lower in ((degree - q + 1, p - 2 * k),
                             (degree - p + 1, q - 2 * k)):
            if 2 <= lower <= upper:
                total += sp.binomial(upper, lower) / upper
        return sp.bernoulli(exponent) * total

    return sp.Matrix(b, b, entry)


def residue(value):
    numerator, denominator = map(int, sp.fraction(value))
    return numerator % MODULUS * pow(denominator % MODULUS, -1, MODULUS) % MODULUS


def main():
    certificate = json.loads((ROOT / "gap_eight_certificate.json").read_text())
    indexed = dict(certificate["residues"])
    assert sorted(indexed) == list(range(5, 8192))
    assert all(value != 0 for value in indexed.values())
    digest = hashlib.sha256(json.dumps(certificate["residues"],
                                     separators=(",", ":")).encode()).hexdigest()
    assert digest == "25b2d4e306dc375015daf2e1682f2a00f2d6a4038679806f20e0a591c44531e3"
    r, d = fundamental(4, 20)
    exact_checks = []
    for b in range(5, 17):
        f = sp.Matrix(r[b + 1:b + 5]).det()
        assert residue(f) == indexed[b]
        mdet = late_matrix(4, b).det()
        bridge = (-1)**(b * (b - 1) // 2) * math.prod(d[5:b + 5]) * f
        bridge /= 4**b * sp.factorial(b)
        assert mdet == bridge
        exact_checks.append({"b": b, "f_sign": int(sp.sign(f)),
                             "f_residue": residue(f), "bridge_verified": True})

    v = sp.Matrix(4, 4, lambda i, j: sp.Rational(1, (j + 1)**(2 * i + 2)))
    permanent = sum(math.prod(v[i, p[i]] for i in range(4))
                    for p in itertools.permutations(range(4)))
    margin = v.det() - permanent * (sp.Rational(129, 128)**4 - 1)
    assert v.det() == sp.Rational(175, 127401984)
    assert permanent == sp.Rational(157183, 4586471424)
    assert margin > 0
    assert sp.Rational(110, 2 * 8192 - 3) < sp.Rational(1, 128)
    assert sp.Rational(2704, (2 * 8192 - 3)**2) < sp.Rational(1, 128)
    assert 39**2 * (16384 + 1) * 4 < (16384 - 6)**2
    assert 117 * 128 < 16384 - 6
    assert 16384**7 <= 2**(16384 - 2)
    e_upper = sum(sp.Rational(3, 4)**n / sp.factorial(n) for n in range(6))
    e_upper += (sp.Rational(3, 4)**6 / sp.factorial(6)
                / (1 - sp.Rational(3, 28)))
    assert e_upper < sp.Rational(17, 8)

    thresholds = []
    for m in range(1, 7):
        v = sp.Matrix(m, m, lambda i, j: sp.Rational(1, (j + 1)**(2 * i + 2)))
        permanent = sum(math.prod(v[i, p[i]] for i in range(m))
                        for p in itertools.permutations(range(m)))
        delta = abs(v.det()) / permanent
        constant = sp.ceiling(4*m + sp.Rational(3*m*(m + 1), 8) + 1)
        error = 8 * constant + 2 * (m - 1)
        threshold = max(2048 * (m + 1)**2, 1 + int(sp.ceiling(2*m*error/delta)))
        thresholds.append({"m": m, "C_m": int(constant), "E_m": int(error),
                           "delta_m": str(delta), "B_m": threshold})

    auxiliary = sp.Matrix(r[5:9]).det()
    initial = sp.Matrix(r[6:10]).det()
    assert late_matrix(4, 5).inv()[0, 4] == 20 * auxiliary / (d[9] * initial)
    output = {"exact_rational_checks": exact_checks,
              "auxiliary_f_4_4": str(auxiliary),
              "initial_leading_cofactor": str(late_matrix(4, 5).inv()[0, 4]),
              "determinant_margin": str(margin),
              "residue_list_sha256": digest,
              "generic_effective_thresholds": thresholds,
              "all_checks_passed": True}
    (ROOT / "gap_eight_bridge_checks.json").write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
