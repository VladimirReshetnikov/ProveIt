"""Exact and numerical checks for the adjacent-even-tail prefix theorem.

This script is an auxiliary research verifier, not the arbitrary-order proof.
The proof is in adjacent_tail_prefix.tex.  All numeric results are diagnostics,
not rigorous interval enclosures.  Source archives are never modified.
"""
from __future__ import annotations

import argparse
import json
from functools import reduce
from math import gcd
from pathlib import Path

import sympy as sp


def coefficient(p: int, q: int, j: int, k: int):
    """Source matrix, using the original Bernoulli/binomial formula."""
    d = 2 * j + 1
    e = d - p - q + 2 * k + 1
    if e < 0:
        return sp.S.Zero
    ans = sp.S.Zero
    for upper, lower in ((d - q + 1, p - 2 * k),
                         (d - p + 1, q - 2 * k)):
        if 2 <= lower <= upper:
            ans += sp.binomial(upper, lower) / upper
    return sp.bernoulli(e) * ans


def matrix(b: int):
    return sp.Matrix(b, b,
                     lambda r, k: coefficient(2 * b - 2, 2 * b, b + r, k))


def coth_coefficient(k: int):
    return 2 * sp.bernoulli(2 * k) / sp.factorial(2 * k)


def bracket(n: int, r: int):
    return 2 * r * (2 * r - 1) + (2 * n - 1) * (2 * n - 2) - 2 * (r == 1)


def formal_solution(count: int):
    q = {1: sp.S.One}
    for n in range(2, count + 1):
        q[n] = -sum(coth_coefficient(n - r) * bracket(n, r) * q[r]
                    for r in range(1, n)) / (4 * (2 * n - 1) ** 2)
    return q


def operator_matrix(b: int):
    """Independently extract the coth differential-operator coefficients."""
    return sp.Matrix(b, b,
        lambda row, col: (coth_coefficient(row + 1 - col)
                          * bracket(row + 2, col + 1))
        if col <= row + 1 else sp.S.Zero)


def inverse_bernoulli(j: int, r: int):
    return (sp.binomial(2 * j + 1, 2 * r)
            / sp.Integer(2) ** (2 * (j - r))) if r <= j else sp.S.Zero


def primitive_integer_row(b: int, k: int):
    inv = matrix(b).inv()
    w = [sum(inv[k, t] * inverse_bernoulli(b + t, r) for t in range(b))
         for r in range(2 * b)]
    multiplier = sp.ilcm(*[x.q for x in w])
    v = [int(multiplier * x) for x in w]
    common = reduce(gcd, [abs(x) for x in v])
    v = [x // common for x in v]
    multiplier = sp.Rational(multiplier, common)
    if v[0] < 0:
        v = [-x for x in v]
        multiplier = -multiplier
    return v, multiplier


def alpha(p: int, h: int):
    if h == 0:
        return sp.Rational(1, p - 1)
    return (sp.bernoulli(2 * h, sp.Rational(1, 2))
            * sp.rf(p, 2 * h - 1) / sp.factorial(2 * h))


def product_alpha(p: int, q: int, h: int):
    return sum(alpha(p, j) * alpha(q, h - j) for j in range(h + 1))


def zsymbol(s: int):
    if s == 0:
        return -sp.Rational(1, 2)
    return sp.Symbol(f"zeta_{s}")


def block_U(p: int, q: int, d: int):
    if d < q:
        return sp.Symbol(f"double_zeta_{p}_{q-d}") + zsymbol(p + q - d) / 2
    return sum(sp.binomial(d - q + 1, 2 * h) * sp.bernoulli(d - q + 1 - 2 * h)
               * zsymbol(p - 2 * h) / (d - q + 1)
               for h in range(1, min((d - q + 1) // 2, p // 2 - 1) + 1))


def source_block(p: int, q: int, j: int):
    """Independent U/R source construction, retaining formal zeta labels."""
    d = 2 * j + 1
    ans = block_U(p, q, d) + block_U(q, p, d)
    if d >= p + q - 1:
        ans -= sp.bernoulli(d - p - q + 1) / 2 * (
            sp.binomial(d - q, p - 1) / p + sp.binomial(d - p, q - 1) / q)
    return sp.expand(ans)


def source_moment(p: int, q: int, r: int):
    return sp.expand(sum(sp.binomial(2 * r, 2 * j) * sp.bernoulli(2 * r - 2 * j,
                          sp.Rational(1, 2)) / (2 * j + 1)
                         * source_block(p, q, j) for j in range(r + 1)))


def exact_checks():
    q = formal_solution(40)
    checks = 0
    assert q[2] == -sp.Rational(1, 36)
    assert q[3] == sp.Rational(11, 5400)
    assert q[4] == -sp.Rational(113, 705600)
    checks += 3
    for n, value in q.items():
        assert (-1) ** (n - 1) * value > 0
        checks += 1
    # Independent finite hypergeometric formula and change of variable.
    f = [sp.factorial(n) ** 2 / sp.rf(sp.Rational(3, 2), n) ** 2
         * sum(sp.rf(sp.Rational(1, 2), k) ** 2 / sp.factorial(k) ** 2
               for k in range(n + 1)) for n in range(16)]
    for n in range(1, len(f)):
        assert (n + sp.Rational(1, 2)) ** 2 * f[n] - n ** 2 * f[n - 1] == sp.Rational(1, 4)
        checks += 1
    t = sp.Symbol("t")
    z = sp.tanh(t / 2).series(t, 0, 16).removeO()
    composed = sp.series(4 * sum(f[n] * z ** (2 * n + 2) for n in range(7)), t, 0, 16).removeO()
    assert sp.expand(composed) == sum(q[n] * t ** (2 * n) for n in range(1, 8))
    checks += 1
    determinants = []
    for b in range(2, 17):
        A, K = matrix(b), operator_matrix(b)
        scaled = sp.diag(*[sp.Rational(2, sp.factorial(2 * r + 1)) for r in range(b)])
        scaled = scaled * A[:, ::-1] * sp.diag(*[sp.factorial(2 * n) for n in range(1, b + 1)])
        assert scaled == K
        c = (-1) ** b * q[b + 1]
        predicted = ((-1) ** (b * (b - 1) // 2)
                     * sp.factorial2(2 * b + 1) ** 2 * c / sp.factorial(b))
        actual = A.det()
        assert actual == predicted
        assert K.det() == 4 ** b * sp.factorial2(2 * b + 1) ** 2 * c
        checks += 3
        determinants.append({"p": 2 * b - 2, "q": 2 * b, "determinant": str(actual),
                             "complete_moment_determinant": str(actual / sp.factorial2(4 * b - 1))})
    examples = []
    for b in (3, 4):
        p, outer_q = 2 * b - 2, 2 * b
        moments = [source_moment(p, outer_q, r) for r in range(2 * b)]
        rows = []
        for k in range(b):
            polynomial, multiplier = primitive_integer_row(b, k)
            reduced = sp.expand(sum(a * d for a, d in zip(polynomial, moments)))
            assert reduced == multiplier * zsymbol(2 * k)
            a0, a1 = product_alpha(p, outer_q, 0), product_alpha(p, outer_q, 1)
            assert a0 == sp.Rational(1, (p - 1) * (outer_q - 1))
            assert a1 == -sp.Rational(p, 24 * (outer_q - 1)) - sp.Rational(outer_q, 24 * (p - 1))
            rows.append({"zeta_order": 2 * k, "polynomial_even_coefficients": polynomial,
                         "zeta_multiplier": str(multiplier),
                         "subtraction_x2": str(polynomial[-1] * a0),
                         "subtraction_constant": str(polynomial[-2] * a0 + polynomial[-1] * a1),
                         "right_side": str(reduced)})
            checks += 3
        examples.append({"p": p, "q": outer_q, "matrix": [[str(x) for x in row] for row in matrix(b).tolist()],
                         "inverse": [[str(x) for x in row] for row in matrix(b).inv().tolist()], "rows": rows})
    # Two targeted convention errors produce different exact results.
    K = operator_matrix(3)
    wrong = K.copy()
    for row in range(3):
        wrong[row, 0] += 2 * coth_coefficient(row + 1)
    assert wrong.det() != K.det()  # dropping Q''(0) h is not harmless
    assert matrix(3).det() != abs(matrix(3).det())  # reversal orientation is required
    checks += 2
    return {"status": "passed", "exact_assertions": checks,
            "positive_coefficients": {str(n): str((-1) ** (n - 1) * v) for n, v in q.items()},
            "determinants": determinants, "examples": examples,
            "negative_controls": ["missing constant subtraction", "lost column-reversal sign"]}


def numeric_checks(exact):
    import mpmath as mp
    mp.mp.dps = 110
    records = []
    for example in exact["examples"]:
        p, q = example["p"], example["q"]
        # One rational and one nonrational specialization for each order pair.
        for row in example["rows"][:2]:
            coeff = row["polynomial_even_coefficients"]
            s2 = mp.mpf(str(sp.Rational(row["subtraction_x2"]).p)) / int(sp.Rational(row["subtraction_x2"]).q)
            s0 = mp.mpf(str(sp.Rational(row["subtraction_constant"]).p)) / int(sp.Rational(row["subtraction_constant"]).q)
            multiplier = sp.Rational(row["zeta_multiplier"])
            target = mp.mpf(int(multiplier.p)) / int(multiplier.q) * mp.zeta(row["zeta_order"])
            for N in (80, 160):
                partial = mp.mpf(0)
                for n in range(N):
                    x = mp.mpf(n) + mp.mpf('0.5')
                    poly = sum(mp.mpf(c) * x ** (2 * r) for r, c in enumerate(coeff))
                    partial += poly * mp.zeta(p, n + 1) * mp.zeta(q, n + 1) - s2 * x * x - s0
                # Independent centered Hurwitz asymptotic tail; not a certificate.
                tail = mp.mpf(0)
                for h in range(0, 35):
                    ah = product_alpha(p, q, h)
                    am = mp.mpf(int(ah.p)) / int(ah.q)
                    for r, c in enumerate(coeff):
                        exponent = 2 * r + 2 - p - q - 2 * h
                        if exponent < 0:
                            tail += c * am * mp.zeta(-exponent, mp.mpf(N) + mp.mpf('0.5'))
                value = partial + tail
                residual = abs(value - target) / max(1, abs(target))
                assert residual < mp.mpf('1e-70')
                records.append({"p": p, "q": q, "zeta_order": row["zeta_order"],
                                "cutoff": N, "working_dps": mp.mp.dps,
                                "asymptotic_product_orders": 35,
                                "value": mp.nstr(value, 80), "target": mp.nstr(target, 80),
                                "scaled_residual": mp.nstr(residual, 12)})
    return {"status": "passed", "diagnostics": records,
            "qualification": "Floating-point tail-accelerated diagnostics; no interval enclosure."}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--numeric", action="store_true")
    args = parser.parse_args()
    result = exact_checks()
    if args.numeric:
        result["numerical"] = numeric_checks(result)
    destination = Path(__file__).resolve().parents[1] / "verification/adjacent_tail_prefix.json"
    destination.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"output": str(destination), "status": result["status"],
                      "exact_assertions": result["exact_assertions"],
                      "numeric_diagnostics": len(result.get("numerical", {}).get("diagnostics", []))}))


if __name__ == "__main__":
    main()
