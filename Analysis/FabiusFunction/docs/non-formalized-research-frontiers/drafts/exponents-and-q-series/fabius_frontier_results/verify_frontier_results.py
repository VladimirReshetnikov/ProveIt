#!/usr/bin/env python3
"""Reproduce and verify the symbolic and numerical claims in the report.

The script studies

    P_b(x) = product_{nu>=1} sinc(x / b**nu),  sinc(z)=sin(z)/z,

its n-factor truncation P_{b,n}, and the q-Richardson extrapolants

    R_{m,n} = sum_{j=0}^m w_j^(m) P_{b,n+j},  q=b**(-2).

It uses high-precision mpmath arithmetic. SymPy is used for exact rational
identities involving Bernoulli/Bell coefficients, q-Pochhammer symbols, and
Gaussian binomial coefficients. No network access is required.
"""

from __future__ import annotations

import csv
from pathlib import Path

import mpmath as mp
import sympy as sp


mp.mp.dps = 90
OUTDIR = Path(__file__).resolve().parent
ONE = mp.mpf(1)


def sinc(x: mp.mpf) -> mp.mpf:
    """Analytic sinc, including the removable value at zero."""
    return ONE if x == 0 else mp.sin(x) / x


def finite_product(x: mp.mpf, b: mp.mpf, n: int) -> mp.mpf:
    """Return P_{b,n}(x)."""
    value = ONE
    for nu in range(1, n + 1):
        value *= sinc(x / b**nu)
    return value


def infinite_product(x: mp.mpf, b: mp.mpf, tol: mp.mpf | None = None) -> mp.mpf:
    """Evaluate P_b(x), stopping from a geometric log-tail estimate."""
    if tol is None:
        tol = mp.mpf(10) ** (-(mp.mp.dps - 20))
    value = ONE
    nu = 1
    while True:
        y = x / b**nu
        value *= sinc(y)
        # Since -log(sinc y) ~ y^2/6, the omitted geometric y^2-sum
        # is an inexpensive conservative scale for stopping.
        tail_scale = (x * x) / (6 * b ** (2 * (nu + 1)) * (1 - b**-2))
        if tail_scale < tol:
            return value
        nu += 1
        if nu > 100000:
            raise RuntimeError("infinite_product did not converge")


def q_pochhammer(q: mp.mpf, n: int) -> mp.mpf:
    value = ONE
    for r in range(1, n + 1):
        value *= 1 - q**r
    return value


def richardson_weights(q: mp.mpf, m: int) -> list[mp.mpf]:
    """Lagrange weights at nodes 1,q,...,q^m, evaluated at zero."""
    result: list[mp.mpf] = []
    for j in range(m + 1):
        exponent = (m - j) * (m - j + 1) // 2
        numerator = (-1) ** (m - j) * q**exponent
        denominator = q_pochhammer(q, j) * q_pochhammer(q, m - j)
        result.append(numerator / denominator)
    return result


def extrapolated_product(x: mp.mpf, b: mp.mpf, n: int, m: int) -> mp.mpf:
    """Evaluate R_{m,n} from its explicit weights."""
    q = b**-2
    weights = richardson_weights(q, m)
    return mp.fsum(weights[j] * finite_product(x, b, n + j) for j in range(m + 1))


def extrapolated_product_table(x: mp.mpf, b: mp.mpf, n: int, m: int) -> mp.mpf:
    """Evaluate R_{m,n} by the triangular q-Richardson recursion."""
    q = b**-2
    row = [finite_product(x, b, n + j) for j in range(m + 1)]
    for k in range(1, m + 1):
        row = [
            (row[j + 1] - q**k * row[j]) / (1 - q**k)
            for j in range(len(row) - 1)
        ]
    return row[0]


def exact_symbolic_data(max_order: int = 7) -> tuple[list[sp.Expr], list[sp.Expr]]:
    """Return exact c_k and alpha_r for b=2."""
    c: list[sp.Expr] = [sp.Integer(0)]
    for k in range(1, max_order + 1):
        c.append(
            sp.simplify(sp.zeta(2 * k) / (k * sp.pi ** (2 * k) * (4**k - 1)))
        )
    alpha: list[sp.Expr] = [sp.Integer(1)]
    for r in range(1, max_order + 1):
        ar = sp.simplify(
            sum(k * c[k] * alpha[r - k] for k in range(1, r + 1)) / r
        )
        alpha.append(sp.factor(ar))
    return c, alpha


def exact_weights_b2(max_m: int = 5) -> list[list[sp.Expr]]:
    q = sp.Rational(1, 4)
    rows: list[list[sp.Expr]] = []
    for m in range(max_m + 1):
        row: list[sp.Expr] = []
        for j in range(m + 1):
            exponent = (m - j) * (m - j + 1) // 2
            qpj = sp.prod(1 - q**r for r in range(1, j + 1))
            qpmj = sp.prod(1 - q**r for r in range(1, m - j + 1))
            row.append(sp.factor((-1) ** (m - j) * q**exponent / (qpj * qpmj)))
        rows.append(row)
    return rows


def q_binomial(n: int, k: int, q: sp.Expr) -> sp.Expr:
    if not 0 <= k <= n:
        return sp.Integer(0)
    num = sp.prod(1 - q**r for r in range(1, n + 1))
    den = sp.prod(1 - q**r for r in range(1, k + 1)) * sp.prod(
        1 - q**r for r in range(1, n - k + 1)
    )
    return sp.factor(num / den)


def verify_symbolic_identities() -> None:
    """Assert normalization, cancellations, and the q-binomial moment formula."""
    q = sp.symbols("q", positive=True)
    for m in range(0, 7):
        weights: list[sp.Expr] = []
        for j in range(m + 1):
            qpj = sp.prod(1 - q**r for r in range(1, j + 1))
            qpmj = sp.prod(1 - q**r for r in range(1, m - j + 1))
            exponent = (m - j) * (m - j + 1) // 2
            weights.append(
                sp.factor((-1) ** (m - j) * q**exponent / (qpj * qpmj))
            )
        assert sp.simplify(sum(weights) - 1) == 0
        for r in range(1, m + 1):
            assert (
                sp.simplify(sum(weights[j] * q ** (j * r) for j in range(m + 1)))
                == 0
            )
        for r in range(m + 1, m + 6):
            lhs = sp.factor(sum(weights[j] * q ** (j * r) for j in range(m + 1)))
            rhs = sp.factor(
                (-1) ** m
                * q ** (m * (m + 1) // 2)
                * q_binomial(r - 1, m, q)
            )
            assert sp.simplify(lhs - rhs) == 0


def write_numerical_csv() -> None:
    b = mp.mpf(2)
    rows: list[dict[str, str | int]] = []
    for x in (mp.mpf(1), mp.mpf(3), mp.mpf(10)):
        truth = infinite_product(x, b)
        for n in range(3, 8):
            for m in range(0, 4):
                estimate = extrapolated_product(x, b, n, m)
                estimate_table = extrapolated_product_table(x, b, n, m)
                assert mp.almosteq(estimate, estimate_table)
                rows.append(
                    {
                        "x": mp.nstr(x, 8),
                        "n": n,
                        "m": m,
                        "estimate": mp.nstr(estimate, 35),
                        "absolute_error": mp.nstr(abs(estimate - truth), 20),
                    }
                )
    path = OUTDIR / "numerical_results.csv"
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def report() -> str:
    verify_symbolic_identities()
    c, alpha = exact_symbolic_data(7)
    weights = exact_weights_b2(5)
    lines: list[str] = []
    lines.append("Exact Bernoulli cumulants c_k for b=2:")
    for k in range(1, 8):
        lines.append(f"  c_{k} = {c[k]}")
    lines.append("\nExact Bell coefficients alpha_r for b=2:")
    for r in range(0, 8):
        lines.append(f"  alpha_{r} = {alpha[r]}")
    lines.append("\nExact q-Richardson weights for q=1/4:")
    for m, row in enumerate(weights):
        lines.append(f"  m={m}: {row}")

    qnum = mp.mpf(1) / 4
    lines.append("\nLebesgue/stability constants:")
    for m in range(1, 9):
        lam = mp.nprod(lambda r: (1 + qnum**r) / (1 - qnum**r), [1, m])
        lines.append(f"  Lambda_{m} = {mp.nstr(lam, 30)}")
    lam_inf = mp.nprod(lambda r: (1 + qnum**r) / (1 - qnum**r), [1, mp.inf])
    lines.append(f"  Lambda_infinity = {mp.nstr(lam_inf, 50)}")

    b = mp.mpf(2)
    for x in (mp.mpf(1), mp.mpf(3), mp.mpf(10)):
        truth = infinite_product(x, b)
        lines.append(f"\nP_2({x}) = {mp.nstr(truth, 45)}")
        lines.append("  n      m=0 error          m=1 error          m=2 error          m=3 error")
        for n in range(3, 7):
            errs = [abs(extrapolated_product(x, b, n, m) - truth) for m in range(4)]
            lines.append(
                f"  {n:<2d}  " + "  ".join(f"{mp.nstr(err, 12):>16}" for err in errs)
            )

    x = mp.mpf(3)
    truth = infinite_product(x, b)
    lines.append("\nScaled leading-error checks at x=3:")
    for m in range(4):
        r = m + 1
        predicted = (
            (-1) ** m
            * qnum ** (m * (m + 1) // 2)
            * mp.mpf(str(sp.N(alpha[r], 90)))
            * x ** (2 * r)
            * truth
        )
        lines.append(f"  m={m}, predicted constant = {mp.nstr(predicted, 35)}")
        for n in (7, 9, 11):
            error = extrapolated_product(x, b, n, m) - truth
            scaled = error / qnum ** (r * n)
            lines.append(f"      n={n}: scaled error = {mp.nstr(scaled, 35)}")

    lines.append("\nA-posteriori certificate checks:")
    for x in (mp.mpf(1), mp.mpf(3), mp.mpf(10)):
        truth = infinite_product(x, b)
        for m in range(4):
            n = 4
            rn = extrapolated_product(x, b, n, m)
            rnp1 = extrapolated_product(x, b, n + 1, m)
            error = abs(rn - truth)
            lower = abs(rnp1 - rn)
            upper = lower / (1 - qnum ** (m + 1))
            assert lower <= error * (1 + mp.mpf("1e-70"))
            assert error <= upper * (1 + mp.mpf("1e-70"))
            lines.append(
                f"  x={x}, m={m}: difference={mp.nstr(lower, 12)}, "
                f"error={mp.nstr(error, 12)}, upper={mp.nstr(upper, 12)}"
            )
    return "\n".join(lines) + "\n"


def main() -> None:
    text = report()
    (OUTDIR / "numerical_results.txt").write_text(text, encoding="utf-8")
    write_numerical_csv()
    print(text)
    print("Wrote numerical_results.txt and numerical_results.csv")


if __name__ == "__main__":
    main()
