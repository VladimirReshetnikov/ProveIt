#!/usr/bin/env python3
"""Exact and high-precision regression checks for the hypergeometric iPRA packet.

The exact checks use only Python integers and fractions.Fraction.  The
high-precision checks use mpmath when available and are explicitly labelled as
numerical audits, not proofs.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass, asdict
from fractions import Fraction
from pathlib import Path
from typing import Callable, Iterable, Sequence

Q = Fraction


def rise(a: Q, n: int) -> Q:
    out = Q(1)
    for k in range(n):
        out *= a + k
    return out


def hg_coeff(a: Q, b: Q, c: Q, n: int) -> Q:
    den = rise(c, n) * math.factorial(n)
    if den == 0:
        raise ZeroDivisionError(f"singular hypergeometric coefficient at n={n}")
    return rise(a, n) * rise(b, n) / den


def pFq_coeff(as_: Sequence[Q], bs: Sequence[Q], n: int) -> Q:
    num = Q(1)
    den = Q(math.factorial(n))
    for a in as_:
        num *= rise(a, n)
    for b in bs:
        den *= rise(b, n)
    if den == 0:
        raise ZeroDivisionError(f"singular pFq coefficient at n={n}")
    return num / den


def conv(a: Sequence[Q], b: Sequence[Q], N: int | None = None) -> list[Q]:
    if N is None:
        N = len(a) + len(b) - 1
    out = [Q(0) for _ in range(N)]
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            if i + j < N:
                out[i + j] += x * y
    return out


def poly_add(a: Sequence[Q], b: Sequence[Q], N: int | None = None) -> list[Q]:
    if N is None:
        N = max(len(a), len(b))
    return [
        (a[i] if i < len(a) else Q(0)) + (b[i] if i < len(b) else Q(0))
        for i in range(N)
    ]


def poly_scale(a: Sequence[Q], s: Q) -> list[Q]:
    return [s * x for x in a]


def poly_shift(a: Sequence[Q], k: int, N: int | None = None) -> list[Q]:
    if N is None:
        N = len(a) + k
    out = [Q(0)] * N
    for i, x in enumerate(a):
        if i + k < N:
            out[i + k] = x
    return out


def frac_json(x: Q) -> dict[str, int]:
    return {"numerator": x.numerator, "denominator": x.denominator}


@dataclass
class Check:
    name: str
    passed: bool
    detail: str


class Ledger:
    def __init__(self) -> None:
        self.checks: list[Check] = []

    def record(self, name: str, condition: bool, detail: str = "") -> None:
        self.checks.append(Check(name, bool(condition), detail))
        if not condition:
            raise AssertionError(f"{name}: {detail}")


def exact_checks() -> tuple[list[Check], dict[str, object]]:
    L = Ledger()

    # Pochhammer recurrences and splitting.
    params = [Q(-7, 3), Q(-2), Q(0), Q(1, 5), Q(11, 4)]
    for a in params:
        for m in range(7):
            for n in range(7):
                L.record(
                    "pochhammer_split",
                    rise(a, m + n) == rise(a, m) * rise(a + m, n),
                    f"a={a}, m={m}, n={n}",
                )
    for m in range(9):
        for n in range(m + 1, m + 5):
            L.record(
                "negative_integer_termination",
                rise(Q(-m), n) == 0,
                f"m={m}, n={n}",
            )

    # Coefficient ratio, formal derivative, and ODE residual.
    tuples = [
        (Q(1, 3), Q(2, 5), Q(7, 4)),
        (Q(-3, 2), Q(5, 7), Q(11, 6)),
        (Q(4, 3), Q(-2, 5), Q(9, 5)),
    ]
    for a, b, c in tuples:
        for n in range(12):
            An = hg_coeff(a, b, c, n)
            An1 = hg_coeff(a, b, c, n + 1)
            L.record(
                "coefficient_ratio",
                Q(n + 1) * (c + n) * An1 == (a + n) * (b + n) * An,
                f"a={a}, b={b}, c={c}, n={n}",
            )
            shifted = hg_coeff(a + 1, b + 1, c + 1, n)
            L.record(
                "formal_derivative",
                Q(n + 1) * An1 == a * b / c * shifted,
                f"a={a}, b={b}, c={c}, n={n}",
            )
            residual = Q(n + 1) * (c + n) * An1 - (a + n) * (b + n) * An
            L.record("gauss_ode_residual", residual == 0, f"n={n}")

    # Euler and Pfaff transformations coefficientwise.
    for a, b, c in tuples:
        for N in range(11):
            euler_rhs = sum(
                rise(a + b - c, k) / math.factorial(k)
                * hg_coeff(c - a, c - b, c, N - k)
                for k in range(N + 1)
            )
            L.record(
                "euler_transformation_coefficient",
                hg_coeff(a, b, c, N) == euler_rhs,
                f"a={a}, b={b}, c={c}, N={N}",
            )
            pfaff_rhs = sum(
                Q((-1) ** j)
                * hg_coeff(a, c - b, c, j)
                * rise(a + j, N - j)
                / math.factorial(N - j)
                for j in range(N + 1)
            )
            L.record(
                "pfaff_transformation_coefficient",
                hg_coeff(a, b, c, N) == pfaff_rhs,
                f"a={a}, b={b}, c={c}, N={N}",
            )

    # Chu--Vandermonde.
    vandermonde_examples: list[dict[str, object]] = []
    for m in range(10):
        for b, c in [(Q(2, 3), Q(7, 5)), (Q(-3, 4), Q(11, 6)), (Q(5, 2), Q(13, 7))]:
            lhs = sum(hg_coeff(Q(-m), b, c, n) for n in range(m + 1))
            rhs = rise(c - b, m) / rise(c, m)
            L.record("chu_vandermonde", lhs == rhs, f"m={m}, b={b}, c={c}")
            if m in (0, 4, 9) and b == Q(2, 3):
                vandermonde_examples.append({"m": m, "value": frac_json(lhs)})

    # Contiguous relations from the master list.
    for a, b, c in tuples:
        for n in range(1, 11):
            A = hg_coeff(a, b, c, n)
            Ap = hg_coeff(a + 1, b, c, n)
            Bp = hg_coeff(a, b + 1, c, n)
            Cm = hg_coeff(a, b, c - 1, n)
            prev = hg_coeff(a, b, c, n - 1)
            prev_cplus = hg_coeff(a, b, c + 1, n - 1)
            L.record("contiguous_a_plus", Q(n) * A == a * (Ap - A), f"n={n}")
            L.record("contiguous_b_plus", Q(n) * A == b * (Bp - A), f"n={n}")
            L.record("contiguous_c_minus", Q(n) * A == (c - 1) * (Cm - A), f"n={n}")
            Am = hg_coeff(a - 1, b, c, n)
            left = Q(n) * A - Q(n - 1) * prev
            right = (c - a) * Am + (a - c) * A + b * prev
            L.record("contiguous_a_minus", left == right, f"n={n}")
            left_c = c * Q(n) * A - c * Q(n - 1) * prev
            right_c = (c - a) * (c - b) * prev_cplus + c * (a + b - c) * prev
            L.record("contiguous_c_plus", left_c == right_c, f"n={n}")

    # Gauss difference chain used by the finite continued fraction.
    def fj_params(a: Q, b: Q, c: Q, j: int) -> tuple[Q, Q, Q]:
        if j % 2 == 0:
            k = j // 2
            return a + k, b + k, c + 2 * k
        k = (j - 1) // 2
        return a + k + 1, b + k, c + 2 * k + 1

    def alpha(a: Q, b: Q, c: Q, j: int) -> Q:
        if j % 2 == 1:
            k = (j - 1) // 2
            return (a - c - k) * (b + k) / ((c + 2 * k) * (c + 2 * k + 1))
        k = (j - 2) // 2
        return (b - c - k - 1) * (a + k + 1) / ((c + 2 * k + 1) * (c + 2 * k + 2))

    a, b, c = Q(2, 7), Q(3, 8), Q(11, 6)
    for j in range(1, 10):
        p0 = fj_params(a, b, c, j - 1)
        p1 = fj_params(a, b, c, j)
        p2 = fj_params(a, b, c, j + 1)
        al = alpha(a, b, c, j)
        for n in range(9):
            lhs = hg_coeff(*p0, n) - hg_coeff(*p1, n)
            rhs = Q(0) if n == 0 else al * hg_coeff(*p2, n - 1)
            L.record("gauss_difference_chain", lhs == rhs, f"j={j}, n={n}")

    # Cubic radical/Fuss--Catalan coefficients and the cubic equation.
    cubic_coeffs: list[Q] = []
    N = 14
    for n in range(N):
        hyper = hg_coeff(Q(1, 3), Q(2, 3), Q(3, 2), n) * Q(-27, 4) ** n
        fuss = Q((-1) ** n * math.comb(3 * n, n), 2 * n + 1)
        L.record("cubic_fuss_coefficient", hyper == fuss, f"n={n}")
        cubic_coeffs.append(hyper)
    cube = conv(conv(cubic_coeffs, cubic_coeffs, N), cubic_coeffs, N)
    residual = cubic_coeffs[:]
    residual[0] -= 1
    shifted_cube = poly_shift(cube, 1, N)
    residual = poly_add(residual, shifted_cube, N)
    L.record("cubic_equation_truncated", all(x == 0 for x in residual), repr(residual))

    # General Glasser/Fuss--Catalan coefficient identity.
    glasser_examples: list[dict[str, object]] = []
    for k in range(2, 7):
        numer = [Q(j, k + 1) for j in range(1, k + 1)]
        denom = [Q(j, k) for j in range(2, k)] + [Q(k + 1, k)]
        fk_pow_k = Q(k**k, (k + 1) ** (k + 1))
        for n in range(8):
            lhs = pFq_coeff(numer, denom, n)
            rhs = Q(math.comb((k + 1) * n, n), k * n + 1) * fk_pow_k**n
            L.record("glasser_coefficient", lhs == rhs, f"k={k}, n={n}")
        glasser_examples.append({"k": k, "coefficient_n_5": frac_json(pFq_coeff(numer, denom, 5))})

    # Legendre polynomial specialization, compared with the three-term recurrence.
    def poly_mul_x(p: Sequence[Q]) -> list[Q]:
        return [Q(0)] + list(p)

    def legendre_poly(n: int) -> list[Q]:
        if n == 0:
            return [Q(1)]
        if n == 1:
            return [Q(0), Q(1)]
        p0, p1 = [Q(1)], [Q(0), Q(1)]
        for m in range(1, n):
            xpart = poly_scale(poly_mul_x(p1), Q(2 * m + 1))
            p0pad = list(p0) + [Q(0)] * (len(xpart) - len(p0))
            num = poly_add(xpart, poly_scale(p0pad, Q(-m)), len(xpart))
            p2 = poly_scale(num, Q(1, m + 1))
            p0, p1 = p1, p2
        return p1

    for n in range(9):
        hyp = [Q(0)] * (n + 1)
        for m in range(n + 1):
            A = hg_coeff(Q(-n), Q(n + 1), Q(1), m)
            for j in range(m + 1):
                hyp[j] += A * Q(math.comb(m, j) * ((-1) ** j), 2**m)
        leg = legendre_poly(n)
        leg += [Q(0)] * (n + 1 - len(leg))
        L.record("legendre_hypergeometric", hyp == leg, f"n={n}, hyp={hyp}, leg={leg}")

    summary = {
        "exact_check_count": len(L.checks),
        "vandermonde_examples": vandermonde_examples,
        "cubic_coefficients_first_10": [frac_json(x) for x in cubic_coeffs[:10]],
        "glasser_examples": glasser_examples,
    }
    return L.checks, summary


def numerical_audit(dps: int) -> dict[str, object]:
    try:
        import mpmath as mp
    except ImportError:
        return {"available": False, "reason": "mpmath is not installed"}

    mp.mp.dps = dps
    cases: list[tuple[str, object, object]] = [
        (
            "MW18",
            mp.hyp2f1(mp.mpf(1) / 3, mp.mpf(2) / 3, mp.mpf(5) / 6, mp.mpf(27) / 32),
            mp.mpf(8) / 5,
        ),
        (
            "MW19",
            mp.hyp2f1(mp.mpf(1) / 4, mp.mpf(1) / 2, mp.mpf(3) / 4, mp.mpf(80) / 81),
            mp.mpf(9) / 5,
        ),
        (
            "MW20",
            mp.hyp2f1(mp.mpf(1) / 8, mp.mpf(3) / 8, mp.mpf(1) / 2, mp.mpf(2400) / 2401),
            mp.mpf(2) * mp.sqrt(7) / 3,
        ),
        (
            "MW21",
            mp.hyp2f1(mp.mpf(1) / 6, mp.mpf(1) / 3, mp.mpf(1) / 2, mp.mpf(25) / 27),
            mp.mpf(3) * mp.sqrt(3) / 4,
        ),
        (
            "MW22",
            mp.hyp2f1(mp.mpf(1) / 6, mp.mpf(1) / 2, mp.mpf(2) / 3, mp.mpf(125) / 128),
            mp.mpf(4) / 3 * mp.power(2, mp.mpf(1) / 6),
        ),
        (
            "MW23",
            mp.hyp2f1(mp.mpf(1) / 12, mp.mpf(5) / 12, mp.mpf(1) / 2, mp.mpf(1323) / 1331),
            mp.mpf(3) / 4 * mp.power(11, mp.mpf(1) / 4),
        ),
    ]
    mw24_target = (
        mp.power(2, mp.mpf(1) / 6)
        * mp.power(15, mp.mpf(1) / 4)
        / (4 * mp.sqrt(mp.pi))
        * mp.gamma(mp.mpf(1) / 3) ** 3
        / mp.gamma(mp.mpf(1) / 4) ** 2
        * (1 + mp.sqrt(3))
    )
    cases.append(
        (
            "MW24",
            mp.hyp2f1(mp.mpf(1) / 12, mp.mpf(5) / 12, mp.mpf(1) / 2, mp.mpf(121) / 125),
            mw24_target,
        )
    )

    rows = []
    threshold = mp.power(10, -(dps - 20))
    for name, lhs, rhs in cases:
        err = abs(lhs - rhs)
        rows.append(
            {
                "name": name,
                "lhs": mp.nstr(lhs, dps),
                "rhs": mp.nstr(rhs, dps),
                "absolute_error": mp.nstr(err, 12),
                "passes_threshold": bool(err < threshold),
            }
        )

    # Additional analytic formulas used in the report.
    a = mp.mpf(7) / 13
    b = mp.mpf(4) / 9
    c = mp.mpf(17) / 11
    z = mp.mpf(2) / 7
    euler_lhs = mp.hyp2f1(a, b, c, z)
    euler_rhs = (1 - z) ** (c - a - b) * mp.hyp2f1(c - a, c - b, c, z)
    rows.append(
        {
            "name": "Euler transformation sample",
            "lhs": mp.nstr(euler_lhs, dps),
            "rhs": mp.nstr(euler_rhs, dps),
            "absolute_error": mp.nstr(abs(euler_lhs - euler_rhs), 12),
            "passes_threshold": bool(abs(euler_lhs - euler_rhs) < threshold),
        }
    )

    return {
        "available": True,
        "decimal_digits": dps,
        "threshold": mp.nstr(threshold, 8),
        "rows": rows,
        "all_passed": all(row["passes_threshold"] for row in rows),
        "warning": "High-precision agreement is a regression check, not a proof.",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path("evidence/validation.json"))
    parser.add_argument("--dps", type=int, default=100)
    args = parser.parse_args()

    checks, summary = exact_checks()
    payload = {
        "schema_version": 1,
        "exact": {
            "all_passed": all(c.passed for c in checks),
            "summary": summary,
            "checks_by_name": {},
        },
        "numerical_audit": numerical_audit(args.dps),
    }
    grouped: dict[str, dict[str, object]] = {}
    for c in checks:
        row = grouped.setdefault(c.name, {"count": 0, "all_passed": True, "examples": []})
        row["count"] = int(row["count"]) + 1
        row["all_passed"] = bool(row["all_passed"]) and c.passed
        if len(row["examples"]) < 3:
            row["examples"].append(c.detail)
    payload["exact"]["checks_by_name"] = grouped

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"wrote {args.output}")
    print(f"exact checks: {summary['exact_check_count']} (all passed)")
    print(f"numerical audit available: {payload['numerical_audit']['available']}")
    if payload["numerical_audit"].get("available"):
        print(f"numerical audit all passed: {payload['numerical_audit']['all_passed']}")


if __name__ == "__main__":
    main()
