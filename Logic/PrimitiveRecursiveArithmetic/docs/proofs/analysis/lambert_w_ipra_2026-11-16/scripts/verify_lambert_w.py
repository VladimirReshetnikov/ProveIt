#!/usr/bin/env python3
"""Exact and high-precision checks for the constructive Lambert W report.

The exact layer uses only finite arrays of rational coefficients.  The
high-precision layer records representative residuals and inequality margins.
This evidence supports, but does not replace, the human proofs in the paper.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from dataclasses import asdict, dataclass
from fractions import Fraction
from pathlib import Path

import mpmath as mp


@dataclass
class Check:
    name: str
    kind: str
    passed: bool
    detail: str
    metric: float | None = None


CHECKS: list[Check] = []


def record(name: str, kind: str, passed: bool, detail: str, metric: float | None = None) -> None:
    c = Check(name, kind, bool(passed), detail, metric)
    CHECKS.append(c)
    if not c.passed:
        raise AssertionError(f"{name}: {detail}")


# ---------------------------------------------------------------------------
# Exact finite-series algebra over Q
# ---------------------------------------------------------------------------

def zero_series(n: int) -> list[Fraction]:
    return [Fraction(0) for _ in range(n + 1)]


def add(a: list[Fraction], b: list[Fraction], n: int) -> list[Fraction]:
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n + 1)]


def sub(a: list[Fraction], b: list[Fraction], n: int) -> list[Fraction]:
    return [(a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0) for i in range(n + 1)]


def scale(a: list[Fraction], c: Fraction, n: int) -> list[Fraction]:
    return [(a[i] if i < len(a) else 0) * c for i in range(n + 1)]


def mul(a: list[Fraction], b: list[Fraction], n: int) -> list[Fraction]:
    out = zero_series(n)
    for i in range(min(len(a), n + 1)):
        if a[i] == 0:
            continue
        for j in range(min(len(b), n - i + 1)):
            if b[j] != 0:
                out[i + j] += a[i] * b[j]
    return out


def inv(a: list[Fraction], n: int) -> list[Fraction]:
    if not a or a[0] == 0:
        raise ZeroDivisionError("series constant coefficient is zero")
    out = zero_series(n)
    out[0] = 1 / a[0]
    for k in range(1, n + 1):
        out[k] = -sum((a[j] if j < len(a) else 0) * out[k - j] for j in range(1, k + 1)) / a[0]
    return out


def pow_series(a: list[Fraction], exponent: int, n: int) -> list[Fraction]:
    if exponent < 0:
        return pow_series(inv(a, n), -exponent, n)
    result = zero_series(n)
    result[0] = 1
    base = a[:n + 1] + [Fraction(0)] * max(0, n + 1 - len(a))
    e = exponent
    while e:
        if e & 1:
            result = mul(result, base, n)
        base = mul(base, base, n)
        e >>= 1
    return result


def exp_series(a: list[Fraction], n: int) -> list[Fraction]:
    """exp(a), requiring a[0]=0, via n e_n = sum k a_k e_{n-k}."""
    if a[0] != 0:
        raise ValueError("exp_series currently expects zero constant term")
    out = zero_series(n)
    out[0] = 1
    for m in range(1, n + 1):
        out[m] = sum(Fraction(k) * (a[k] if k < len(a) else 0) * out[m - k]
                     for k in range(1, m + 1)) / m
    return out


def derivative_poly(a: list[Fraction]) -> list[Fraction]:
    if len(a) <= 1:
        return [Fraction(0)]
    return [Fraction(i) * a[i] for i in range(1, len(a))]


def poly_mul(a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
    out = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] += ai * bj
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def poly_add(a: list[Fraction], b: list[Fraction]) -> list[Fraction]:
    out = [Fraction(0)] * max(len(a), len(b))
    for i in range(len(out)):
        out[i] = (a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def frac_pow(base: int, exponent: int) -> Fraction:
    if exponent >= 0:
        return Fraction(base**exponent)
    return Fraction(1, base**(-exponent))


def assert_series_zero(name: str, a: list[Fraction], detail: str) -> None:
    nz = [(i, c) for i, c in enumerate(a) if c]
    record(name, "exact", not nz, f"{detail}; nonzero={nz[:4]}")


def assert_poly_equal(name: str, a: list[Fraction], b: list[Fraction], detail: str = "polynomial identity") -> None:
    n = max(len(a), len(b))
    aa = a + [Fraction(0)] * (n - len(a))
    bb = b + [Fraction(0)] * (n - len(b))
    record(name, "exact", aa == bb, f"{detail}; lhs={aa}, rhs={bb}")


def unsigned_stirling_first(n: int, k: int) -> int:
    table = [[0] * (n + 1) for _ in range(n + 1)]
    table[0][0] = 1
    for i in range(n):
        for j in range(i + 1):
            table[i + 1][j] += i * table[i][j]
            table[i + 1][j + 1] += table[i][j]
    return table[n][k] if 0 <= k <= n else 0


def symbolic_checks() -> None:
    N = 18
    x = zero_series(N)
    x[1] = 1
    Wfull = zero_series(N + 1)
    for n in range(1, N + 2):
        Wfull[n] = Fraction((-n) ** (n - 1), math.factorial(n))
    W = Wfull[:N + 1]

    # W exp W = x and T = x exp T.
    residual = sub(mul(W, exp_series(W, N), N), x, N)
    assert_series_zero("maclaurin_defining_equation_through_18", residual,
                       "W_N exp(W_N)=x mod x^19")
    T = [W[i] * ((-1) ** (i + 1)) for i in range(N + 1)]  # -W(-x)
    assert_series_zero("rooted_tree_functional_equation_through_18",
                       sub(T, mul(x, exp_series(T, N), N), N),
                       "T_N=x exp(T_N) mod x^19")

    # Integral powers W^r.
    for r in range(1, 7):
        predicted = zero_series(N)
        for n in range(r, N + 1):
            predicted[n] = Fraction(-r, math.factorial(n - r)) * frac_pow(-n, n - r - 1)
        assert_series_zero(f"integral_power_formula_r_{r}",
                           sub(pow_series(W, r, N), predicted, N),
                           f"formula (8.5) through degree {N}")

    # (W/x)^r.  Q has constant term 1 and Q_n=W_{n+1}.
    Q = [Wfull[i + 1] for i in range(N + 1)]
    for r in (-4, -3, -2, -1, 1, 2, 3, 4, 5):
        predicted = zero_series(N)
        predicted[0] = 1
        for n in range(1, N + 1):
            predicted[n] = Fraction(r * (n + r) ** (n - 1) * ((-1) ** n), math.factorial(n))
        assert_series_zero(f"ratio_power_formula_r_{r}",
                           sub(pow_series(Q, r, N), predicted, N),
                           f"formula (8.6) through degree {N}")

    # Higher derivative polynomial recurrence and independently expanded numerator.
    P: dict[int, list[Fraction]] = {1: [Fraction(1)]}
    one_plus_w = [Fraction(1), Fraction(1)]
    for n in range(1, 11):
        pn = P[n]
        term1 = poly_mul(one_plus_w, derivative_poly(pn))
        linear = [Fraction(1 - 3*n), Fraction(-n)]
        pnext = poly_add(term1, poly_mul(linear, pn))
        P[n + 1] = pnext
        # Differentiate P e^{-nw}(1+w)^{-(2n-1)} and clear common factors.
        independently_cleared = poly_add(
            poly_mul(one_plus_w, derivative_poly(pn)),
            poly_add(poly_mul([Fraction(-n), Fraction(-n)], pn),
                     [-(2*n-1)*c for c in pn]),
        )
        assert_poly_equal(f"higher_derivative_induction_n_{n}", pnext, independently_cleared,
                          "cleared numerator of the derivative operator")
    assert_poly_equal("P2", P[2], [Fraction(-2), Fraction(-1)])
    assert_poly_equal("P3", P[3], [Fraction(9), Fraction(8), Fraction(2)])
    assert_poly_equal("P4", P[4], [Fraction(-64), Fraction(-79), Fraction(-36), Fraction(-6)])

    # Puiseux coefficients at the branch point.
    coeffs = [Fraction(1), -Fraction(1, 3), Fraction(11, 72),
              -Fraction(43, 540), Fraction(769, 17280)]
    for sign, branch in ((1, "principal"), (-1, "secondary")):
        s = zero_series(7)
        for j, c in enumerate(coeffs, start=1):
            s[j] = c * (sign if j % 2 else 1)
        s_minus_one = s[:]
        s_minus_one[0] -= 1
        lhs = scale(add([Fraction(1)] + [Fraction(0)] * 6,
                        mul(s_minus_one, exp_series(s, 6), 6), 6), Fraction(2), 6)
        p2 = zero_series(6); p2[2] = 1
        assert_series_zero(f"puiseux_{branch}_through_p6", sub(lhs, p2, 6),
                           "substitution in p^2=2(1+(s-1)e^s)")

    # Stirling-number asymptotic polynomials A_1,...,A_4.
    A: dict[int, list[Fraction]] = {}
    for ell in range(1, 5):
        poly = [Fraction(0)] * (ell + 1)
        for m in range(1, ell + 1):
            poly[m] = Fraction(((-1) ** (ell - m)) * unsigned_stirling_first(ell, ell - m + 1),
                               math.factorial(m))
        A[ell] = poly
    assert_poly_equal("asymptotic_A1", A[1], [0, 1])
    assert_poly_equal("asymptotic_A2", A[2], [0, -1, Fraction(1, 2)])
    assert_poly_equal("asymptotic_A3", A[3], [0, 1, Fraction(-3, 2), Fraction(1, 3)])
    assert_poly_equal("asymptotic_A4", A[4], [0, -1, 3, Fraction(-11, 6), Fraction(1, 4)])

    # Q(v)=(e^v-1+2v)^2-18(e^v-1-v).
    M = 16
    v = zero_series(M); v[1] = 1
    ev = exp_series(v, M)
    a = ev[:]; a[0] -= 1; a[1] += 2
    b = ev[:]; b[0] -= 1; b[1] -= 1
    q = sub(mul(a, a, M), scale(b, Fraction(18), M), M)
    for n in range(M + 1):
        expected = Fraction(0) if n < 4 else Fraction(2**n + 4*n - 20, math.factorial(n))
        record(f"secondary_near_Q_coefficient_{n}", "exact", q[n] == expected,
               f"coefficient={q[n]}, expected={expected}")

    # Elementary antiderivatives after the substitution x=w e^w.  We record
    # the coefficient identities in Q[w,e^w] after cancellation.
    # d/dw[e^w(w^2-w+1)] = e^w(w^2+w) = w e^w(1+w).
    left_poly = poly_add([Fraction(1), Fraction(-1), Fraction(1)],
                         derivative_poly([Fraction(1), Fraction(-1), Fraction(1)]))
    assert_poly_equal("antiderivative_W", left_poly, [0, 1, 1],
                      "(P+P') for P=w^2-w+1")
    # d/dw(w^2/2+w)=w+1, matching (W/x) dx/dw.
    assert_poly_equal("antiderivative_W_over_x",
                      derivative_poly([0, 1, Fraction(1, 2)]), [1, 1])


# ---------------------------------------------------------------------------
# High-precision diagnostics
# ---------------------------------------------------------------------------

def W0(x: mp.mpf) -> mp.mpf:
    return mp.re(mp.lambertw(x, 0))


def Wm1(x: mp.mpf) -> mp.mpf:
    return mp.re(mp.lambertw(x, -1))


def close(name: str, a: mp.mpf | mp.mpc, b: mp.mpf | mp.mpc, tol: mp.mpf, detail: str) -> None:
    err = abs(a - b)
    record(name, "numeric", err <= tol, f"{detail}; abs_error={mp.nstr(err, 14)}", float(err))


def inequality(name: str, lhs: mp.mpf, rhs: mp.mpf, relation: str, detail: str) -> None:
    if relation == "<=":
        margin = rhs - lhs; ok = margin >= -mp.mpf("1e-50")
    elif relation == "<":
        margin = rhs - lhs; ok = margin > 0
    elif relation == ">=":
        margin = lhs - rhs; ok = margin >= -mp.mpf("1e-50")
    elif relation == ">":
        margin = lhs - rhs; ok = margin > 0
    else:
        raise ValueError(relation)
    record(name, "numeric", ok, f"{detail}; signed_margin={mp.nstr(margin, 14)}", float(margin))


def numerical_checks() -> None:
    mp.mp.dps = 70
    tol = mp.mpf("1e-55")

    for idx, x in enumerate([mp.mpf("-0.36"), mp.mpf("-0.2"), mp.mpf("-0.01"),
                             mp.mpf("0"), mp.mpf("0.5"), mp.mpf("1"), mp.e, mp.mpf("100")]):
        w = W0(x)
        close(f"principal_residual_{idx}", w*mp.e**w, x, tol, f"x={x}")
        if x < 0:
            wm = Wm1(x)
            close(f"secondary_residual_{idx}", wm*mp.e**wm, x, tol, f"x={x}")
            inequality(f"secondary_range_{idx}", wm, mp.mpf("-1"), "<=", f"x={x}")

    close("W0_zero", W0(0), 0, tol, "W0(0)=0")
    close("W0_e", W0(mp.e), 1, tol, "W0(e)=1")
    omega = W0(1)
    inequality("omega_lower_decimal", omega, mp.mpf("0.567143290409783872999967"), ">", "lower decimal")
    inequality("omega_upper_decimal", omega, mp.mpf("0.567143290409783872999969"), "<", "upper decimal")
    close("omega_fixed_point", omega, mp.e**(-omega), tol, "Omega=e^-Omega")

    I0e = mp.quad(lambda t: W0(t), [0, mp.e])
    close("integral_0_e", I0e, mp.e - 1, mp.mpf("1e-55"), "integral W0 from 0 to e")

    for N in (2, 3, 5):
        value = (mp.mpf(1)/N) * mp.quad(
            lambda u: u**(-mp.mpf(1)/N) * (1+u) * mp.e**(-u/N), [0, 1, mp.inf])
        expected = mp.power(N, 1-mp.mpf(1)/N) * mp.gamma(1-mp.mpf(1)/N)
        close(f"gamma_integral_N_{N}", value, expected, mp.mpf("1e-34"), "formula (7.7)")

    I79 = mp.quad(lambda u: (mp.sqrt(u) + 1/mp.sqrt(u)) * mp.e**(-u/2), [0, 1, mp.inf])
    close("integral_7_9", I79, 2*mp.sqrt(2*mp.pi), mp.mpf("1e-34"), "formula (7.9)")

    for j, xx in enumerate([mp.e, mp.mpf("4"), mp.mpf("10"), mp.mpf("100"), mp.mpf("1e6")]):
        t = mp.log(xx); u = mp.log(t); w = W0(xx)
        lo = t-u+u/(2*t); hi = t-u+(mp.e/(mp.e-1))*u/t
        inequality(f"HH_lower_{j}", lo, w, "<=", f"x={xx}")
        inequality(f"HH_upper_{j}", w, hi, "<=", f"x={xx}")
        q = u/t; A = mp.log(xx/t); h = -mp.log(1-q)
        lo2 = A + A/(1+A)*h
        hi2 = A + h - mp.log(1+h/(1+A))
        inequality(f"IB_lower_{j}", lo2, w, "<=", f"x={xx}")
        inequality(f"IB_upper_{j}", w, hi2, "<=", f"x={xx}")

    pairs = [(-1/mp.e, mp.mpf("0.5")), (mp.mpf("-0.2"), mp.mpf("1")),
             (mp.mpf("0"), mp.mpf("1")), (mp.mpf("1"), mp.mpf("2")),
             (mp.mpf("10"), mp.mpf("3"))]
    for j, (xx, y) in enumerate(pairs):
        upper = mp.log((xx+y)/(1+mp.log(y)))
        inequality(f"general_upper_{j}", W0(xx), upper, "<=", f"x={xx}, y={y}")
    for j, y in enumerate([mp.mpf("0.5"), mp.mpf("1"), mp.mpf("2"), mp.mpf("10")]):
        xx = y*mp.log(y)
        upper = mp.log((xx+y)/(1+mp.log(y)))
        close(f"general_upper_equality_{j}", W0(xx), upper, mp.mpf("1e-55"), f"y={y}")

    for j in range(1, 20):
        xx = -1/mp.e + (mp.mpf(j)/20) * (1/mp.e)
        q = 1 + mp.e*xx
        lo = mp.sqrt(q)-1; hi = mp.root(q, 3)-1; w = W0(xx)
        inequality(f"root_bound_lower_{j}", lo, w, "<=", f"x={mp.nstr(xx,8)}")
        inequality(f"root_bound_upper_{j}", w, hi, "<=", f"x={mp.nstr(xx,8)}")

    for j, u in enumerate([mp.mpf("0.001"), mp.mpf("0.01"), mp.mpf("0.1"), mp.mpf("1"), mp.mpf("10")]):
        xx = -mp.e**(-u-1); w = Wm1(xx)
        lower = -1-mp.sqrt(2*u)-u; upper = -1-mp.sqrt(2*u)-2*u/3
        inequality(f"wm_near_lower_{j}", lower, w, "<", f"u={u}")
        inequality(f"wm_near_upper_{j}", w, upper, "<", f"u={u}")

    for j, u in enumerate([mp.mpf("1.01"), mp.mpf("1.2"), mp.mpf("2"), mp.mpf("5"), mp.mpf("20")]):
        xx = -mp.e**(-u); w = Wm1(xx)
        lower = -u-mp.log(u)-mp.log(u)/(u-1)
        upper = -u-mp.log(u)-mp.log(u)/(u+mp.log(u))
        inequality(f"wm_far_lower_{j}", lower, w, "<=", f"u={u}")
        inequality(f"wm_far_upper_{j}", w, upper, "<=", f"u={u}")

    for j, pp in enumerate([mp.mpf("1e-2"), mp.mpf("5e-3"), mp.mpf("1e-3")]):
        z = (pp*pp/2 - 1) / mp.e
        coeff = [mp.mpf(1), -mp.mpf(1)/3, mp.mpf(11)/72, -mp.mpf(43)/540, mp.mpf(769)/17280]
        approx0 = -1 + sum(coeff[k-1]*pp**k for k in range(1,6))
        approxm = -1 + sum(((-1)**k)*coeff[k-1]*pp**k for k in range(1,6))
        err0 = abs(W0(z)-approx0); errm = abs(Wm1(z)-approxm)
        record(f"puiseux_principal_numeric_{j}", "numeric", err0 < 2*pp**6,
               f"p={pp}; error={mp.nstr(err0,14)}", float(err0))
        record(f"puiseux_secondary_numeric_{j}", "numeric", errm < 2*pp**6,
               f"p={pp}; error={mp.nstr(errm,14)}", float(errm))

    for j, xx in enumerate([mp.mpf("1e20"), mp.mpf("1e50"), mp.mpf("1e100")]):
        L1 = mp.log(xx); L2 = mp.log(L1)
        approx = (L1-L2 + L2/L1 + L2*(-2+L2)/(2*L1**2)
                  + L2*(6-9*L2+2*L2**2)/(6*L1**3)
                  + L2*(-12+36*L2-22*L2**2+3*L2**3)/(12*L1**4))
        err = abs(W0(xx)-approx); scalev = (1+L2)**5/L1**5
        record(f"large_x_asymptotic_{j}", "numeric", err/scalev < 2,
               f"error/scale={mp.nstr(err/scalev,14)}", float(err/scalev))

    log3 = mp.log(3)
    sol0 = -1-W0(-log3/6)/log3; solm = -1-Wm1(-log3/6)/log3
    close("equation_2x2_principal", 2*sol0+2, 3**sol0, tol, "first solution")
    close("equation_2x2_secondary", 2*solm+2, 3**solm, tol, "second solution")
    inequality("equation_2x2_first_interval_lo", sol0, mp.mpf("-0.79012"), ">", "reported interval")
    inequality("equation_2x2_first_interval_hi", sol0, mp.mpf("-0.79010"), "<", "reported interval")
    inequality("equation_2x2_second_interval_lo", solm, mp.mpf("1.44455"), ">", "reported interval")
    inequality("equation_2x2_second_interval_hi", solm, mp.mpf("1.44457"), "<", "reported interval")

    y = mp.mpf("0.8")
    for branch in (0, -1):
        xx = mp.e**mp.lambertw(mp.log(y), branch)
        close(f"superroot_branch_{branch}", xx**xx, y, tol, "x^x=y")

    xx = mp.mpf("7"); target = W0(xx)
    wn = mp.mpf("1.5")
    for _ in range(8):
        wn -= (wn*mp.e**wn-xx)/(mp.e**wn*(1+wn))
    close("newton_convergence", wn, target, mp.mpf("1e-55"), "8 Newton steps for x=7")
    wh = mp.mpf("1.5")
    for _ in range(5):
        f = wh*mp.e**wh-xx
        wh -= f/(mp.e**wh*(1+wh) - (wh+2)*f/(2*(wh+1)))
    close("halley_convergence", wh, target, mp.mpf("1e-55"), "5 Halley steps for x=7")


def write_reports(report_path: Path, json_path: Path) -> None:
    passed = sum(c.passed for c in CHECKS); total = len(CHECKS)
    lines = [
        "Lambert W constructive packet: verification report",
        "==================================================", "",
        f"Python: {sys.version.split()[0]}",
        f"mpmath: {mp.__version__}",
        f"Precision: {mp.mp.dps} decimal digits",
        f"Checks passed: {passed}/{total}",
        f"Status: {'PASS' if passed == total else 'FAIL'}", "",
    ]
    kinds: dict[str, list[Check]] = {}
    for c in CHECKS:
        kinds.setdefault(c.kind, []).append(c)
    for kind in sorted(kinds):
        lines.append(f"[{kind.upper()}] {len(kinds[kind])} checks")
        for c in kinds[kind]:
            lines.append(f"  {'PASS' if c.passed else 'FAIL'}  {c.name}: {c.detail}")
        lines.append("")
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text("\n".join(lines), encoding="utf-8")
    json_path.write_text(json.dumps({
        "summary": {"passed": passed, "total": total, "status": "PASS" if passed == total else "FAIL"},
        "environment": {"python": sys.version.split()[0], "mpmath": mp.__version__, "dps": mp.mp.dps},
        "checks": [asdict(c) for c in CHECKS],
    }, indent=2), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", type=Path, default=Path("evidence/verification_report.txt"))
    parser.add_argument("--json", type=Path, default=Path("evidence/verification_report.json"))
    args = parser.parse_args()
    try:
        symbolic_checks()
        numerical_checks()
    except Exception as exc:
        CHECKS.append(Check("uncaught_exception", "runtime", False, repr(exc)))
        write_reports(args.report, args.json)
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1
    write_reports(args.report, args.json)
    print(f"PASS: {len(CHECKS)} checks; report={args.report}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
