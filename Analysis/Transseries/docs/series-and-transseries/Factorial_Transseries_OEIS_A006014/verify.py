#!/usr/bin/env python3
"""Exact and high-precision checks for the A006014 research note.

Dependencies: Python 3.11+, sympy, mpmath.
The script verifies:
  * the A006014 recurrence and the logarithmic-derivative identity;
  * the bridge n! u_n = A130032(n);
  * the all-orders late-term coefficients phi_j by two recursions;
  * the normalized, logarithmic, centered, and lambda-deformed expansions;
  * the monotone global bounds and inverse-transseries tables used in the paper.
"""
from __future__ import annotations

from math import factorial
from pathlib import Path

import mpmath as mp
import sympy as sp


def a006014(N: int) -> list[int]:
    if N < 1:
        raise ValueError("N must be at least 1")
    a = [0] * (N + 1)
    a[1] = 1
    for n in range(1, N):
        a[n + 1] = (n + 1) * a[n] + sum(a[k] * a[n - k] for k in range(1, n))
    return a


def carrier_u(N: int) -> list[sp.Rational]:
    u: list[sp.Rational] = [sp.Rational(1)]
    for n in range(N):
        u.append(sp.cancel(u[-1] * sp.Rational(n * n + n + 1, n + 1)))
    return u


def a130032(n: int) -> int:
    p = 1
    for k in range(n + 1):
        p *= k * k - k + 1
    return p


def phi_coefficients(N: int) -> tuple[list[sp.Rational], list[sp.Rational]]:
    """Return r_j and phi_j from R=U(-x)/U(x), Phi=R/x+xR'."""
    u = carrier_u(N)
    r: list[sp.Rational] = [sp.Rational(1)]
    for n in range(1, N + 1):
        rn = (-1) ** n * u[n] - sum(u[k] * r[n - k] for k in range(1, n + 1))
        r.append(sp.cancel(rn))
    phi = [r[0]]
    for j in range(1, N + 1):
        phi.append(sp.cancel(r[j] + (j - 1) * r[j - 1]))
    return r, phi


def verify_exact_identities(N: int = 60) -> None:
    a = a006014(N)
    u = carrier_u(N)
    for n in range(N + 1):
        assert sp.factorial(n) * u[n] == a130032(n), (n, u[n], a130032(n))
    for n in range(1, N + 1):
        lhs = sum(sp.Integer(a[k]) * u[n - k] for k in range(1, n + 1))
        rhs = n * u[n]
        assert sp.cancel(lhs - rhs) == 0, (n, lhs, rhs)



def verify_symbolic_expansions() -> None:
    """Check every displayed rational expansion and the lambda deformation."""
    a = a006014(20)
    _, phi = phi_coefficients(16)

    # Independent triangular late-term recurrence from the two convolution endpoints.
    for m in range(1, 15):
        lhs = m * phi[m] + 2 * sum(sp.Integer(a[k]) * phi[m-k] for k in range(1, m+1))
        assert sp.cancel(lhs) == 0, (m, lhs)

    z = sp.symbols("z")
    q_expr = sp.Integer(0)
    for j in range(12):
        term = z**j / sp.prod(1-r*z for r in range(j))
        q_expr += phi[j] * term
    q_series = sp.series(q_expr, z, 0, 11).removeO().expand()
    q_expected = [
        sp.Rational(1), sp.Rational(-2), sp.Rational(0), sp.Rational(-2),
        sp.Rational(-14), sp.Rational(-514, 5), sp.Rational(-4412, 5),
        sp.Rational(-8782), sp.Rational(-497172, 5),
        sp.Rational(-18919774, 15), sp.Rational(-1328641736, 75),
    ]
    assert [q_series.coeff(z, j) for j in range(11)] == q_expected

    log_series = sp.series(sp.log(q_series), z, 0, 11).removeO().expand()
    log_expected = [
        sp.Rational(0), sp.Rational(-2), sp.Rational(-2), sp.Rational(-14, 3),
        sp.Rational(-22), sp.Rational(-726, 5), sp.Rational(-3518, 3),
        sp.Rational(-78094, 7), sp.Rational(-122110),
        sp.Rational(-67926286, 45), sp.Rational(-103886522, 5),
    ]
    assert [log_series.coeff(z, j) for j in range(11)] == log_expected

    # Center at m=n+1/2, using y=1/m and 1/n=y/(1-y/2).
    y = sp.symbols("y")
    centered = sp.series(log_series.subs(z, y/(1-y/2)), y, 0, 8).removeO().expand()
    centered_expected = [
        sp.Rational(0), sp.Rational(-2), sp.Rational(-3), sp.Rational(-43, 6),
        sp.Rational(-123, 4), sp.Rational(-7893, 40),
        sp.Rational(-25555, 16), sp.Rational(-3422399, 224),
    ]
    assert [centered.coeff(y, j) for j in range(8)] == centered_expected

    lam = sp.symbols("lambda")
    u_lam = [sp.Integer(1)]
    for n in range(8):
        u_lam.append(sp.cancel(u_lam[-1] * (n*n+n+lam)/(n+1)))
    r_lam = [sp.Integer(1)]
    for n in range(1, 6):
        r_lam.append(sp.cancel((-1)**n*u_lam[n] - sum(u_lam[k]*r_lam[n-k] for k in range(1, n+1))))
    phi_lam = [sp.Integer(1)] + [sp.factor(r_lam[j] + (j-1)*r_lam[j-1]) for j in range(1, 5)]
    expected_lam = [
        sp.Integer(1),
        -2*lam,
        2*lam*(lam-1),
        -sp.Rational(2, 3)*lam*(2*lam**2-5*lam+6),
        sp.Rational(2, 3)*lam*(lam-3)*(lam**2-lam+6),
    ]
    assert all(sp.expand(x-y) == 0 for x, y in zip(phi_lam, expected_lam))


def verify_numeric_bounds(N: int = 500) -> None:
    """Check monotonicity and the explicit inequalities on a substantial range."""
    mp.mp.dps = 80
    a = a006014(N)
    C = mp.cosh(mp.pi * mp.sqrt(3) / 2) / mp.pi
    previous = mp.mpf("0")
    product = mp.mpf(1)
    for n in range(1, N+1):
        if n > 1:
            j = n-1
            product *= 1 + mp.mpf(1)/(j*(j+1))
        r_n = product
        b_n = mp.mpf(a[n]) / mp.factorial(n)
        assert b_n >= previous
        if n >= 3:
            assert b_n > previous
        if n == 1:
            assert b_n == r_n
        else:
            assert b_n < r_n < C
            assert r_n - b_n < 2*C*C/n
        previous = b_n

def mpq(q: sp.Rational) -> mp.mpf:
    return mp.mpf(int(sp.numer(q))) / mp.mpf(int(sp.denom(q)))


def factorial_asymptotic(n: int, terms: int, phi: list[sp.Rational], C: mp.mpf) -> mp.mpf:
    return C * mp.fsum(mpq(phi[j]) * mp.gamma(n + 1 - j) for j in range(terms))


def inverse_estimate(Y: int, C: mp.mpf, order: int = 3) -> mp.mpf:
    """The shifted Lambert-W inverse through the displayed order."""
    L = mp.log(mp.mpf(Y) / C)
    X = L - mp.log(2 * mp.pi) / 2
    w = mp.lambertw(X / mp.e)
    M = X / w
    q = mp.log(M)
    ans = M - mp.mpf("0.5")
    if order >= 1:
        ans += mp.mpf(49) / (24 * M * q)
    if order >= 2:
        ans += mp.mpf(3) / (M**2 * q)
    if order >= 3:
        ans += (
            mp.mpf(41266) * q**2 - mp.mpf(24010) * q - mp.mpf(12005)
        ) / (mp.mpf(5760) * M**3 * q**3)
    return ans


def write_tables(path: Path, N: int = 500) -> None:
    mp.mp.dps = 80
    a = a006014(N)
    _, phi = phi_coefficients(14)
    C = mp.cosh(mp.pi * mp.sqrt(3) / 2) / mp.pi

    lines: list[str] = []
    lines.extend([
        "PASS: exact identities through n=80",
        "PASS: phi coefficients through j=11 and the direct endpoint recursion",
        "PASS: normalized, logarithmic, centered, and lambda expansions",
        "PASS: monotonicity and global bounds through n=500",
        "",
    ])
    lines.append(f"C = {mp.nstr(C, 70)}")
    lines.append("phi[0..11] = " + repr(phi[:12]))
    lines.append("")
    lines.append("CONVERGENCE")
    lines.append("n  b_n=a_n/n!  b_n/C  n(1-b_n/C)  n^3(b_n/C-1+2/n)")
    for n in (10, 20, 50, 100, 200, 500):
        b = mp.mpf(a[n]) / mp.factorial(n)
        lines.append(
            f"{n:3d}  {mp.nstr(b, 20):>22}  {mp.nstr(b/C, 20):>22}  "
            f"{mp.nstr(n*(1-b/C), 15):>18}  "
            f"{mp.nstr(n**3*(b/C-1+2/mp.mpf(n)), 15):>20}"
        )

    lines.append("")
    lines.append("ABSOLUTE RELATIVE ERROR OF FACTORIAL EXPANSION")
    lines.append("n       J=1          J=2          J=4          J=6          J=8          J=10         J=12")
    for n in (20, 50, 100, 200):
        errs = []
        for J in (1, 2, 4, 6, 8, 10, 12):
            ap = factorial_asymptotic(n, J, phi, C)
            errs.append(abs(ap / mp.mpf(a[n]) - 1))
        lines.append(f"{n:3d}  " + "  ".join(f"{mp.nstr(e, 8):>12}" for e in errs))

    lines.append("")
    lines.append("INVERSE ERRORS nu(a_N)-N")
    lines.append("N       carrier       +M^-1        +M^-2        +M^-3")
    for n in (10, 20, 50, 100, 200, 500):
        vals = [inverse_estimate(a[n], C, order=j) - n for j in range(4)]
        lines.append(f"{n:3d}  " + "  ".join(f"{mp.nstr(v, 12):>13}" for v in vals))

    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    verify_exact_identities(80)
    verify_symbolic_expansions()
    verify_numeric_bounds(500)
    _, phi = phi_coefficients(14)
    expected = [
        sp.Rational(1), sp.Rational(-2), sp.Rational(0), sp.Rational(-2),
        sp.Rational(-8), sp.Rational(-204, 5), sp.Rational(-1222, 5),
        sp.Rational(-1682), sp.Rational(-65412, 5),
        sp.Rational(-1703944, 15), sp.Rational(-81792476, 75),
        sp.Rational(-3157977156, 275),
    ]
    assert phi[: len(expected)] == expected
    out = Path(__file__).with_name("verification_output.txt")
    write_tables(out)
    print("PASS: exact identities through n=80")
    print("PASS: phi coefficients through j=11")
    print("PASS: normalized, logarithmic, centered, and lambda expansions")
    print("PASS: monotonicity and global bounds through n=500")
    print(f"Wrote {out}")


if __name__ == "__main__":
    main()
