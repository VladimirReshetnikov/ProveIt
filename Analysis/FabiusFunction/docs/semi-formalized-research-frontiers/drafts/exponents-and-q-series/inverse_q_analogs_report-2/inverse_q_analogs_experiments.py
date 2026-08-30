#!/usr/bin/env python3
"""Numerical and symbolic checks for the report
"Inverse Functions of q-Pochhammer Symbols, Gaussian Coefficients,
and Related q-Analogs".

The script is intentionally self-contained.  It uses only mpmath and sympy,
both of which are standard Python packages in scientific Python environments.
Every experiment compares a formula derived in the report with direct high-
precision evaluation or a symbolic expansion.

This is *validation*, not proof.  The proofs in the report are independent of
these computations.  The numerical checks are designed to catch transcription
errors, missing low-degree exceptions, and branch/sign mistakes.

Run:
    python inverse_q_analogs_experiments.py

The human-readable output is also distributed as numerical_results.txt.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Iterable, List, Sequence, Tuple

import mpmath as mp
import sympy as sp

mp.mp.dps = 80


# ---------------------------------------------------------------------------
# Basic q-functions
# ---------------------------------------------------------------------------

def finite_qpoch(a: mp.mpf | mp.mpc, q: mp.mpf | mp.mpc, n: int):
    """Return (a;q)_n = product_{j=0}^{n-1} (1-a q^j)."""
    p = mp.mpf(1)
    for j in range(n):
        p *= 1 - a * q**j
    return p


def log_qpoch_inf(a: mp.mpf, q: mp.mpf, tol: mp.mpf | None = None):
    r"""Return log((a;q)_infinity) for 0 <= a,q < 1.

    We use the absolutely convergent Lambert-series identity

        log((a;q)_infinity) = -sum_{m>=1} a^m/[m(1-q^m)].

    It is much faster than multiplying factors when q is close to 1 and is
    ideal for the real test cases below.  The routine is not intended as a
    general complex analytic-continuation implementation.
    """
    if tol is None:
        tol = mp.mpf("1e-72")
    if not (-1 < a < 1 and 0 <= q < 1):
        raise ValueError("log_qpoch_inf requires -1 < a < 1 and 0 <= q < 1")
    if a == 0:
        return mp.mpf(0)
    total = mp.mpf(0)
    m = 1
    while True:
        term = a**m / (m * (1 - q**m))
        total -= term
        if abs(term) < tol:
            # Require a few consecutive small terms to avoid accidental early
            # termination when parameters are unusual.
            ok = True
            for r in range(1, 4):
                nxt = a ** (m + r) / ((m + r) * (1 - q ** (m + r)))
                if abs(nxt) >= tol:
                    ok = False
                    break
            if ok:
                break
        m += 1
        if m > 2_000_000:
            raise RuntimeError("Lambert series did not converge")
    return total


def qpoch_inf(a: mp.mpf, q: mp.mpf):
    """Return (a;q)_infinity for real 0 <= a,q < 1."""
    return mp.e ** log_qpoch_inf(a, q)


def gaussian_qbinom(n: int, k: int, q: mp.mpf | mp.mpc):
    """Evaluate the Gaussian polynomial [n choose k]_q.

    The removable singularity at q=1 is handled explicitly.  For other q we
    use the product representation.  Test points avoid roots of denominator
    factors, so no root-of-unity cancellation machinery is needed here.
    """
    if k < 0 or k > n:
        return mp.mpf(0)
    k = min(k, n - k)
    if k == 0:
        return mp.mpf(1)
    if abs(q - 1) < mp.mpf("1e-60"):
        return mp.mpf(math.comb(n, k))
    p = mp.mpf(1)
    for j in range(1, k + 1):
        p *= (1 - q ** (n - k + j)) / (1 - q**j)
    return p


def gaussian_qbinom_poly(n: int, k: int, symbol: sp.Symbol | None = None):
    """Return [n choose k]_q as an exact SymPy polynomial by recurrence."""
    q = symbol or sp.Symbol("q")
    if k < 0 or k > n:
        return sp.Integer(0)
    k = min(k, n - k)
    row = [sp.Integer(1)]
    for m in range(1, n + 1):
        new = [sp.Integer(1)]
        for j in range(1, m):
            left = row[j] if j < len(row) else 0
            right = row[j - 1]
            new.append(sp.expand(left + q ** (m - j) * right))
        new.append(sp.Integer(1))
        row = new
    return sp.Poly(sp.expand(row[k]), q)


def q_number(x: mp.mpf, q: mp.mpf):
    """Return [x]_q=(1-q^x)/(1-q), with its continuous value at q=1."""
    if abs(q - 1) < mp.mpf("1e-50"):
        return x
    return (1 - q**x) / (1 - q)


def q_factorial(n: int, q: mp.mpf):
    """Return [n]_q! for integer n >= 0."""
    p = mp.mpf(1)
    for j in range(1, n + 1):
        p *= q_number(mp.mpf(j), q)
    return p


def q_gamma(x: mp.mpf, q: mp.mpf):
    r"""Return Jackson's Gamma_q(x) for 0<q<1 and x>0.

    For q not extremely close to 1, mpmath's q-Pochhammer implementation is
    reliable.  The experiments use t=-log(q) >= 0.025.
    """
    return (1 - q) ** (1 - x) * mp.qp(q, q) / mp.qp(q**x, q)


def q_catalan(n: int, q: mp.mpf):
    """Return MacMahon's q-Catalan polynomial [2n choose n]_q/[n+1]_q."""
    return gaussian_qbinom(2 * n, n, q) / q_number(mp.mpf(n + 1), q)


# ---------------------------------------------------------------------------
# Small numerical helpers
# ---------------------------------------------------------------------------

def bisect_monotone(f: Callable[[mp.mpf], mp.mpf], lo: mp.mpf, hi: mp.mpf,
                    target: mp.mpf, increasing: bool = True,
                    iterations: int = 250):
    """Invert a continuous monotone real function on [lo,hi] by bisection."""
    flo = f(lo) - target
    fhi = f(hi) - target
    if increasing:
        if flo > 0 or fhi < 0:
            raise ValueError("target not bracketed for increasing function")
    else:
        if flo < 0 or fhi > 0:
            raise ValueError("target not bracketed for decreasing function")
    for _ in range(iterations):
        mid = (lo + hi) / 2
        fm = f(mid) - target
        if (fm < 0) == increasing:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def sci(x, digits: int = 8) -> str:
    """Compact scientific formatting for mpmath values."""
    return mp.nstr(x, digits, min_fixed=-3, max_fixed=4)


def relative_error(approx, exact):
    if exact == 0:
        return abs(approx)
    return abs((approx - exact) / exact)


# ---------------------------------------------------------------------------
# Experiments
# ---------------------------------------------------------------------------

def experiment_symbolic_q0_reversion() -> List[str]:
    """Check the stable q=0 inverse series and low-n exceptions symbolically."""
    q, a, x = sp.symbols("q a x")
    lines = ["EXPERIMENT 1: symbolic q=0 reversion for (a;q)_n"]

    expected_stable = x - x**2 + (a + 1) * x**3 - (4 * a + 1) * x**4 \
        + (3 * a**2 + 11 * a + 1) * x**5

    for n in [2, 3, 4, 5, 6, 8]:
        P = sp.prod(1 - a * q**j for j in range(n))
        # x=(P-(1-a))/(a^2-a).  Solve coefficient-by-coefficient for
        # q=x+b2*x^2+...+b5*x^5.
        x_of_q = sp.series((P - (1 - a)) / (a**2 - a), q, 0, 6).removeO()
        coeffs = sp.symbols("b2:6")
        q_ansatz = x + sum(coeffs[r - 2] * x**r for r in range(2, 6))
        composed = sp.series(x_of_q.subs(q, q_ansatz), x, 0, 6).removeO()
        equations = [sp.Eq(sp.expand(composed).coeff(x, r), 0) for r in range(2, 6)]
        sol = sp.solve(equations, coeffs, dict=True)[0]
        inv = sp.expand(q_ansatz.subs(sol))
        lines.append(f"  n={n}: q(x)={sp.sstr(inv)}")
        if n >= 6:
            assert sp.simplify(inv - expected_stable) == 0

    lines.append("  Stable formula verified exactly for n>=6 through x^5.")
    lines.append("")
    return lines


def experiment_pochhammer_q0_numeric() -> List[str]:
    """Numerically test the stable q=0 inverse expansion."""
    a = mp.mpf("0.37")
    n = 8
    lines = ["EXPERIMENT 2: numerical q=0 inverse for finite q-Pochhammer",
             "  a=0.37, n=8; x=(y-(1-a))/(a^2-a)"]
    for q_true in [mp.mpf("0.02"), mp.mpf("0.01"), mp.mpf("0.005")]:
        y = finite_qpoch(a, q_true, n)
        x = (y - (1 - a)) / (a**2 - a)
        q3 = x - x**2 + (a + 1) * x**3
        q5 = q3 - (4 * a + 1) * x**4 + (3 * a**2 + 11 * a + 1) * x**5
        lines.append(
            f"  q={sci(q_true,10)}  err(O(x^3))={sci(abs(q3-q_true),7)}"
            f"  err(O(x^5))={sci(abs(q5-q_true),7)}"
        )
    lines.append("")
    return lines


def experiment_infinite_pochhammer_q1() -> List[str]:
    r"""Test singular inversion q->1 for (a;q)_infinity at fixed a."""
    a = mp.mpf("0.30")
    A = mp.polylog(2, a)
    B = mp.log(1 - a) / 2
    C = a / (12 * (1 - a))
    E = a * (1 + a) / (720 * (1 - a) ** 3)  # Li_{-2}(a)/720
    lines = ["EXPERIMENT 3: singular q->1 inversion for (a;q)_infinity",
             "  a=0.30; t=-log q is reconstructed from y"]
    for t_true in [mp.mpf("0.10"), mp.mpf("0.07"), mp.mpf("0.05"), mp.mpf("0.035")]:
        q = mp.e**(-t_true)
        logy = log_qpoch_inf(a, q)
        Y = -logy
        Lam = Y + B
        t1 = A / Lam
        t3 = t1 + A**2 * C / Lam**3
        t5 = t3 + (2 * A**3 * C**2 - A**4 * E) / Lam**5
        lines.append(
            f"  t={sci(t_true,8)}  err1={sci(abs(t1-t_true),7)}"
            f"  err3={sci(abs(t3-t_true),7)}  err5={sci(abs(t5-t_true),7)}"
        )
    lines.append("")
    return lines



def experiment_infinite_pochhammer_minus_one() -> List[str]:
    r"""Test radial q->-1 inversion for (a;q)_infinity."""
    a = mp.mpf("0.30")
    A = mp.polylog(2, a * a) / 4
    B = mp.log(1 - a) / 2
    C = a * (a + 3) / (12 * (1 - a * a))
    lines = ["EXPERIMENT 4: radial q->-1 inversion for (a;q)_infinity",
             "  q=-e^{-t}, a=0.30; t is reconstructed from y"]
    for t_true in [mp.mpf("0.10"), mp.mpf("0.07"), mp.mpf("0.05"), mp.mpf("0.035")]:
        Q = mp.e ** (-2 * t_true)
        # Even and odd factors split exactly:
        # (a;-e^{-t})_inf=(a;e^{-2t})_inf(-a e^{-t};e^{-2t})_inf.
        logy = log_qpoch_inf(a, Q) + log_qpoch_inf(-a * mp.e**(-t_true), Q)
        Y = -logy
        Lam = Y + B
        t1 = A / Lam
        t3 = t1 + A**2 * C / Lam**3
        lines.append(
            f"  t={sci(t_true,8)}  err1={sci(abs(t1-t_true),7)}"
            f"  err3={sci(abs(t3-t_true),7)}"
        )
    lines.append("")
    return lines

def experiment_pochhammer_a_double_scaling() -> List[str]:
    r"""Test the a-inverse as q->1 with y fixed."""
    y = mp.e**(-1)  # L=1 is convenient but nontrivial.
    L = -mp.log(y)
    lines = ["EXPERIMENT 5: a-inverse of (a;e^{-t})_infinity at fixed y=e^{-1}"]
    for t in [mp.mpf("0.10"), mp.mpf("0.07"), mp.mpf("0.05"), mp.mpf("0.035")]:
        q = mp.e**(-t)
        a1 = L * t
        a2 = a1 - L * (L + 2) * t**2 / 4
        a3 = a2 + L * (L**2 + 9 * L + 12) * t**3 / 72
        a4 = a3 - L * (L**3 + 4 * L**2 + 12 * L + 24) * t**4 / 576
        # Newton/secant inversion is far faster than bisection here.  The
        # asymptotic approximation supplies an excellent positive initial
        # guess and all test points lie well inside 0<a<1.
        exact = mp.findroot(lambda aa: log_qpoch_inf(aa, q) - mp.log(y),
                            (a3, a4))
        lines.append(
            f"  t={sci(t,8)}  exact a={sci(exact,12)}"
            f"  |e2|={sci(abs(a2-exact),7)} |e3|={sci(abs(a3-exact),7)}"
            f" |e4|={sci(abs(a4-exact),7)}"
        )
    lines.append("")
    return lines


def experiment_qbinomial_q1() -> List[str]:
    """Test the q=1 inverse expansion for a Gaussian coefficient."""
    n, k = 8, 3
    D = k * (n - k)
    C0 = mp.mpf(math.comb(n, k))
    lines = ["EXPERIMENT 6: q=1 inverse of [8 choose 3]_q",
             "  u=log(y/binom(8,3)); compare two- and three-term t-series"]
    for t_true in [mp.mpf("0.08"), mp.mpf("0.04"), mp.mpf("-0.04")]:
        q = mp.e**t_true
        y = gaussian_qbinom(n, k, q)
        u = mp.log(y / C0)
        t1 = 2 * u / D
        t2 = t1 - (n + 1) * u**2 / (3 * D**2)
        t3 = t2 + (n + 1) ** 2 * u**3 / (9 * D**3)
        lines.append(
            f"  t={sci(t_true,8)}  err1={sci(abs(t1-t_true),7)}"
            f"  err2={sci(abs(t2-t_true),7)}  err3={sci(abs(t3-t_true),7)}"
        )
    lines.append("")
    return lines


def experiment_qbinomial_minus_one() -> List[str]:
    """Verify the explicit values and derivatives at q=-1 exactly."""
    q = sp.Symbol("q")
    cases = [(6, 3), (8, 3), (7, 3), (8, 4), (9, 4)]
    lines = ["EXPERIMENT 7: exact Gaussian coefficients at q=-1"]
    for n, k in cases:
        poly = gaussian_qbinom_poly(n, k, q)
        val = sp.expand(poly.as_expr()).subs(q, -1)
        der = sp.diff(poly.as_expr(), q).subs(q, -1)
        D = k * (n - k)
        if n % 2 == 0 and k % 2 == 1:
            m, r = n // 2, (k - 1) // 2
            pred_val = 0
            pred_der = sp.factorial(m) / (sp.factorial(r) * sp.factorial(m - r - 1))
        else:
            pred_val = math.comb(n // 2, k // 2)
            pred_der = -sp.Rational(D, 2) * pred_val
        assert sp.simplify(val - pred_val) == 0
        assert sp.simplify(der - pred_der) == 0
        lines.append(f"  (n,k)=({n},{k}): value={val}, derivative={der}")
    lines.append("  All displayed value/derivative formulas verified exactly.")
    lines.append("")
    return lines


def experiment_qgamma_q1_inverse() -> List[str]:
    r"""Test x-inversion of Gamma_q near q=1 at fixed y=Gamma(x0)."""
    x0 = mp.mpf("3.4")
    y = mp.gamma(x0)
    psi = mp.digamma(x0)
    trigamma = mp.polygamma(1, x0)

    def A1(x):
        return -(x - 1) * (x - 2) / 4

    def A1p(x):
        return -(2 * x - 3) / 4

    def B3(x):
        return x**3 - mp.mpf("1.5") * x**2 + mp.mpf("0.5") * x

    def A2(x):
        return B3(x) / 72 - (x - 1) / 24

    d1 = -A1(x0) / psi
    d2 = -(A2(x0) + A1p(x0) * d1 + mp.mpf("0.5") * trigamma * d1**2) / psi

    lines = ["EXPERIMENT 8: inverse Gamma_q(x)=Gamma(3.4) as q->1",
             f"  predicted x_q=3.4+({sci(d1,12)})t+({sci(d2,12)})t^2+..."]
    for t in [mp.mpf("0.08"), mp.mpf("0.05"), mp.mpf("0.03"), mp.mpf("0.025")]:
        q = mp.e**(-t)
        exact = mp.findroot(lambda xx: mp.log(q_gamma(xx, q)) - mp.log(y), x0 + d1 * t)
        x1 = x0 + d1 * t
        x2 = x1 + d2 * t**2
        lines.append(
            f"  t={sci(t,8)}  exact x={sci(exact,13)}"
            f"  |e1|={sci(abs(x1-exact),7)} |e2|={sci(abs(x2-exact),7)}"
        )
    lines.append("")
    return lines


def experiment_qcatalan_ramification() -> List[str]:
    """Check the square-root inverse at the q-Catalan endpoint."""
    n = 5
    lines = ["EXPERIMENT 9: square-root ramification for MacMahon q-Catalan",
             "  n=5; compare q with sqrt(Cat_5(q)-1)"]
    for q in [mp.mpf("0.04"), mp.mpf("0.02"), mp.mpf("0.01")]:
        y = q_catalan(n, q)
        root = mp.sqrt(y - 1)
        lines.append(
            f"  q={sci(q,8)}  sqrt(y-1)={sci(root,12)}"
            f"  difference={sci(root-q,7)}"
        )
    lines.append("")
    return lines


def experiment_qnumber_exact_inverse() -> List[str]:
    """Check the exact parameter inverse of the q-number."""
    q = mp.mpf("0.63")
    lines = ["EXPERIMENT 10: exact x-inverse of [x]_q"]
    for x in [mp.mpf("0.7"), mp.mpf("2.5"), mp.mpf("7.2")]:
        y = q_number(x, q)
        recovered = mp.log(1 - y * (1 - q)) / mp.log(q)
        lines.append(
            f"  x={sci(x,6)} recovered={sci(recovered,16)}"
            f"  error={sci(abs(recovered-x),7)}"
        )
    lines.append("")
    return lines


def main() -> None:
    sections: List[str] = []
    sections.extend([
        "NUMERICAL AND SYMBOLIC VALIDATION",
        "=================================",
        "mpmath working precision: 80 decimal digits",
        "",
    ])
    for experiment in [
        experiment_symbolic_q0_reversion,
        experiment_pochhammer_q0_numeric,
        experiment_infinite_pochhammer_q1,
        experiment_infinite_pochhammer_minus_one,
        experiment_pochhammer_a_double_scaling,
        experiment_qbinomial_q1,
        experiment_qbinomial_minus_one,
        experiment_qgamma_q1_inverse,
        experiment_qcatalan_ramification,
        experiment_qnumber_exact_inverse,
    ]:
        sections.extend(experiment())

    text = "\n".join(sections).rstrip() + "\n"
    # Use ``end=""`` so stdout is byte-for-byte identical to the saved file.
    print(text, end="")
    out = Path(__file__).with_name("numerical_results.txt")
    out.write_text(text, encoding="utf-8")


if __name__ == "__main__":
    main()
