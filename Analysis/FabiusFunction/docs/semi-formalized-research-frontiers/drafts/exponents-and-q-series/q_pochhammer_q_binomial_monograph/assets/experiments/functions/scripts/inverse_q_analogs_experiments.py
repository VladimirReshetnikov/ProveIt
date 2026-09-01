#!/usr/bin/env python3
"""High-precision numerical checks for the inverse-q-analogue report.

This self-contained program uses mpmath, sympy, and matplotlib.  It verifies
local inverse expansions for q-Pochhammer symbols, Gaussian coefficients,
q-gamma, continuous q-binomial coefficients, and the scaled q-exponential.
It also writes a LaTeX table, a plain-text log, and three figures used by the
report.  No network access or external data is required.

Numerical design choices:
* Direct q-Pascal recurrence is used for Gaussian polynomials, especially at
  q=-1, where quotient formulas produce removable 0/0 singularities.
* Infinite products are summed logarithmically to avoid overflow and loss of
  relative accuracy near q=1.
* Real inverse branches are seeded by the derived asymptotic formulas, then
  checked with 80-digit secant solves.
"""
from __future__ import annotations

import math
from pathlib import Path
from typing import Callable, Sequence

import matplotlib.pyplot as plt
import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parent.parent
OUTPUT = ROOT / "output"
FIGURES = ROOT / "figures"
mp.mp.dps = 80


def finite_qpoch(a, q, n: int):
    """Finite q-Pochhammer product (a;q)_n."""
    p = mp.mpf(1)
    for j in range(n):
        p *= 1 - a * q**j
    return p


def finite_qpoch_da(a, q, n: int):
    """Derivative in a; product-rule form remains valid at a zero."""
    total = mp.mpf(0)
    for j in range(n):
        term = -q**j
        for r in range(n):
            if r != j:
                term *= 1 - a * q**r
        total += term
    return total


def qbin_positive(n: int, k: int, q):
    """Gaussian coefficient by product, used only for 0<q<1."""
    if k < 0 or k > n:
        return mp.mpf(0)
    k = min(k, n-k)
    ans = mp.mpf(1)
    for j in range(1, k+1):
        ans *= (1-q**(n-k+j))/(1-q**j)
    return ans


def inverse_a_near_one(y, q, n: int, order: int = 5):
    """Inverse branch a(y) near a=0, y=1, through order five."""
    delta = 1-y
    A = qbin_positive(n, 1, q)
    B = q*qbin_positive(n, 2, q)
    C = q**3*qbin_positive(n, 3, q)
    D = q**6*qbin_positive(n, 4, q)
    E = q**10*qbin_positive(n, 5, q)
    ans = delta/A
    if order >= 2:
        ans += B*delta**2/A**3
    if order >= 3:
        ans += (2*B**2/A**5-C/A**4)*delta**3
    if order >= 4:
        ans += (5*B**3/A**7-5*B*C/A**6+D/A**5)*delta**4
    if order >= 5:
        ans += (14*B**4/A**9-21*B**2*C/A**8+(6*B*D+3*C**2)/A**7-E/A**6)*delta**5
    return ans


def inverse_a_at_root(y, q, n: int, j: int, order: int = 2):
    """Inverse branch at the simple zero a_j=q^{-j}."""
    aj = q**(-j)
    p1 = finite_qpoch_da(aj, q, n)
    h = y/p1
    if order >= 2:
        residual = mp.fsum(q**r/(1-q**(r-j)) for r in range(n) if r != j)
        h += residual*y**2/p1**2
    return aj+h


def inverse_q_near_zero(y, a, order: int = 5):
    """Stable n>=6 inverse of (a;q)_n (and the infinite product) near q=0."""
    eta = 1-y/(1-a)
    ans = eta/a
    if order >= 2:
        ans -= eta**2/a**2
    if order >= 3:
        ans += (a+1)*eta**3/a**3
    if order >= 4:
        ans -= (4*a+1)*eta**4/a**4
    if order >= 5:
        ans += (3*a**2+11*a+1)*eta**5/a**5
    return ans


def inverse_q_near_one_finite(y, a, n: int, order: int = 4):
    """Return t=-log q from the logarithmic expansion at q=1."""
    u = mp.log(y/(1-a)**n)
    K = {}
    for r in range(1, 5):
        power_sum = mp.fsum(mp.mpf(j)**r for j in range(n))
        K[r] = (-1)**(r+1)*mp.polylog(1-r, a)*power_sum
    ans = u/K[1]
    if order >= 2:
        ans -= K[2]*u**2/(2*K[1]**3)
    if order >= 3:
        ans += (3*K[2]**2-K[1]*K[3])*u**3/(6*K[1]**5)
    if order >= 4:
        ans += (-K[4]/(24*K[1]**5)+5*K[2]*K[3]/(12*K[1]**6)-5*K[2]**3/(8*K[1]**7))*u**4
    return ans


def log_qpoch_inf(a, q, tol=None):
    """Principal log of (a;q)_infinity by a convergent log-product."""
    if tol is None:
        tol = mp.mpf(10)**(-(mp.mp.dps-15))
    s = mp.mpf(0)
    qj = mp.mpf(1)
    for _ in range(2_000_000):
        z = a*qj
        s += mp.log(1-z)
        qj *= q
        if abs(z) < tol:
            return s
    raise RuntimeError("q-Pochhammer product did not converge")


def inverse_inf_q_to_one(y, a, order: int = 5):
    """Radial inverse t=-log q for (a;q)_infinity as q->1-."""
    A = mp.polylog(2, a)
    c = a/(12*(1-a))
    d = a*(1+a)/(720*(1-a)**3)
    X = -mp.log(y)+mp.log(1-a)/2
    ans = A/X
    if order >= 3:
        ans += A**2*c/X**3
    if order >= 5:
        ans += (2*A**3*c**2-A**4*d)/X**5
    return ans


def inverse_inf_q_to_minus_one(y, a, order: int = 5):
    """Radial inverse t for q=-exp(-t) as q->-1 from inside the unit disk."""
    A = mp.polylog(2, a**2)/4
    c = a*(a+3)/(12*(1-a**2))
    d = a*(15*a**4+4*a**3+90*a**2+4*a+15)/(720*(1-a**2)**3)
    X = -mp.log(y)+mp.log(1-a)/2
    ans = A/X
    if order >= 3:
        ans += A**2*c/X**3
    if order >= 5:
        ans += (2*A**3*c**2-A**4*d)/X**5
    return ans


def qbinomial_value(n: int, k: int, q):
    """Gaussian polynomial evaluated by q-Pascal recurrence."""
    k = min(k, n-k)
    row = [mp.mpf(0)]*(k+1)
    row[0] = mp.mpf(1)
    for N in range(1, n+1):
        for K in range(min(N, k), 0, -1):
            row[K] = row[K]+q**(N-K)*row[K-1]
    return row[k]


def qbinomial_coefficients(n: int, k: int) -> list[int]:
    """Exact coefficient list of the Gaussian polynomial."""
    q = sp.Symbol("q")
    k = min(k, n-k)
    row = [sp.Integer(0)]*(k+1)
    row[0] = sp.Integer(1)
    for N in range(1, n+1):
        for K in range(min(N, k), 0, -1):
            row[K] = sp.expand(row[K]+q**(N-K)*row[K-1])
    p = sp.Poly(row[k], q)
    return [int(p.nth(j)) for j in range(p.degree()+1)]


def inverse_qbin_near_zero(y, n: int, k: int, order: int = 5):
    """Inverse q(y) near y=1 using the partition coefficients."""
    c = qbinomial_coefficients(n, k)
    c2 = mp.mpf(c[2]) if len(c)>2 else 0
    c3 = mp.mpf(c[3]) if len(c)>3 else 0
    c4 = mp.mpf(c[4]) if len(c)>4 else 0
    c5 = mp.mpf(c[5]) if len(c)>5 else 0
    d = y-1
    ans = d
    if order >= 2:
        ans -= c2*d**2
    if order >= 3:
        ans += (2*c2**2-c3)*d**3
    if order >= 4:
        ans += (-5*c2**3+5*c2*c3-c4)*d**4
    if order >= 5:
        ans += (14*c2**4-21*c2**2*c3+6*c2*c4+3*c3**2-c5)*d**5
    return ans


def inverse_qbin_near_one(y, n: int, k: int, order: int = 3):
    """Inverse q(y) near q=1 in u=log(y/binomial(n,k))."""
    d = mp.mpf(k*(n-k))
    u = mp.log(y/mp.binomial(n, k))
    ans = 1+2*u/d
    if order >= 2:
        ans += (5-n)*u**2/(3*d**2)
    if order >= 3:
        ans += (n**2-4*n+7)*u**3/(9*d**3)
    return ans


def qgamma_log(x, q):
    """Log Jackson q-gamma for x>0 and 0<q<1."""
    return (1-x)*mp.log(1-q)+log_qpoch_inf(q, q)-log_qpoch_inf(q**x, q)


def qpsi(x, q):
    """q-digamma by a rapidly convergent Lambert series."""
    lq = mp.log(q)
    s = mp.mpf(0)
    r = q**x
    tol = mp.mpf(10)**(-(mp.mp.dps-15))
    for _ in range(2_000_000):
        term = r/(1-r)
        s += term
        r *= q
        if abs(term) < tol:
            return -mp.log(1-q)+lq*s
    raise RuntimeError("q-digamma series did not converge")


def qpolygamma(order: int, x, q):
    """Derivative^order of q-digamma, order>=1."""
    lq = mp.log(q)
    s = mp.mpf(0)
    r = q**x
    tol = mp.mpf(10)**(-(mp.mp.dps-15))
    for _ in range(2_000_000):
        term = mp.polylog(-order, r)
        s += term
        r *= q
        if abs(term) < tol:
            return lq**(order+1)*s
    raise RuntimeError("q-polygamma series did not converge")


def qgamma_minimum(q):
    """Unique positive minimizer x_q and minimum M_q."""
    lo, hi = mp.mpf("1e-8"), mp.mpf(2)
    while qpsi(hi, q) <= 0:
        hi *= 2
    for _ in range(220):
        mid = (lo+hi)/2
        if qpsi(mid, q) < 0:
            lo = mid
        else:
            hi = mid
    x0 = (lo+hi)/2
    return x0, mp.e**qgamma_log(x0, q)


def inverse_qgamma_minimum(delta, q, sign: int):
    """Puiseux inverse of log(Gamma_q/M_q)=delta."""
    x0, _ = qgamma_minimum(q)
    p1 = qpolygamma(1, x0, q)
    p2 = qpolygamma(2, x0, q)
    p3 = qpolygamma(3, x0, q)
    s = sign*mp.sqrt(2*delta/p1)-p2*delta/(3*p1**2)
    s += sign*mp.sqrt(2)*(5*p2**2-3*p1*p3)*delta**mp.mpf("1.5")/(36*p1**mp.mpf("3.5"))
    return x0+s


def continuous_qbinom_log(x, y, q):
    """q-gamma interpolation of a Gaussian coefficient, in logarithmic form."""
    return qgamma_log(x+1, q)-qgamma_log(y+1, q)-qgamma_log(x-y+1, q)


def inverse_continuous_qbinom_center(x, q, delta, sign: int):
    """Inverse lower parameter near the symmetric maximum y=x/2."""
    u = x/2+1
    p1 = qpolygamma(1, u, q)
    p3 = qpolygamma(3, u, q)
    s = sign*mp.sqrt(delta/p1)*(1-p3*delta/(24*p1**2))
    return x/2+s


def scaled_e_q(z, q):
    """Scaled q-exponential e_q((1-q)z)."""
    return mp.e**(-log_qpoch_inf((1-q)*z, q))


def inverse_scaled_e_q(y, q, order: int = 3):
    """Inverse argument of e_q((1-q)z) through (1-q)^3."""
    eps, L = 1-q, mp.log(y)
    ans = L
    if order >= 1:
        ans -= eps*L**2/4
    if order >= 2:
        ans += eps**2*L**2*(L-9)/72
    if order >= 3:
        ans -= eps**3*L**2*(L**2-8*L+36)/576
    return ans


def fmt(x, digits: int = 8) -> str:
    """Compact decimal/scientific notation suitable for a LaTeX table."""
    return mp.nstr(mp.re(x), digits, min_fixed=-3, max_fixed=4)


def solve_near(f: Callable, seed):
    """High-precision secant solve seeded by an asymptotic approximation."""
    companion = seed*(1+mp.mpf("1e-5"))+mp.mpf("1e-10")
    return mp.findroot(f, (seed, companion), solver="secant", tol=mp.mpf("1e-60"), maxsteps=100)


def numerical_rows():
    """Run representative checks; each row gives exact, approximation, error."""
    rows = []

    n, q, a0 = 7, mp.mpf("0.37"), mp.mpf("0.012")
    y = finite_qpoch(a0, q, n)
    aa = inverse_a_near_one(y, q, n)
    rows.append((r"$(a;q)_7$, $a\leftarrow y$, $q=0.37$", fmt(a0), fmt(aa), fmt(abs(aa-a0), 4)))

    n, q, j = 8, mp.mpf("0.61"), 3
    a0 = q**(-j)+mp.mpf("2e-7")
    y = finite_qpoch(a0, q, n)
    aa = inverse_a_at_root(y, q, n, j)
    rows.append((r"$(a;q)_8$, branch at $a=q^{-3}$", fmt(a0), fmt(aa), fmt(abs(aa-a0), 4)))

    n, a, q0 = 9, mp.mpf("0.42"), mp.mpf("0.025")
    y = finite_qpoch(a, q0, n)
    qq = inverse_q_near_zero(y, a)
    rows.append((r"$(0.42;q)_9$, $q\leftarrow y$, $q\sim0$", fmt(q0), fmt(qq), fmt(abs(qq-q0), 4)))

    n, a, q0 = 8, mp.mpf("0.31"), mp.mpf("0.975")
    y = finite_qpoch(a, q0, n)
    qq = mp.e**(-inverse_q_near_one_finite(y, a, n))
    rows.append((r"$(0.31;q)_8$, $q\leftarrow y$, $q\sim1$", fmt(q0), fmt(qq), fmt(abs(qq-q0), 4)))

    a, t0 = mp.mpf("0.30"), mp.mpf("0.035")
    q0 = mp.e**(-t0)
    y = mp.e**log_qpoch_inf(a, q0)
    qq = mp.e**(-inverse_inf_q_to_one(y, a))
    rows.append((r"$(0.30;q)_\infty$, radial $q\to1$", fmt(q0), fmt(qq), fmt(abs(qq-q0), 4)))

    q0 = -mp.e**(-t0)
    y = mp.e**log_qpoch_inf(a, q0)
    qq = -mp.e**(-inverse_inf_q_to_minus_one(y, a))
    rows.append((r"$(0.30;q)_\infty$, radial $q\to-1$", fmt(q0), fmt(qq), fmt(abs(qq-q0), 4)))

    n, k, q0 = 13, 5, mp.mpf("0.018")
    y = qbinomial_value(n, k, q0)
    qq = inverse_qbin_near_zero(y, n, k)
    rows.append((r"$\qbinom{13}{5}$, $q\sim0$", fmt(q0), fmt(qq), fmt(abs(qq-q0), 4)))

    n, k, q0 = 12, 5, mp.mpf("0.985")
    y = qbinomial_value(n, k, q0)
    qq = inverse_qbin_near_one(y, n, k)
    rows.append((r"$\qbinom{12}{5}$, $q\sim1$", fmt(q0), fmt(qq), fmt(abs(qq-q0), 4)))

    q0 = -1+mp.mpf("2e-7")
    y = qbinomial_value(n, k, q0)
    m, r = n//2, (k-1)//2
    slope = (m-r)*mp.binomial(m, r)
    qq = -1+y/slope
    rows.append((r"$\qbinom{12}{5}$, simple zero at $q=-1$", fmt(q0), fmt(qq), fmt(abs(qq-q0), 4)))

    q = mp.mpf("0.4")
    x0, M = qgamma_minimum(q)
    delta = mp.mpf("2e-5")
    target = mp.log(M)+delta
    for sign, name in [(-1, "left"), (1, "right")]:
        xa = inverse_qgamma_minimum(delta, q, sign)
        xe = solve_near(lambda x: qgamma_log(x, q)-target, xa)
        rows.append((rf"$\Gamma_{{0.4}}^{{-1}}$, {name} minimum branch", fmt(xe), fmt(xa), fmt(abs(xa-xe), 4)))

    q, x, delta = mp.mpf("0.5"), mp.mpf("7.3"), mp.mpf("2e-5")
    maxlog = continuous_qbinom_log(x, x/2, q)
    for sign, name in [(-1, "left"), (1, "right")]:
        ya = inverse_continuous_qbinom_center(x, q, delta, sign)
        ye = solve_near(lambda yy: maxlog-continuous_qbinom_log(x, yy, q)-delta, ya)
        rows.append((rf"$C_{{0.5}}(7.3,y)^{{-1}}$, {name} center branch", fmt(ye), fmt(ya), fmt(abs(ya-ye), 4)))

    q, z0 = mp.mpf("0.97"), mp.mpf("0.8")
    y = scaled_e_q(z0, q)
    zz = inverse_scaled_e_q(y, q)
    rows.append((r"$e_q((1-q)z)^{-1}$, $q=0.97$", fmt(z0), fmt(zz), fmt(abs(zz-z0), 4)))
    return rows


def write_tables(rows: Sequence[tuple[str, str, str, str]]):
    """Write both a LaTeX longtable and a human-readable text log."""
    tex = [
        "% Generated by inverse_q_analogs_experiments.py.",
        r"\begin{longtable}{@{}p{0.43\textwidth}rrr@{}}",
        r"\caption{Representative high-precision checks of the inverse expansions. The final column is absolute error.\label{tab:numerical-checks}}\\",
        r"\toprule",
        r"Experiment & exact & asymptotic & error\\",
        r"\midrule",
        r"\endfirsthead",
        r"\toprule",
        r"Experiment & exact & asymptotic & error\\",
        r"\midrule",
        r"\endhead",
    ]
    for label, exact, approx, error in rows:
        tex.append(f"{label} & ${exact}$ & ${approx}$ & ${error}$\\\\")
    tex += [r"\bottomrule", r"\end{longtable}", ""]
    (OUTPUT / "numerical_results.tex").write_text(
        "\n".join(tex), encoding="utf-8", newline="\n"
    )

    width = max(len(r[0]) for r in rows)
    txt = ["Numerical checks for inverse q-analogue expansions", "="*51, "", "All calculations use 80 decimal digits; the displayed error is absolute.", ""]
    for label, exact, approx, error in rows:
        txt.append(f"{label:<{width}}  exact={exact:>14}  approx={approx:>14}  error={error}")
    txt.append("")
    (OUTPUT / "numerical_results.txt").write_text(
        "\n".join(txt), encoding="utf-8", newline="\n"
    )


def make_branch_figure():
    """Real branch atlas of (a;0.72)_5: roots and one critical point per gap."""
    q, n = 0.72, 5
    roots = [q**(-j) for j in range(n)]
    critical = []
    for left, right in zip(roots[:-1], roots[1:]):
        lo = left+1e-9*(right-left)
        hi = right-1e-9*(right-left)
        for _ in range(100):
            mid = (lo+hi)/2
            val = sum(1/(mid-r) for r in roots)
            if val > 0:
                lo = mid
            else:
                hi = mid
        critical.append((lo+hi)/2)
    xs = [-0.6+(roots[-1]+1.1)*i/1800 for i in range(1801)]
    ys = [float(finite_qpoch(mp.mpf(x), mp.mpf(q), n)) for x in xs]
    cy = [float(finite_qpoch(mp.mpf(x), mp.mpf(q), n)) for x in critical]
    plt.figure(figsize=(8.0, 4.8))
    plt.plot(xs, ys, linewidth=1.3, label=r"$(a;0.72)_5$")
    plt.axhline(0, linewidth=0.8)
    plt.scatter(roots, [0]*len(roots), marker="o", label="simple zeros")
    plt.scatter(critical, cy, marker="x", s=55, label="critical points")
    plt.ylim(-0.35, 8.0)
    plt.xlabel(r"active parameter $a$")
    plt.ylabel(r"level $y$")
    plt.title("Real branch atlas for a finite q-Pochhammer polynomial")
    plt.legend(loc="upper right")
    plt.tight_layout()
    plt.savefig(FIGURES / "finite_pochhammer_branch_atlas.pdf")
    plt.close()


def periodic_residual(rho: float, q: float) -> float:
    """Theta-type periodic residual in log((-x;q)_infinity)."""
    tau = -math.log(q)
    r = math.exp(rho)
    theta = mp.qp(-r, q)*mp.qp(-q/r, q)
    return float(mp.log(theta)-rho/2-rho**2/(2*tau))


def make_periodic_figure():
    q = 0.5
    tau = -math.log(q)
    rhos = [tau*i/500 for i in range(501)]
    vals = [periodic_residual(r, q) for r in rhos]
    plt.figure(figsize=(7.7, 4.5))
    plt.plot(rhos, vals, linewidth=1.4)
    plt.xlabel(r"phase $\rho=\log x\; (\mathrm{mod}\; -\log q)$")
    plt.ylabel(r"$\Psi_q(\rho)$")
    plt.title("Log-periodic correction in the large-negative-a inverse")
    plt.tight_layout()
    plt.savefig(FIGURES / "log_periodic_correction.pdf")
    plt.close()


def make_qgamma_figure():
    q = mp.mpf("0.4")
    x0, M = qgamma_minimum(q)
    delta = mp.mpf("0.08")
    level = mp.log(M)+delta
    xl = solve_near(lambda x: qgamma_log(x, q)-level, x0-mp.mpf("0.4"))
    xr = solve_near(lambda x: qgamma_log(x, q)-level, x0+mp.mpf("0.4"))
    xs = [0.12+(6.0-0.12)*i/900 for i in range(901)]
    ys = [float(qgamma_log(mp.mpf(x), q)) for x in xs]
    plt.figure(figsize=(7.8, 4.7))
    plt.plot(xs, ys, linewidth=1.35, label=r"$\log\Gamma_{0.4}(x)$")
    plt.axhline(float(level), linewidth=0.9, linestyle="--", label="chosen level")
    plt.scatter([float(x0)], [float(mp.log(M))], marker="x", s=60, label="unique minimum")
    plt.scatter([float(xl), float(xr)], [float(level), float(level)], marker="o", label="two inverse branches")
    plt.xlabel(r"$x$")
    plt.ylabel(r"$\log\Gamma_{0.4}(x)$")
    plt.title("Two real branches of the inverse q-gamma function")
    plt.legend(loc="upper right")
    plt.tight_layout()
    plt.savefig(FIGURES / "qgamma_inverse_branches.pdf")
    plt.close()


def main():
    OUTPUT.mkdir(parents=True, exist_ok=True)
    FIGURES.mkdir(parents=True, exist_ok=True)
    rows = numerical_rows()
    write_tables(rows)
    make_branch_figure()
    make_periodic_figure()
    make_qgamma_figure()
    print((OUTPUT / "numerical_results.txt").read_text(encoding="utf-8"))


if __name__ == "__main__":
    main()
