#!/usr/bin/env python3
"""Reproducible experiments for the Fabius/Rvachev frontier report.

This program studies the symmetric geometric-uniform random series

    Y_q = sum_{k>=1} q^k U_k,        U_k ~ Uniform[-1,1] independently.

For q=1/2 its probability density is Rvachev's up-function on [-1,1].
The script computes exact classical, free, and Boolean cumulants; an exact
Hankel certificate excluding free infinite divisibility; a parameter-uniform
q-family obstruction; Jacobi-parameter experiments; finite sinc-product
approximants; and endpoint diagnostics.

Exact claims use Python Fraction or SymPy integer/rational arithmetic.
Numerical tables use mpmath with explicit high precision.  The code is
self-contained and deterministic.
"""

from __future__ import annotations

import argparse
import csv
import math
from fractions import Fraction
from pathlib import Path
from typing import List, Sequence

import mpmath as mp
import sympy as sp
import matplotlib.pyplot as plt


# ---------------------------------------------------------------------------
# Truncated power-series utilities
# ---------------------------------------------------------------------------

def conv(a: Sequence, b: Sequence, degree: int):
    """Multiply coefficient lists and truncate after ``degree``."""
    zero = a[0] * 0 if a else b[0] * 0
    out = [zero for _ in range(degree + 1)]
    for i, ai in enumerate(a):
        if i > degree or ai == 0:
            continue
        for j in range(min(len(b) - 1, degree - i) + 1):
            if b[j] != 0:
                out[i + j] += ai * b[j]
    return out


def moments_from_even_classical(kappa: Sequence, nmax: int):
    """Compressed even-moment recurrence.

    ``kappa[j]`` means the classical cumulant kappa_{2j}; the return value
    ``a[n]`` is m_{2n}=E[X^{2n}].  The recurrence follows from the standard
    exponential Bell-polynomial moment/cumulant identity.
    """
    one = kappa[1] * 0 + 1
    a = [one] + [one * 0 for _ in range(nmax)]
    for n in range(1, nmax + 1):
        a[n] = sum(
            math.comb(2 * n - 1, 2 * j - 1) * kappa[j] * a[n - j]
            for j in range(1, n + 1)
        )
    return a


def free_from_even_moments(a: Sequence, nmax: int):
    r"""Compressed free cumulants rho_n=r_{2n}.

    For a symmetric law with A(t)=sum a_n t^n, the moment/free-cumulant
    equation is

        A(t) = 1 + sum_{j>=1} rho_j t^j A(t)^{2j}.

    It is triangular in rho_j.  Powers A^{2j} are cached.
    """
    A = list(a[: nmax + 1])
    A2 = conv(A, A, nmax)
    powers = [[A[0] * 0 + 1] + [A[0] * 0 for _ in range(nmax)]]
    for _ in range(1, nmax + 1):
        powers.append(conv(powers[-1], A2, nmax))

    rho = [A[0] * 0 for _ in range(nmax + 1)]
    for n in range(1, nmax + 1):
        rho[n] = A[n] - sum(rho[j] * powers[j][n - j] for j in range(1, n))
    return rho


def boolean_from_even_moments(a: Sequence, nmax: int):
    r"""Compressed Boolean cumulants eta_n=b_{2n} from B=1-A^{-1}."""
    eta = [a[0] * 0 for _ in range(nmax + 1)]
    for n in range(1, nmax + 1):
        eta[n] = a[n] - sum(eta[j] * a[n - j] for j in range(1, n))
    return eta


# ---------------------------------------------------------------------------
# Exact dyadic law
# ---------------------------------------------------------------------------

def dyadic_classical(nmax: int) -> List[Fraction]:
    r"""Classical cumulants of Y_{1/2}.

        kappa_{2n} = 4^n B_{2n} / (2n(4^n-1)).
    """
    out = [Fraction(0)] * (nmax + 1)
    for n in range(1, nmax + 1):
        B = sp.bernoulli(2 * n)
        b = Fraction(int(B.p), int(B.q))
        out[n] = Fraction(4**n, 2 * n * (4**n - 1)) * b
    return out


def decimal(x: Fraction, digits: int = 24) -> str:
    mp.mp.dps = digits + 10
    return mp.nstr(mp.mpf(x.numerator) / x.denominator, digits)


def exact_dyadic_tables(outdir: Path, nmax: int):
    kappa = dyadic_classical(nmax)
    moments = moments_from_even_classical(kappa, nmax)
    free = free_from_even_moments(moments, nmax)
    boolean = boolean_from_even_moments(moments, nmax)

    with (outdir / "dyadic_cumulants.csv").open("w", newline="", encoding="utf-8") as fh:
        w = csv.writer(fh)
        w.writerow([
            "n", "m_2n_exact", "classical_kappa_2n_exact",
            "free_r_2n_exact", "boolean_b_2n_exact",
            "free_decimal", "boolean_decimal",
        ])
        for n in range(1, nmax + 1):
            w.writerow([
                n, str(moments[n]), str(kappa[n]), str(free[n]), str(boolean[n]),
                decimal(free[n]), decimal(boolean[n]),
            ])

    all_positive = all(free[n] > 0 for n in range(1, nmax + 1))
    with (outdir / "dyadic_exact_summary.txt").open("w", encoding="utf-8") as fh:
        fh.write(f"Exact positivity r_{{2n}}>0 checked for 1<=n<={nmax}: {all_positive}\n")
        fh.write("\nFirst twelve exact values:\n")
        for n in range(1, min(nmax, 12) + 1):
            fh.write(
                f"n={n}: m_2n={moments[n]}; kappa_2n={kappa[n]}; "
                f"r_2n={free[n]}; b_2n={boolean[n]}\n"
            )
    if not all_positive:
        raise RuntimeError("Unexpected nonpositive dyadic free cumulant.")
    return kappa, moments, free, boolean


# ---------------------------------------------------------------------------
# Exact free-infinite-divisibility obstruction
# ---------------------------------------------------------------------------

def det3(M):
    return (
        M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
        - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
        + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0])
    )


def dyadic_fid_certificate(outdir: Path, free: Sequence[Fraction]):
    # Y_{1/2} has variance 1/9.  X=3Y therefore has variance one, and
    # c_{2n}=3^{2n}r_{2n}=9^n r_{2n}.
    c = [Fraction(0)] + [free[n] * 9**n for n in range(1, len(free))]
    H = [[c[i + j] for j in range(1, 4)] for i in range(1, 4)]
    D = det3(H)
    v = [Fraction(3), Fraction(-4), Fraction(1)]
    Q = sum(v[i] * H[i][j] * v[j] for i in range(3) for j in range(3))

    expected_D = Fraction(
        -110020031172003013633803653,
        3288379747918347944189453125,
    )
    expected_Q = Fraction(-108624693817191, 404291747234375)
    assert D == expected_D and Q == expected_Q

    with (outdir / "dyadic_free_ID_certificate.txt").open("w", encoding="utf-8") as fh:
        fh.write("Variance-one shifted free-cumulant block H:\n")
        for row in H:
            fh.write("[" + ", ".join(str(x) for x in row) + "]\n")
        fh.write(f"\ndet(H)={D}\n")
        fh.write(f"det(H) decimal={decimal(D, 35)}\n")
        fh.write("\nFor v=(3,-4,1), corresponding to p(x)=3x^2-4x^4+x^6:\n")
        fh.write(f"v^T H v={Q}\n")
        fh.write(f"v^T H v decimal={decimal(Q, 35)}\n")
    return c, H, D, Q


# ---------------------------------------------------------------------------
# Exact q-family certificate (s=q^2)
# ---------------------------------------------------------------------------

P30_COEFFICIENTS = [
    588031288239582935, 1365452791577583829, 3106555208559680768,
    3802457057684963283, 6277464174324435942, 4570485884957325545,
    5387333540324201540, 2656469118337756915, 4423316345984162365,
    2006573378166739986, 3586241741057425853, 2149494971059201511,
    944899121577446453, 948703157726602056, 710585546823441352,
    260832096100041918, 111335265126207640, -3112870344293064,
    47450105349899789, 17451160220542367, 6462787608357749,
    -1567422948953118, 500704487135269, -174414460271621,
    -25423927396444, -4962354733999, -309530241402,
    -32161726341, 154644128, 236797, -1,
]

ROOT_INTERVALS = [
    (Fraction(6261, 1486660088), Fraction(7013, 1665220763)),
    (Fraction(17338229, 3019459543), Fraction(18557046, 3231717013)),
    (Fraction(385546279, 1406842461), Fraction(219810848, 802080713)),
]


def poly_eval_mp(coefficients, x):
    value = mp.mpf(0)
    for coefficient in coefficients:
        value = value * x + coefficient
    return value


def bisect_root(coefficients, interval, digits=60):
    mp.mp.dps = digits + 20
    left, right = interval
    a = mp.mpf(left.numerator) / left.denominator
    b = mp.mpf(right.numerator) / right.denominator
    fa, fb = poly_eval_mp(coefficients, a), poly_eval_mp(coefficients, b)
    if fa * fb >= 0:
        raise RuntimeError("Root-isolating interval has no sign change.")
    for _ in range(4 * digits):
        m = (a + b) / 2
        fm = poly_eval_mp(coefficients, m)
        if fa * fm <= 0:
            b, fb = m, fm
        else:
            a, fa = m, fm
    return (a + b) / 2


def sturm_variations(sturm, symbol, point):
    signs = []
    for p in sturm:
        val = sp.sign(sp.factor(p.subs(symbol, point)))
        if val != 0:
            signs.append(int(val))
    return sum(a != b for a, b in zip(signs, signs[1:]))


def q_family_certificate(outdir: Path):
    s = sp.symbols("s", positive=True)
    c = [sp.Integer(0)] * 7
    c[1] = 1
    c[2] = (11 * s - 1) / (5 * (1 + s))
    c[3] = 2 * (379 * s**3 + 20 * s**2 + 20 * s + 1) / (
        35 * (1 + s) * (1 + s + s**2)
    )
    c[4] = 3 * (
        24359 * s**6 + 4221 * s**5 + 4579 * s**4 + 4242 * s**3
        + 379 * s**2 + 21 * s - 1
    ) / (175 * (1 + s)**2 * (1 + s**2) * (1 + s + s**2))
    P10 = (
        2437711 * s**10 + 646150 * s**9 + 757701 * s**8 + 780549 * s**7
        + 782870 * s**6 + 159568 * s**5 + 136730 * s**4 + 25179 * s**3
        + 2331 * s**2 + 10 * s + 1
    )
    c[5] = 2 * P10 / (
        385 * (1 + s)**2 * (1 + s**2) * (1 + s + s**2)
        * (1 + s + s**2 + s**3 + s**4)
    )
    P12 = (
        239971210481 * s**15 + 79887931849 * s**14 + 98139745702 * s**13
        + 106474515277 * s**12 + 123041556053 * s**11
        + 114309825775 * s**10 + 52750980414 * s**9 + 35665790305 * s**8
        + 27408293365 * s**7 + 10846922526 * s**6 + 2506486435 * s**5
        + 1249569737 * s**4 + 82945993 * s**3 + 5673358 * s**2
        + 3421 * s - 691
    )
    c[6] = 2 * P12 / (
        875875 * (1 + s)**3 * (1 + s**2) * (1 - s + s**2)
        * (1 + s + s**2)**2 * (1 + s + s**2 + s**3 + s**4)
    )
    c = [sp.factor(sp.cancel(x)) if i else x for i, x in enumerate(c)]

    poly = sp.Poly.from_list(P30_COEFFICIENTS, gens=s, domain=sp.ZZ)
    denominator = (
        11802415625 * (1 + s)**6 * (1 + s**2)**3 * (1 - s + s**2)
        * (1 + s + s**2)**4 * (1 + s + s**2 + s**3 + s**4)**2
    )
    D3 = poly.as_expr() / denominator
    roots = [bisect_root(P30_COEFFICIENTS, I, 60) for I in ROOT_INTERVALS]

    sturm = sp.sturm(poly.as_expr(), s)
    alpha_left = sp.Rational(ROOT_INTERVALS[-1][0].numerator, ROOT_INTERVALS[-1][0].denominator)
    alpha_right = sp.Rational(ROOT_INTERVALS[-1][1].numerator, ROOT_INTERVALS[-1][1].denominator)
    counts = {
        "roots_(0,1)": sturm_variations(sturm, s, 0) - sturm_variations(sturm, s, 1),
        "roots_(1/11,alpha_left)": sturm_variations(sturm, s, sp.Rational(1, 11)) - sturm_variations(sturm, s, alpha_left),
        "roots_(alpha_left,alpha_right)": sturm_variations(sturm, s, alpha_left) - sturm_variations(sturm, s, alpha_right),
        "roots_(alpha_right,1)": sturm_variations(sturm, s, alpha_right) - sturm_variations(sturm, s, 1),
    }
    assert counts == {
        "roots_(0,1)": 3,
        "roots_(1/11,alpha_left)": 0,
        "roots_(alpha_left,alpha_right)": 1,
        "roots_(alpha_right,1)": 0,
    }

    with (outdir / "q_family_symbolic_results.txt").open("w", encoding="utf-8") as fh:
        for n in range(1, 7):
            fh.write(f"c_{2*n}(s)={sp.sstr(c[n])}\n\n")
        fh.write("D_3(s)=P_30(s)/denominator, with coefficient list (descending):\n")
        fh.write(str(P30_COEFFICIENTS) + "\n\n")
        fh.write("Positive root-isolating intervals and numerical roots:\n")
        for I, root in zip(ROOT_INTERVALS, roots):
            fh.write(f"{I}: {mp.nstr(root, 65)}\n")
        fh.write(f"sqrt(alpha)={mp.nstr(mp.sqrt(roots[-1]), 65)}\n\n")
        fh.write("Exact Sturm counts:\n")
        for key, value in counts.items():
            fh.write(f"{key}={value}\n")
        fh.write(f"\nD_3(1/4)={sp.factor(D3.subs(s, sp.Rational(1,4)))}\n")

    return s, c, D3, roots


# ---------------------------------------------------------------------------
# Numerical leading shifted-Hankel thresholds
# ---------------------------------------------------------------------------
_BERNOULLI_CACHE = {}


def bernoulli_mp(n: int):
    if n not in _BERNOULLI_CACHE:
        B = sp.bernoulli(n)
        _BERNOULLI_CACHE[n] = (int(B.p), int(B.q))
    p, q = _BERNOULLI_CACHE[n]
    return mp.mpf(p) / q


def standardized_classical_mp(s, nmax):
    # Divide the unnormalised kappa_{2n} by kappa_2^n.
    out = [mp.mpf(0)] * (nmax + 1)
    for n in range(1, nmax + 1):
        out[n] = (
            mp.power(3, n) * mp.power(2, 2 * n) * bernoulli_mp(2 * n)
            / (2 * n) * mp.power(1 - s, n) / (1 - mp.power(s, n))
        )
    return out


def leading_even_hankel_det(s, block_size):
    nmax = 2 * block_size
    kappa = standardized_classical_mp(s, nmax)
    moments = moments_from_even_classical(kappa, nmax)
    free = free_from_even_moments(moments, nmax)
    H = mp.matrix(block_size)
    for i in range(block_size):
        for j in range(block_size):
            H[i, j] = free[i + j + 2]
    return mp.det(H)


def largest_sign_change_root(block_size, left, right, scans=80):
    xs = [mp.mpf(left) + (mp.mpf(right) - left) * k / scans for k in range(scans + 1)]
    vals = [leading_even_hankel_det(x, block_size) for x in xs]
    brackets = []
    for k in range(scans):
        if vals[k] * vals[k + 1] < 0:
            brackets.append((xs[k], xs[k + 1]))
    if not brackets:
        raise RuntimeError(f"No sign change for block {block_size} in [{left},{right}].")
    a, b = brackets[-1]
    fa = leading_even_hankel_det(a, block_size)
    for _ in range(90):
        m = (a + b) / 2
        fm = leading_even_hankel_det(m, block_size)
        if fa * fm <= 0:
            b = m
        else:
            a, fa = m, fm
    return (a + b) / 2


def hankel_thresholds(outdir: Path, max_block=10):
    mp.mp.dps = 80
    brackets = {
        1: (0.07, 0.13), 2: (0.16, 0.24), 3: (0.24, 0.31),
        4: (0.29, 0.35), 5: (0.32, 0.38), 6: (0.34, 0.40),
        7: (0.35, 0.41), 8: (0.36, 0.42), 9: (0.36, 0.42),
        10: (0.36, 0.42),
    }
    rows = []
    for m in range(1, max_block + 1):
        root = largest_sign_change_root(m, *brackets.get(m, (0.34, 0.45)))
        rows.append((m, root, mp.sqrt(root)))
    with (outdir / "leading_hankel_thresholds.csv").open("w", newline="", encoding="utf-8") as fh:
        w = csv.writer(fh)
        w.writerow(["block_size", "s_root", "q_root"])
        for m, sr, qr in rows:
            w.writerow([m, mp.nstr(sr, 40), mp.nstr(qr, 40)])
    return rows


# ---------------------------------------------------------------------------
# Jacobi-parameter increment experiment
# ---------------------------------------------------------------------------

def s_fraction_moments(nmax: int):
    r"""Weighted-Dyck-path moments of an S-fraction.

      A(t)=1/(1-beta_1 t/(1-beta_2 t/(...))).

    A down-step from height h carries beta_h.  Dynamic programming produces
    the moment polynomial without enumerating every path explicitly.
    """
    beta = sp.symbols("beta1:" + str(2 * nmax + 1))
    state = {0: sp.Integer(1)}
    moments = [sp.Integer(1)]
    for step in range(1, 2 * nmax + 1):
        new = {}
        for height, weight in state.items():
            new[height + 1] = new.get(height + 1, 0) + weight
            if height > 0:
                new[height - 1] = new.get(height - 1, 0) + weight * beta[height - 1]
        state = new
        if step % 2 == 0:
            moments.append(sp.expand(state.get(0, 0)))
    return beta, moments


def jacobi_increment_experiment(outdir: Path, nmax=8):
    beta, moments = s_fraction_moments(nmax)
    free = free_from_even_moments(moments, nmax)
    b1 = sp.symbols("beta1")
    delta = sp.symbols("Delta1:" + str(nmax))
    substitutions = {beta[0]: b1}
    for j in range(1, nmax):
        substitutions[beta[j]] = b1 + sum(delta[:j])

    rows = []
    formulas = {}
    for n in range(2, nmax + 1):
        expr = sp.expand(free[n].subs(substitutions))
        poly = sp.Poly(expr, b1, *delta[: n - 1])
        nonnegative = all(coef.is_Integer and coef >= 0 for coef in poly.coeffs())
        rows.append((2 * n, len(poly.terms()), nonnegative))
        formulas[n] = sp.factor(expr)
        if not nonnegative:
            raise RuntimeError(f"Negative Jacobi-increment coefficient at r_{2*n}.")

    with (outdir / "jacobi_increment_verification.csv").open("w", newline="", encoding="utf-8") as fh:
        w = csv.writer(fh)
        w.writerow(["free_cumulant_order", "monomial_count", "all_coefficients_nonnegative"])
        w.writerows(rows)
    with (outdir / "jacobi_increment_formulas.txt").open("w", encoding="utf-8") as fh:
        fh.write("Substitution beta_j=beta_1+Delta_1+...+Delta_{j-1}.\n\n")
        for n in range(2, min(4, nmax) + 1):
            fh.write(f"r_{2*n}={sp.sstr(formulas[n])}\n\n")
        fh.write("Verification summary:\n")
        for order, terms, ok in rows:
            fh.write(f"r_{order}: monomials={terms}, all_nonnegative={ok}\n")
    return rows, formulas


# ---------------------------------------------------------------------------
# Finite dyadic sinc-product approximants
# ---------------------------------------------------------------------------

def finite_dyadic_polynomials(outdir: Path, nmax=6):
    r"""Cumulants of Y^(N)=sum_{k=1}^N 2^{-k}U_k as Q=4^{-N} polynomials."""
    Q = sp.symbols("Q")
    base = dyadic_classical(nmax)
    kappa = [sp.Integer(0)] * (nmax + 1)
    for n in range(1, nmax + 1):
        b = sp.Rational(base[n].numerator, base[n].denominator)
        kappa[n] = b * (1 - Q**n)
    moments = moments_from_even_classical(kappa, nmax)
    free = free_from_even_moments(moments, nmax)
    boolean = boolean_from_even_moments(moments, nmax)

    with (outdir / "finite_dyadic_approximant_polynomials.txt").open("w", encoding="utf-8") as fh:
        fh.write("Q=4^{-N}. Every expression below is exact.\n\n")
        for n in range(1, nmax + 1):
            fr = sp.factor(free[n])
            bo = sp.factor(boolean[n])
            assert sp.degree(fr, Q) <= n and sp.degree(bo, Q) <= n
            fh.write(f"r_{2*n}^(N)={sp.sstr(fr)}\n")
            fh.write(f"b_{2*n}^(N)={sp.sstr(bo)}\n")
            fh.write(f"deg_Q(r)={sp.degree(fr,Q)}, deg_Q(b)={sp.degree(bo,Q)}\n")
            fh.write(f"[Q]r={sp.expand(fr).coeff(Q,1)}, [Q]b={sp.expand(bo).coeff(Q,1)}\n\n")
    return Q, free, boolean


# ---------------------------------------------------------------------------
# Stable endpoint diagnostics
# ---------------------------------------------------------------------------

def dyadic_moments_fixed_point(nmax: int, dps=120):
    r"""Stable positive recurrence from Y=(Y'+U)/2.

      (4^n-1)m_{2n}=sum_{k=1}^n binom(2n,2k)m_{2n-2k}/(2k+1).
    """
    mp.mp.dps = dps
    a = [mp.mpf(1)] + [mp.mpf(0) for _ in range(nmax)]
    for n in range(1, nmax + 1):
        total = mp.fsum(
            math.comb(2 * n, 2 * k) * a[n - k] / (2 * k + 1)
            for k in range(1, n + 1)
        )
        a[n] = total / (mp.power(4, n) - 1)
    return a


def endpoint_diagnostics(outdir: Path, exact_free, nmax=200):
    a = dyadic_moments_fixed_point(nmax, 140)
    b = boolean_from_even_moments(a, nmax)
    S = mp.fsum(a)
    Sinv2 = 1 / S**2
    Aprime = mp.fsum(n * a[n] for n in range(1, nmax + 1))
    chosen = [n for n in [5, 10, 20, 40, 60, 80, 100, 150, 200] if n <= nmax]

    with (outdir / "endpoint_diagnostics.csv").open("w", newline="", encoding="utf-8") as fh:
        w = csv.writer(fh)
        w.writerow(["n", "m_2n", "b_2n", "b_over_m", "m_nth_root", "b_nth_root"])
        for n in chosen:
            w.writerow([
                n, mp.nstr(a[n], 40), mp.nstr(b[n], 40), mp.nstr(b[n] / a[n], 40),
                mp.nstr(mp.root(a[n], n), 40), mp.nstr(mp.root(b[n], n), 40),
            ])
    with (outdir / "endpoint_summary.txt").open("w", encoding="utf-8") as fh:
        fh.write(f"N={nmax}\nS_N={mp.nstr(S, 70)}\nS_N^(-2)={mp.nstr(Sinv2,70)}\n")
        fh.write(f"A_N'(1)={mp.nstr(Aprime,70)}\n\n")
        for n in chosen:
            fh.write(f"n={n}: b_2n/m_2n={mp.nstr(b[n]/a[n],50)}\n")

    free_roots = []
    for n in range(1, len(exact_free)):
        x = mp.mpf(exact_free[n].numerator) / exact_free[n].denominator
        free_roots.append((n, mp.root(x, n)))
    return a, b, S, Sinv2, free_roots


# ---------------------------------------------------------------------------
# Figures
# ---------------------------------------------------------------------------

def make_figures(figdir: Path, thresholds, a, b, Sinv2, free_roots, s_symbol, c):
    figdir.mkdir(parents=True, exist_ok=True)

    # Leading-Hankel thresholds.
    plt.figure(figsize=(7.1, 4.5))
    plt.plot([m for m, _, _ in thresholds], [float(q) for _, _, q in thresholds], marker="o")
    plt.axhline(0.5, linestyle="--", linewidth=1)
    plt.xlabel("leading shifted-Hankel block size")
    plt.ylabel(r"largest detected threshold $q=\sqrt{s}$")
    plt.title("Necessary free-infinite-divisibility thresholds")
    plt.grid(alpha=0.25)
    plt.tight_layout()
    plt.savefig(figdir / "hankel_thresholds.pdf")
    plt.savefig(figdir / "hankel_thresholds.png", dpi=180)
    plt.close()

    # Endpoint/root diagnostics.
    ns = list(range(2, min(120, len(a) - 1) + 1))
    plt.figure(figsize=(7.1, 4.7))
    plt.plot(ns, [float(mp.root(a[n], n)) for n in ns], label=r"$m_{2n}^{1/n}$")
    plt.plot(ns, [float(mp.root(b[n], n)) for n in ns], label=r"$b_{2n}^{1/n}$")
    fr_n = [n for n, _ in free_roots if n >= 2]
    fr_v = [float(x) for n, x in free_roots if n >= 2]
    plt.plot(fr_n, fr_v, label=r"$r_{2n}^{1/n}$")
    plt.axhline(float(Sinv2), linestyle="--", linewidth=1, label=r"$S^{-2}$")
    plt.xlabel("compressed order n")
    plt.ylabel("n-th root")
    plt.title("Moment, Boolean, and free-cumulant root trends")
    plt.legend()
    plt.grid(alpha=0.25)
    plt.tight_layout()
    plt.savefig(figdir / "cumulant_root_trends.pdf")
    plt.savefig(figdir / "cumulant_root_trends.png", dpi=180)
    plt.close()

    # Low-order q-family obstruction.
    import numpy as np
    f = sp.lambdify(s_symbol, c[2], "numpy")
    ss = np.linspace(0.0001, 0.55, 1000)
    plt.figure(figsize=(7.1, 4.5))
    plt.plot(np.sqrt(ss), f(ss))
    plt.axhline(0, linewidth=1)
    plt.axvline(math.sqrt(1 / 11), linestyle="--", linewidth=1)
    plt.xlabel(r"geometric parameter $q=\sqrt{s}$")
    plt.ylabel(r"variance-normalized $c_4(s)$")
    plt.title("First free-cumulant obstruction in the geometric-uniform family")
    plt.grid(alpha=0.25)
    plt.tight_layout()
    plt.savefig(figdir / "q_c4_obstruction.pdf")
    plt.savefig(figdir / "q_c4_obstruction.png", dpi=180)
    plt.close()


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def _common_cli_arguments(parser):
    parser.add_argument("--output-dir", type=Path, default=Path("results"))
    parser.add_argument("--figure-dir", type=Path, default=Path("figures"))
    parser.add_argument("--exact-order", type=int, default=60)
    parser.add_argument("--endpoint-order", type=int, default=200)
    parser.add_argument("--hankel-max", type=int, default=10)
    parser.add_argument("--jacobi-order", type=int, default=8)
    parser.add_argument("--finite-order", type=int, default=6)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--task",
        choices=["analysis", "jacobi", "finite"],
        default="analysis",
        help=(
            "Select an isolated reproducibility stage.  Run the three stages as "
            "separate commands listed in README.md."
        ),
    )
    _common_cli_arguments(parser)
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    args.figure_dir.mkdir(parents=True, exist_ok=True)

    if args.task == "jacobi":
        print("[jacobi] Jacobi-increment expansion", flush=True)
        jacobi_increment_experiment(args.output_dir, args.jacobi_order)
        print("[jacobi] complete", flush=True)
        return

    if args.task == "finite":
        print("[finite] finite dyadic approximants", flush=True)
        finite_dyadic_polynomials(args.output_dir, args.finite_order)
        print("[finite] complete", flush=True)
        return

    print("[analysis 1/6] exact dyadic cumulants", flush=True)
    _, _, free, _ = exact_dyadic_tables(args.output_dir, args.exact_order)
    print("[analysis 2/6] exact free-ID certificate", flush=True)
    dyadic_fid_certificate(args.output_dir, free)
    print("[analysis 3/6] exact q-family/Sturm certificate", flush=True)
    s, c, _, _ = q_family_certificate(args.output_dir)
    print("[analysis 4/6] leading-Hankel numerical hierarchy", flush=True)
    thresholds = hankel_thresholds(args.output_dir, args.hankel_max)
    print("[analysis 5/6] endpoint diagnostics", flush=True)
    a, b, _, Sinv2, free_roots = endpoint_diagnostics(args.output_dir, free, args.endpoint_order)
    print("[analysis 6/6] figures", flush=True)
    make_figures(args.figure_dir, thresholds, a, b, Sinv2, free_roots, s, c)
    print("[analysis] complete", flush=True)


if __name__ == "__main__":
    main()
