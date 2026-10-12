#!/usr/bin/env python3
"""Research verification for sharp late coefficients of a Lambert inverse.

Run from the package root:
    python verification/verify.py

The default run evaluates the COMPLETE finite Lagrange sum, every k <= n,
through n = 1025.  It uses factorial-normalized positive convolutions, so
factorials do not overflow the recorded long-double arithmetic.  An independent
80-digit mpmath computation and exact rational formal calculations cross-check
the implementation.  Floating-point diagnostics are NOT interval certificates.
The mathematical theorems rely on the article's proofs, not these finite tests.
"""
from __future__ import annotations

import argparse
import csv
from fractions import Fraction
import json
import math
import platform
from pathlib import Path
import sys
import time
from typing import Any

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np
import sympy as sp

LD = np.longdouble
CD = np.clongdouble


def as_ld(x: Any) -> LD:
    return LD(mp.nstr(x, 70))


def as_cd(x: Any) -> CD:
    return CD(as_ld(mp.re(x))) + CD(1j) * CD(as_ld(mp.im(x)))


def ld_string(x: Any) -> str:
    return np.format_float_scientific(LD(x), precision=25, unique=False, trim="k")


def complex_record(z: Any) -> dict[str, str]:
    return {"real": ld_string(np.real(z)), "imag": ld_string(np.imag(z))}


def mp_from_cd(z: Any) -> Any:
    return mp.mpc(ld_string(np.real(z)), ld_string(np.imag(z)))


def rational_record(q: Fraction) -> dict[str, str]:
    return {"numerator": str(q.numerator), "denominator": str(q.denominator)}


def exact_checks(order: int) -> tuple[dict[str, Any], list[Any]]:
    """Finite Lagrange formula versus independent implicit recurrence."""
    u = sp.Symbol("u")
    zero = sp.Poly(0, u, domain=sp.QQ)
    one = sp.Poly(1, u, domain=sp.QQ)
    up = sp.Poly(u, u, domain=sp.QQ)
    r = [sp.S.Zero] + [(-1) ** n * sp.zeta(1 - n) ** 2 / sp.factorial(n)
                       for n in range(1, order + 1)]
    powers = [[sp.S.One] + [sp.S.Zero] * order]
    for k in range(1, order + 1):
        powers.append([sum(powers[-1][j] * r[n-j] for j in range(n + 1))
                       for n in range(order + 1)])
    lagrange = [zero]
    assertions = 0
    for n in range(1, order + 1):
        cn = sp.S.Zero
        for k in range(1, n + 1):
            t = sum(sp.binomial(k-1, j) * n ** (k-1-j) * sp.rf(k, j)
                    * (u/2) ** j for j in range(k))
            cn -= u ** k * powers[k][n] * t / sp.factorial(k)
        lagrange.append(sp.Poly(cn, u, domain=sp.QQ))

    # Here no Lagrange coefficient is used to construct the recursive solution.
    # The q^n coefficient in V is minus the known q^n residual of the lower jet.
    recursive = [zero]
    for n in range(1, order + 1):
        square = sum((recursive[j] * recursive[n-j] for j in range(1, n)), zero)
        tail = zero
        for m in range(1, n + 1):
            if r[m] == 0:
                continue
            ex = [one]
            for ell in range(1, n-m+1):
                ex.append(sum((j * recursive[j] * ex[ell-j]
                               for j in range(1, ell+1)), zero)
                          * (-sp.Rational(m, ell)))
            tail += r[m] * ex[n-m]
        recursive.append(-up * (square/2 + tail))
        assert recursive[n] == lagrange[n]
        assertions += 1

    records = []
    for n in range(1, order + 1):
        p = lagrange[n]
        valuation = min(mon[0] for mon, coefficient in p.terms() if coefficient)
        expected_val = 2 if n >= 3 and n % 2 else 1
        assert p.degree() == 2*n-1
        assert valuation == expected_val
        assert all((-1) ** (n+1) * coefficient > 0
                   for coefficient in p.all_coeffs() if coefficient)
        assert p.LC() == (-1) ** (n+1) * sp.catalan(n-1) / 2 ** (3*n-1)
        assert p.nth(1) == -r[n]
        assertions += 5
        if n >= 3 and n % 2:
            assert p.nth(2) == sp.Rational(n, 4) * r[n-1]
            assertions += 1
        records.append({"n": n, "coefficient": str(p.as_expr()),
                        "degree": p.degree(), "valuation": valuation})

    # Independently substitute the Lagrange jet into the original equation.
    residual = [lagrange[n] + up * sum(
        (lagrange[j] * lagrange[n-j] for j in range(n+1)), zero)/2
        for n in range(order+1)]
    for m in range(1, order+1):
        if r[m] == 0:
            continue
        ex = [one]
        for ell in range(1, order-m+1):
            ex.append(sum((j * lagrange[j] * ex[ell-j]
                           for j in range(1, ell+1)), zero)
                      * (-sp.Rational(m, ell)))
        for n in range(m, order+1):
            residual[n] += up * r[m] * ex[n-m]
    assert all(p.is_zero for p in residual)
    assertions += len(residual)

    # Exact finite versions of the estimates used in the proof.
    b = [Fraction(0)] + [Fraction(math.factorial(n-1), n) for n in range(1, 101)]
    max_pair = Fraction(0)
    max_interior = Fraction(0)
    for n in range(2, 101):
        pair = sum((b[j]*b[n-j] for j in range(1, n)), Fraction(0))
        assert pair <= 3*b[n-1]
        max_pair = max(max_pair, pair/b[n-1])
        assertions += 1
        if n >= 4:
            interior = sum((b[j]*b[n-j] for j in range(2, n-1)), Fraction(0))
            assert interior <= 6*b[n-2]
            max_interior = max(max_interior, interior/b[n-2])
            assertions += 1
    for n in range(1, 101):
        for k in range(1, n+1):
            ratio = n ** (k-1) * b[n-k+1] / b[n]
            # Rational consequence of the proven sharper bound k*exp(k).
            assert ratio <= k * 3 ** k
            assertions += 1
    bp = b[:33]
    for k in range(1, 33):
        for n in range(k, 33):
            assert bp[n] <= 3 ** (k-1) * b[n-k+1]
            assertions += 1
        if k < 32:
            bp = [sum((bp[j]*b[n-j] for j in range(n+1)), Fraction(0))
                  for n in range(33)]

    # The 1/n correction's finite coefficient algebra, independent of fitting.
    w, z, d = sp.symbols("w z d")
    for k in range(1, 13):
        h = k-1
        rat = sp.prod(1/(1-i*w) for i in range(1, h+1))/(1-h*w)
        assert sp.diff(rat, w).subs(w, 0) == sp.Rational(h*(h+3), 2)
        t = sum(sp.binomial(h, j)*sp.rf(k, j)*(u*w/2)**j for j in range(k))
        assert sp.diff(t, w).subs(w, 0) == u*k*(k-1)/2
        assertions += 2
    for H in (sp.cosh(z), sp.sinh(z)):
        euler = lambda f: z*sp.diff(f, z)
        derived = ((1+u)*euler(euler(H))+(3+u)*euler(H))/2+d*u*H
        claimed = ((1+u)*z**2/2+d*u)*H+(2+u)*z*sp.diff(H, z)
        assert sp.simplify(derived-claimed) == 0
        assertions += 1

    return {"status": "passed", "assertions": assertions,
            "formal_order": order,
            "construction": "Finite Lagrange formula versus independently recursive implicit equation",
            "substitution_residual": "All q^0 through q^N coefficients exactly zero",
            "coefficients": records,
            "convolution_tests": {
                "two_factor_and_interior_max_n": 100,
                "all_ratio_pairs_max_n": 100,
                "ratio_pairs_include_k_equals_n": True,
                "exact_ratio_test": "n^(k-1)*b_(n-k+1)/b_n <= k*3^k; exp(k) bound is proved in article",
                "multi_factor_max_n": 32,
                "max_two_factor_ratio": rational_record(max_pair),
                "max_interior_ratio": rational_record(max_interior)},
            "first_correction_algebra": "12 endpoint and inner-factor expansions; both hyperbolic parity sums"}, lagrange


def normalized_powers(indices: list[int], dtype: Any = LD,
                      cutoff: int | None = None) -> dict[int, np.ndarray]:
    """Return S_(n,k)/b_(n-k+1), not the factorially large S_(n,k).

    F_(k,l)=S_(k+l,k)/b_(l+1). The common triangular operator has entries
    alpha_(l-m+1) * (l+1)/((m+1)(l-m+1) binom(l,m)), where
    alpha_j=a_j/b_j.  These are positive and have bounded row sums.
    """
    N = max(indices)
    cutoff = min(N, cutoff or N)
    alpha = np.zeros(N+1, dtype=dtype)
    alpha[1] = dtype(mp.nstr(mp.pi**2, 70))
    for j in range(2, N+1, 2):
        alpha[j] = dtype(mp.nstr(4*mp.zeta(j)**2, 70))
    matrix = np.zeros((N, N), dtype=dtype)
    for ell in range(N):
        row = np.empty(ell+1, dtype=dtype)
        row[0] = dtype(1)
        half = ell//2
        if half:
            j = np.arange(1, half+1, dtype=dtype)
            rates = j*j/(j+1) * (ell-j+2)/(ell-j+1)**2
            row[1:half+1] = np.cumprod(rates, dtype=dtype)
        for j in range(half+1):
            row[ell-j] = row[j]
        matrix[ell, :ell+1] = row * alpha[1:ell+2][::-1]
    current = alpha[1:].copy()
    out = {n: np.zeros(min(n, cutoff)+1, dtype=dtype) for n in indices}
    for k in range(1, cutoff+1):
        for n in indices:
            if n >= k:
                out[n][k] = current[n-k]
        if k < cutoff:
            size = N-k
            current = matrix[:size, :size] @ current[:size]
    assert all(np.all(np.isfinite(v)) for v in out.values())
    return out


def parameters(n: int) -> list[tuple[str, Any]]:
    return [("u="+v, mp.mpf(v)) for v in ("0.01", "0.05", "0.1", "0.2", "0.5")] + [
        ("complex", mp.mpc("0.1", "0.05")),
        ("moving", 1/mp.log(n+mp.e))]


def evaluate_normalized(n: int, powers: np.ndarray,
                        params: list[tuple[str, Any]]) -> np.ndarray:
    """Compute Z_n=(-1)^(n+1) A^n C_n/(4 u b_n), with u factored out."""
    uv = np.array([as_cd(x) for _, x in params], dtype=CD)
    total = np.zeros(len(uv), dtype=CD)
    compensation = np.zeros(len(uv), dtype=CD)
    upowfac = np.ones(len(uv), dtype=CD)  # u^(k-1)/k!, initially k=1
    ratio = LD(1)  # n^(k-1) b_(n-k+1)/b_n
    for k in range(1, len(powers)):
        tnorm = np.ones(len(uv), dtype=CD)
        term = np.ones(len(uv), dtype=CD)
        for j in range(1, k):
            term *= LD((k-j)*(k+j-1))/LD(2*n*j) * uv
            tnorm += term
        summand = (LD(powers[k])*ratio/LD(4)) * upowfac * tnorm
        # Compensated summation protects the complex diagnostic as well.
        corrected = summand-compensation
        updated = total+corrected
        compensation = (updated-total)-corrected
        total = updated
        if k+1 < len(powers):
            ratio *= LD(n)*LD(n-k+1)/LD((n-k)**2)
            upowfac *= uv/LD(k+1)
    assert np.all(np.isfinite(total))
    return total


def mp_powers(indices: list[int]) -> dict[int, list[Any]]:
    """Independent high-precision recurrence with exact binomial weights."""
    N = max(indices)
    alpha = [mp.mpf(0)]*(N+1)
    alpha[1] = mp.pi**2
    for j in range(2, N+1, 2):
        alpha[j] = 4*mp.zeta(j)**2
    matrix = []
    for ell in range(N):
        row = []
        for j in range(ell+1):
            index = ell-j+1
            if alpha[index]:
                weight = mp.mpf(ell+1)/((j+1)*(ell-j+1)*math.comb(ell, j))
                row.append((j, alpha[index]*weight))
        matrix.append(row)
    current = alpha[1:]
    out = {n: [mp.mpf(0)]*(n+1) for n in indices}
    for k in range(1, N+1):
        for n in indices:
            if n >= k:
                out[n][k] = current[n-k]
        if k < N:
            current = [mp.fsum(weight*current[j] for j, weight in matrix[ell])
                       for ell in range(N-k)]
    return out


def mp_evaluate(n: int, powers: list[Any], u: Any) -> Any:
    ratio = mp.mpf(1)
    upowfac = mp.mpf(1)
    summands = []
    for k in range(1, n+1):
        term = mp.mpf(1)
        pieces = [term]
        for j in range(1, k):
            term *= mp.mpf((k-j)*(k+j-1))/(2*n*j)*u
            pieces.append(term)
        summands.append(powers[k]*ratio*upowfac*mp.fsum(pieces)/4)
        if k < n:
            ratio *= mp.mpf(n)*(n-k+1)/(n-k)**2
            upowfac *= u/(k+1)
    return mp.fsum(summands)


def asymptotic_records(powers: dict[int, np.ndarray], indices: list[int]
                       ) -> tuple[list[dict[str, Any]], dict[int, np.ndarray]]:
    c = as_ld(mp.pi**2)
    d = as_ld((4*mp.pi**2)**2/288)
    records = []
    values = {}
    for n in indices:
        pp = parameters(n)
        actual = evaluate_normalized(n, powers[n], pp)
        values[n] = actual
        for j, (label, uu) in enumerate(pp):
            u = as_cd(uu)
            z = c*u
            H = np.cosh(z) if n % 2 == 0 else np.sinh(z)
            Hp = np.sinh(z) if n % 2 == 0 else np.cosh(z)
            correction = ((1+u)*z*z/2+d*u)*H+(2+u)*z*Hp
            lead_error = (actual[j]-H)/H
            corrected_error = (actual[j]-H-correction/n)/H
            records.append({
                "n": n, "parity": "even" if n % 2 == 0 else "odd",
                "parameter": label, "u": complex_record(u),
                "complete_finite_sum": len(powers[n]) == n+1,
                "k_max": len(powers[n])-1,
                "Z_actual": complex_record(actual[j]),
                "H_leading": complex_record(H),
                "K_first_correction": complex_record(correction),
                "relative_leading_error": complex_record(lead_error),
                "relative_first_corrected_error": complex_record(corrected_error),
                "n_times_relative_leading_error": complex_record(n*lead_error),
                "n2_times_relative_corrected_error": complex_record(n*n*corrected_error)})
    return records, values


def high_precision_checks(powers: dict[int, np.ndarray], lagrange: list[Any],
                          dps: int) -> dict[str, Any]:
    candidates = (6, 7, 12, 64, 65, 128, 129)
    indices = [n for n in candidates if n in powers]
    mh = mp_powers(indices)
    out = []
    maximum = mp.mpf(0)
    exact_maximum = mp.mpf(0)
    u_symbol = sp.Symbol("u")
    for n in indices:
        pp = parameters(n)
        extended = evaluate_normalized(n, powers[n], pp)
        for index in (0, 2, 4, 5, 6):
            label, u = pp[index]
            high = mp_evaluate(n, mh[n], u)
            error = abs(mp_from_cd(extended[index])-high)/max(mp.mpf(1), abs(high))
            maximum = max(maximum, error)
            assert error < mp.mpf("2e-15")
            item = {"n": n, "parameter": label,
                    "mpmath_value": {"real": mp.nstr(mp.re(high), 45),
                                     "imag": mp.nstr(mp.im(high), 45)},
                    "relative_or_absolute_error": mp.nstr(error, 16)}
            if n < len(lagrange):
                exact = mp.mpc(0)
                for mon, coefficient in lagrange[n].terms():
                    exact += (mp.mpf(int(sp.numer(coefficient)))/int(sp.denom(coefficient))) * u**mon[0]
                exact *= (-1)**(n+1)*(4*mp.pi**2)**n/(4*u*(mp.gamma(n)/n))
                ee = abs(high-exact)/max(mp.mpf(1), abs(exact))
                exact_maximum = max(exact_maximum, ee)
                assert ee < mp.mpf(10)**(-dps+12)
                item["exact_polynomial_crosscheck_error"] = mp.nstr(ee, 16)
            out.append(item)
    return {"status": "passed", "mpmath_decimal_digits": dps,
            "algorithm": "Independent mpmath normalized recurrence with exact integer binomial weights; every k<=n",
            "max_extended_precision_error": mp.nstr(maximum, 18),
            "max_exact_polynomial_error": mp.nstr(exact_maximum, 18),
            "records": out}


def double_precision_checks(powers: dict[int, np.ndarray], indices: list[int]
                            ) -> dict[str, Any]:
    """Large-index precision diagnostic; an exact rational tail majorant is supplied."""
    chosen = [n for n in indices if n >= 512]
    if not chosen:
        return {"status": "not run", "reason": "No requested index at least 512"}
    cutoff = 256
    fp = normalized_powers(chosen, dtype=np.float64, cutoff=cutoff)
    # For |u|<=1/2, choose K=12, e<3. The proven k-summand majorant
    # for D_n/(4 b_n) is k*81^k/(18 k!). A geometric tail gives this
    # EXACT rational upper bound. This controls omitted terms only, not roundoff.
    bound = Fraction(81**(cutoff+1)*(cutoff+1),
                     18*math.factorial(cutoff)*(cutoff+1-81))
    bound_mp = mp.mpf(bound.numerator)/bound.denominator
    out = []
    maximum = mp.mpf(0)
    for n in chosen:
        pp = parameters(n)
        full = evaluate_normalized(n, powers[n], pp)
        cross = evaluate_normalized(n, fp[n], pp)
        for j, (label, u) in enumerate(pp):
            error = abs(mp_from_cd(cross[j])-mp_from_cd(full[j]))/max(mp.mpf(1), abs(mp_from_cd(full[j])))
            maximum = max(maximum, error)
            assert error < mp.mpf("2e-12")
            out.append({"n": n, "parameter": label,
                        "relative_or_absolute_error": mp.nstr(error, 16)})
    return {"status": "passed", "convolution_dtype": "float64",
            "evaluation_dtype": "clongdouble", "cutoff": cutoff,
            "rounding_note": "This is a precision diagnostic, not an enclosure of numerical roundoff.",
            "exact_tail_bound_for_D_over_4b": rational_record(bound),
            "tail_bound_decimal": mp.nstr(bound_mp, 30),
            "tail_bound_domain": "|u| <= 1/2; all n; divide this bound by |u| for Z_n",
            "max_precision_difference": mp.nstr(maximum, 18), "records": out}


def write_csv(path: Path, records: list[dict[str, Any]]) -> None:
    names = ["n", "parity", "parameter", "complete_finite_sum", "k_max"]
    complex_names = ["u", "Z_actual", "H_leading", "K_first_correction",
                     "relative_leading_error", "relative_first_corrected_error",
                     "n_times_relative_leading_error", "n2_times_relative_corrected_error"]
    fields = names + [f"{key}_{part}" for key in complex_names for part in ("real", "imag")]
    with path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=fields)
        writer.writeheader()
        for row in records:
            flat = {key: row[key] for key in names}
            for key in complex_names:
                for part in ("real", "imag"):
                    flat[f"{key}_{part}"] = row[key][part]
            writer.writerow(flat)


def make_plots(out: Path, records: list[dict[str, Any]]) -> list[str]:
    plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 11,
                         "axes.spines.top": False, "axes.spines.right": False,
                         "axes.titleweight": "semibold", "pdf.fonttype": 42,
                         "ps.fonttype": 42, "savefig.dpi": 220})
    colors = {"u=0.05": "#007F86", "u=0.1": "#4067B1", "u=0.2": "#C77927"}
    fig, axes = plt.subplots(2, 2, figsize=(7.8, 6.4), constrained_layout=True)
    fig.get_layout_engine().set(rect=(0.0, 0.11, 1.0, 0.89))
    for col, parity in enumerate(("even", "odd")):
        for label, color in colors.items():
            rr = [row for row in records if row["parity"] == parity and row["parameter"] == label]
            n = np.array([row["n"] for row in rr])
            leading = np.array([abs(float(row["relative_leading_error"]["real"])) for row in rr])
            corrected = np.array([abs(float(row["relative_first_corrected_error"]["real"])) for row in rr])
            scaled = np.array([float(row["n2_times_relative_corrected_error"]["real"]) for row in rr])
            axes[0, col].loglog(n, leading, "--", color=color, alpha=.75, lw=1.4)
            axes[0, col].loglog(n, corrected, "o-", color=color, ms=4.5, lw=1.7, label=label)
            axes[1, col].semilogx(n, scaled, "o-", color=color, ms=4.5, lw=1.7, label=label)
        axes[0, col].set_title(f"{parity.capitalize()} coefficients")
        axes[0, col].set_ylabel("Absolute relative error")
        axes[1, col].set_ylabel(r"$n^2\,(Z_n-H-K/n)/H$")
        axes[1, col].set_xlabel("Coefficient index n")
        for row in range(2):
            axes[row, col].grid(True, which="major", alpha=.2)
        axes[0, col].legend(frameon=False, loc="lower left")
    fig.suptitle("Hyperbolic late coefficients and the first correction", fontsize=13.5, fontweight="semibold")
    fig.text(.5, .012,
             "Dashed: leading term. Solid: including the 1/n correction.\n"
             "All plotted values use complete finite coefficient sums.",
             ha="center", va="bottom", fontsize=11)
    fig.savefig(out/"asymptotic_errors.pdf", bbox_inches="tight",
                metadata={"Title": "Hyperbolic late coefficient diagnostics", "CreationDate": None, "ModDate": None})
    fig.savefig(out/"asymptotic_errors.png", bbox_inches="tight")
    plt.close(fig)
    return ["asymptotic_errors.pdf", "asymptotic_errors.png"]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--max-index", type=int, default=1024)
    parser.add_argument("--exact-order", type=int, default=12)
    parser.add_argument("--dps", type=int, default=80)
    args = parser.parse_args()
    if args.max_index < 128 or args.exact_order < 12 or args.dps < 50:
        parser.error("Use --max-index >=128, --exact-order >=12, and --dps >=50.")
    info = np.finfo(LD)
    if info.maxexp < 12000 or info.nmant < 63:
        raise RuntimeError("This replay requires an extended-range long double (64-bit significand, exponent >=12000). "
                           "The supplied recorded results identify their platform; do not silently substitute float64.")
    mp.mp.dps = args.dps
    out = args.output_dir
    out.mkdir(parents=True, exist_ok=True)
    started = time.perf_counter()
    print("Exact formal and factorial-convolution checks...", flush=True)
    exact, lagrange = exact_checks(args.exact_order)
    (out/"exact_results.json").write_text(json.dumps(exact, indent=2)+"\n", encoding="utf-8")
    (out/"coefficients_exact.txt").write_text("\n\n".join(
        f"C_{row['n']}(u) = {row['coefficient']}" for row in exact["coefficients"])+"\n", encoding="utf-8")
    bases = [n for n in (64, 128, 256, 512, 1024) if n <= args.max_index]
    indices = [n+j for n in bases for j in (0, 1)]
    all_indices = sorted(set(indices+[6, 7, 12]))
    print(f"Complete normalized coefficient sums through n={max(all_indices)}...", flush=True)
    powers = normalized_powers(all_indices)
    records, values = asymptotic_records(powers, indices)
    assert all(row["complete_finite_sum"] for row in records)
    write_csv(out/"diagnostics.csv", records)
    print("Independent high-precision coefficient computation...", flush=True)
    high = high_precision_checks(powers, lagrange, args.dps)
    print("Large-index precision comparison and analytic tail bound...", flush=True)
    double = double_precision_checks(powers, indices)
    # At the largest indices, verify that the independently derived correction
    # actually improves every recorded parameter case; no fit is performed.
    improvement = []
    for row in records:
        if row["n"] >= max(indices)-1:
            leading = abs(complex(float(row["relative_leading_error"]["real"]),
                                  float(row["relative_leading_error"]["imag"])))
            corrected = abs(complex(float(row["relative_first_corrected_error"]["real"]),
                                    float(row["relative_first_corrected_error"]["imag"])))
            assert corrected < leading
            improvement.append({"n": row["n"], "parameter": row["parameter"],
                                "error_reduction_factor": leading/corrected})
    plots = make_plots(out, records)
    results = {"status": "passed", "reproducibility": {
        "python": platform.python_version(), "platform": platform.platform(),
        "packages": {"numpy": np.__version__, "mpmath": mp.__version__,
                     "sympy": sp.__version__, "matplotlib": matplotlib.__version__},
        "longdouble_significand_bits": info.nmant+1,
        "longdouble_max_binary_exponent": info.maxexp,
        "high_precision_decimal_digits": args.dps,
        "deterministic": "No random sampling or fitted parameters; fixed index and parameter lists."},
        "evidence_scope": {
            "exact": "Rational polynomial identities and finite rational inequalities.",
            "numerical": "Floating-point diagnostics; not interval-certified.",
            "main_coefficient_sums": "Complete finite Lagrange sums, all k<=n; NO mathematical truncation in main table.",
            "secondary_precision_check": "Float64 convolution at k<=256; exact rational omitted-term majorant recorded separately.",
            "not_claimed": "Finite checks do not prove infinite asymptotic theorems or analytic continuation."},
        "normalization": "Z_n = (-1)^(n+1) A^n C_n(u)/(4 u b_n), A=4*pi^2, b_n=Gamma(n)/n",
        "asymptotic_formula": "Z_n = H + ([(1+u)z^2/2+d*u]H+(2+u)z H')/n + O(n^-2); z=pi^2*u; d=A^2/288",
        "exact_assertions": exact["assertions"], "exact_order": args.exact_order,
        "indices": indices, "main_diagnostic_count": len(records),
        "high_precision_crosschecks": high, "large_index_precision_checks": double,
        "largest_index_improvements": improvement,
        "diagnostics": records, "plots": plots}
    (out/"results.json").write_text(json.dumps(results, indent=2)+"\n", encoding="utf-8")
    summary = [
        "Research verification completed successfully.",
        f"Exact assertions: {exact['assertions']}; independently constructed inverse through q^{args.exact_order}.",
        f"Main table: {len(records)} cases; every finite k-summand included through n={max(indices)}.",
        f"Arithmetic: long double with {info.nmant+1} significand bits; mpmath cross-checks at {args.dps} decimal digits.",
        f"Maximum high-precision comparison error: {high['max_extended_precision_error']}.",
        f"Maximum exact-polynomial comparison error: {high['max_exact_polynomial_error']}.",
        "No interval certification is claimed. The exact tail bound in the secondary precision check bounds omitted terms only.",
        f"Elapsed seconds on this run: {time.perf_counter()-started:.3f}.",
    ]
    (out/"run.txt").write_text("\n".join(summary)+"\n", encoding="utf-8")
    print("\n".join(summary), flush=True)


if __name__ == "__main__":
    main()
