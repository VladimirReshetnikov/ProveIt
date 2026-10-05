#!/usr/bin/env python3
"""Exact-count numerical illustrations for the r=3 first-failure model.

Counts are Python integers; no random sampling is used.  Floating-point
probabilities are formed only after exact coefficient extraction and Catalan
row-sum checks.  Numerical experiments illustrate, rather than prove, the
asymptotic assertions.

Run from the article directory: python3 code/make_figures.py
The --outdir option selects a package root containing data/ and figures/.
Dependencies: numpy, scipy, matplotlib, mpmath.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path
import time

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from scipy.special import logsumexp, expit
from scipy.optimize import root
import mpmath as mp


RHO = (3.0 - math.sqrt(5.0)) / 2.0
Y_C = 4.0 * RHO
P = (5.0 - math.sqrt(5.0)) / 2.0
A = 4.0 / math.sqrt(math.pi)
TAIL = A / P
MEAN_LIMIT = 2.0 * A / P
S_STAR = math.log(P / (2.0 * A))


def exact_rows(ns: list[int]) -> tuple[dict[int, list[int]], dict]:
    """Coefficient rows using D_3=1-3u+u^2 along fixed n-k diagonals.

    For k<n, c[n,k]-3c[n-1,k-1]+c[n-2,k-2]
      = [x^(n-k-1)] C(x)^(k+1), k>=3.
    The two preceding values vanish before k=3.  Ballot coefficients are
    advanced using their exact multiplicative recurrence.
    """
    ns = sorted(set(ns))
    maximum = ns[-1]
    wanted = set(ns)
    rows = {n: [0] * (n+1) for n in ns}
    q = [1, 3]
    for n in range(2, maximum+1):
        q.append(3*q[-1] - q[-2])
    for n, row in rows.items():
        row[n] = 1 if n == 1 else q[n-1] - q[n-2]
    initial_ballot = 1  # [x^0] C(x)^4.
    updates = 0
    for m in range(maximum-3):
        b = initial_ballot
        before = previous = 0
        for k in range(3, maximum-m):
            value = 3*previous - before + b
            n = m+k+1
            if n in wanted:
                rows[n][k] = value
            before, previous = previous, value
            # p=k+1; B(m,p+1)/B(m,p)
            b = b*(k+2)*(2*m+k+1) // ((k+1)*(m+k+2))
            updates += 1
        # B(m+1,4)/B(m,4).
        initial_ballot = initial_ballot*(2*m+4)*(2*m+5) // ((m+1)*(m+5))
    independent_checks = 0
    for n, row in rows.items():
        assert sum(row) == math.comb(2*n, n)//(n+1), (n, "Catalan row sum")
        assert all(v == 0 for v in row[:3])
        assert all(v > 0 for v in row[3:])
        if n <= 100:
            for k in range(3, n):
                m = n-k-1
                direct = 0
                for j in range(3, k+1):
                    b = math.comb(2*m+j, m) - (math.comb(2*m+j, m-1) if m else 0)
                    direct += q[k-j]*b
                assert direct == row[k], (n, k, "independent binomial extraction")
                independent_checks += 1
    return rows, {"exact_row_sum_checks": len(rows), "integer_recurrence_updates": updates,
                  "independent_binomial_coefficient_checks":independent_checks}


def critical_probabilities(row: list[int]) -> tuple[np.ndarray, float, np.ndarray]:
    n = len(row)-1
    k = np.arange(n+1, dtype=float)
    log_weights = np.array([math.log(v) if v else -np.inf for v in row]) + k*math.log(Y_C)
    log_z = float(logsumexp(log_weights))
    return np.exp(log_weights-log_z), math.exp(log_z-n*math.log(4.0)), log_weights-n*math.log(4.0)


def limiting_deficit_pmf(maximum: int) -> np.ndarray:
    """Positive coefficient extraction from the limiting probability GF.

    H(z) = (z/4) rho^3 C(z/4)^4 / (1-rho C(z/4));
    pi(z) = (rho(1-rho)+H(z))/(rho sqrt(5) P).
    """
    cb = np.empty(maximum+1)
    b4 = np.empty(maximum+1)
    cb[0] = b4[0] = 1.0
    for n in range(maximum):
        cb[n+1] = cb[n]*(2*n+1)/(2*n+4)
        b4[n+1] = b4[n]*(2*n+4)*(2*n+5)/(4.0*(n+1)*(n+5))
    inv = np.empty(maximum+1)
    inv[0] = 1.0/(1.0-RHO)
    for n in range(1, maximum+1):
        inv[n] = (RHO/(1.0-RHO))*np.dot(cb[1:n+1], inv[n-1::-1])
    h = np.convolve(b4, inv)[:maximum]
    answer = np.empty(maximum+1)
    normalizer = RHO*math.sqrt(5.0)*P
    answer[0] = RHO*(1.0-RHO)/normalizer
    answer[1:] = (RHO**3/4.0)*h/normalizer
    assert abs(answer[0]-0.2) < 1e-14
    return answer


def csv_write(path: Path, records: list[dict]) -> None:
    with path.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(records[0]))
        writer.writeheader()
        writer.writerows(records)


def setup_style() -> None:
    plt.rcParams.update({
        "font.family": "DejaVu Serif",
        "mathtext.fontset": "dejavuserif",
        "font.size": 9.0,
        "axes.titlesize": 10.0,
        "axes.labelsize": 9.0,
        "xtick.labelsize": 8.0,
        "ytick.labelsize": 8.0,
        "legend.fontsize": 7.4,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "axes.linewidth": 0.7,
        "grid.color": "#d8dce0",
        "grid.linewidth": 0.5,
        "grid.alpha": 0.7,
        "savefig.dpi": 220,
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
    })


def critical_figure(outdir: Path, ns: list[int], critical: dict, limits: np.ndarray) -> None:
    fig, axes = plt.subplots(1, 2, figsize=(7.05, 3.12), layout="constrained")
    ax, right = axes
    n = max(ns)
    m = np.arange(1, n+1)
    ax.loglog(m, limits[1:], color="#25374a", lw=1.6, label=r"Limit $\pi_m$")
    finite = critical[n][0][::-1]
    use = finite[1:] > 0
    ax.loglog(m[use], finite[1:][use], color="#4389a5", lw=1.15, ls="--",
              label=fr"Exact counts, $n={n}$")
    tail_m = np.geomspace(30, n, 250)
    ax.loglog(tail_m, TAIL*tail_m**-1.5, color="#be7133", lw=1.25, ls=":",
              label=r"$(a/P)m^{-3/2}$")
    ax.set(xlabel=r"Deficit $m=n-k$", ylabel=r"Probability at $m$",
           title="(a) Critical deficit and power-law tail")
    ax.set_xlim(1, n*1.05)
    ax.set_ylim(1.0e-6, 0.075)
    ax.grid(True, which="major")
    ax.legend(loc="lower left", frameon=False)
    ax.text(0.97, 0.96, r"Atom at zero: $\pi_0=1/5$", transform=ax.transAxes,
            ha="right", va="top", fontsize=8.0)

    mean_scaled = [float(np.dot(np.arange(n+1)[::-1], critical[n][0]))/math.sqrt(n) for n in ns]
    right.axhline(MEAN_LIMIT, color="#be7133", lw=1.3, ls=":", label=fr"Limit $2a/P={MEAN_LIMIT:.6f}$")
    right.semilogx(ns, mean_scaled, color="#25374a", marker="o", ms=3.0, lw=1.35,
                  label="Exact finite-size values")
    right.set(xlabel=r"Size $n$ (log scale)", ylabel=r"$\mathbb{E}_{y_c}[M_n]/\sqrt{n}$",
              title="(b) A tight law with a growing mean")
    right.set_ylim(0, MEAN_LIMIT*1.05)
    right.grid(True, which="major")
    right.legend(loc="lower right", frameon=False)
    fig.savefig(outdir/"critical_deficit.pdf", bbox_inches="tight")
    fig.savefig(outdir/"critical_deficit.png", bbox_inches="tight")
    plt.close(fig)


def mixture_figure(outdir: Path, records: list[dict], mixture_ns: list[int]) -> None:
    fig, ax = plt.subplots(figsize=(6.4, 3.72), layout="constrained")
    colors = ["#93b9c6", "#5394ac", "#23748e", "#25374a"]
    styles = [":", "-.", "--", "-"]
    for n, color, style in zip(mixture_ns, colors, styles):
        part = [item for item in records if item["n"] == n]
        ax.plot([v["s"] for v in part], [v["exact_late_probability"] for v in part],
                color=color, ls=style, lw=1.7 if n == max(mixture_ns) else 1.3,
                label=fr"Exact counts, $n={n}$")
    grid = np.linspace(-5.0, 5.0, 501)
    ax.plot(grid, expit(S_STAR-grid), color="#be7133", lw=1.8,
            label=r"Limit $Pe^{-s}/(Pe^{-s}+2a)$")
    ax.set(xlabel=r"Window coordinate $s$", ylabel=r"$\Pr_{y_n}(K_n>n/2)$",
           title="Logarithmically shifted coexistence window")
    ax.set_xlim(-5, 5)
    ax.set_ylim(0, 1)
    ax.set_xticks(np.arange(-5, 6))
    ax.set_yticks(np.linspace(0, 1, 6))
    ax.grid(True, which="major")
    ax.legend(loc="upper right", frameon=False)
    ax.text(0.03, 0.075, r"$y_n=y_c\exp[-(\frac{1}{2}\log n+\log\log n+s)/n]$"+"\n"+
            "Finite-size convergence is slow at these sizes.",
            transform=ax.transAxes, ha="left", va="bottom", fontsize=8.0,
            bbox={"facecolor":"white", "edgecolor":"none", "alpha":0.88, "pad":3.0})
    fig.savefig(outdir/"coexistence_window.pdf", bbox_inches="tight")
    fig.savefig(outdir/"coexistence_window.png", bbox_inches="tight")
    plt.close(fig)


def complex_zero_diagnostics(rows: dict, critical: dict, ns: list[int]) -> list[dict]:
    """Locate one complex zero near the limiting s-coordinate; then recheck it.

    This does not assert that the reported root is the nearest zero.  Exact
    integer coefficients are converted to 55-digit arithmetic for refinement.
    """
    results = []
    for n in ns:
        k = np.arange(n+1, dtype=float)
        base = 0.5*math.log(n)+math.log(math.log(n))
        coefficients = np.exp(critical[n][2]-k*base/n)[3:]
        exponents = (k[3:]-3.0)/n  # Remove the exact factor y^3.
        def value(s):
            return np.dot(coefficients, np.exp(-exponents*s))
        def derivative(s):
            return np.dot(-exponents*coefficients, np.exp(-exponents*s))
        def split(coords):
            answer = value(coords[0]+1j*coords[1])
            return [float(answer.real), float(answer.imag)]
        def jacobian(coords):
            answer = derivative(coords[0]+1j*coords[1])
            return [[float(answer.real), -float(answer.imag)],
                    [float(answer.imag), float(answer.real)]]
        candidates = []
        for imaginary_start in [4.5, 5.5, math.pi]:
            with np.errstate(over="ignore", invalid="ignore"):
                candidate = root(split, [S_STAR, imaginary_start], jac=jacobian, tol=1e-11)
            if (np.linalg.norm(candidate.fun) < 1e-10 and
                    -20 < candidate.x[0] < 20 and 0 < candidate.x[1] < 2*math.pi):
                candidates.append(candidate)
        assert candidates, (n, "No zero found in the chosen first-branch neighborhood")
        found = min(candidates, key=lambda item: item.x[1])
        with mp.workdps(55):
            rho = (3-mp.sqrt(5))/2
            yc = 4*rho
            b = mp.log(n)/2 + mp.log(mp.log(n))
            coef = [mp.mpf(v)*yc**j/mp.mpf(4)**n for j,v in enumerate(rows[n])]
            def polynomial_at_s(s):
                z = mp.exp(-(b+s)/n)
                total = mp.mpc(0)
                for v in reversed(coef):
                    total = total*z+v
                return total
            z0 = mp.mpc(float(found.x[0]), float(found.x[1]))
            solved = mp.findroot(polynomial_at_s, (z0, z0+mp.mpf("0.0001")), tol=mp.mpf("1e-48"))
            residual = abs(polynomial_at_s(solved))
            results.append({"n":n, "real_s":mp.nstr(solved.real,25),
                            "imag_s":mp.nstr(solved.imag,25),
                            "limiting_real_s":S_STAR, "limiting_imag_s":math.pi,
                            "absolute_residual_scaled_polynomial":mp.nstr(residual,8),
                            "decimal_precision":55})
    return results


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--outdir", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--maximum", type=int, default=4000)
    parser.add_argument("--skip-zeros", action="store_true")
    args = parser.parse_args()
    start = time.monotonic()
    outdir = args.outdir / 'data'
    figdir = args.outdir / 'figures'
    outdir.mkdir(parents=True, exist_ok=True)
    figdir.mkdir(parents=True, exist_ok=True)
    ns = [25, 50, 100, 200, 400, 800, 1200, 2000, args.maximum]
    ns = sorted(set(n for n in ns if n <= args.maximum))
    mixture_ns = [n for n in [100, 400, 1200, args.maximum] if n in ns]
    mixture_ns = sorted(set(mixture_ns))
    rows, checks = exact_rows(ns)
    print(f"Exact rows computed and checked in {time.monotonic()-start:.3f} seconds.", flush=True)
    critical = {n: critical_probabilities(row) for n, row in rows.items()}
    limit = limiting_deficit_pmf(args.maximum)
    critical_records = []
    for n in ns:
        probabilities, normalized_z, _ = critical[n]
        m = np.arange(n+1)[::-1]
        critical_records.append({
            "n":n, "scaled_partition_Z_over_4pow_n":normalized_z,
            "limiting_partition_constant_P":P,
            "probability_zero_deficit":float(probabilities[n]),
            "mean_deficit":float(np.dot(m, probabilities)),
            "mean_deficit_over_sqrt_n":float(np.dot(m, probabilities))/math.sqrt(n),
            "limiting_mean_over_sqrt_n":MEAN_LIMIT,
            "probability_K_gt_n_over_2":float(probabilities[np.arange(n+1)>n/2].sum()),
        })
    csv_write(outdir/"critical_moments.csv", critical_records)
    pmf_records = []
    for n in mixture_ns:
        for m in range(n+1):
            pmf_records.append({"n":n,"deficit_m":m,
                                "exact_probability":float(critical[n][0][n-m]),
                                "limiting_probability":float(limit[m]),
                                "asymptotic_tail":TAIL*m**-1.5 if m else ""})
    csv_write(outdir/"critical_deficit_pmf.csv", pmf_records)
    mixture_records = []
    for n in mixture_ns:
        k = np.arange(n+1, dtype=float)
        for s in np.linspace(-5, 5, 201):
            shift = 0.5*math.log(n)+math.log(math.log(n))+float(s)
            logw = critical[n][2] - k*shift/n
            logz = logsumexp(logw)
            probabilities = np.exp(logw-logz)
            mixture_records.append({
                "n":n,"s":float(s), "y_n":Y_C*math.exp(-shift/n),
                "exact_late_probability":float(probabilities[k>n/2].sum()),
                "limiting_late_probability":float(expit(S_STAR-s)),
                "mean_K_over_n":float(np.dot(k/n, probabilities)),
                "scaled_partition_Z_over_4pow_n":float(math.exp(logz)),
            })
    csv_write(outdir/"coexistence_probabilities.csv", mixture_records)
    setup_style()
    critical_figure(figdir, ns, critical, limit)
    mixture_figure(figdir, mixture_records, mixture_ns)
    zero_records = [] if args.skip_zeros else complex_zero_diagnostics(rows, critical, mixture_ns)
    if zero_records:
        csv_write(outdir/"complex_zero_diagnostics.csv", zero_records)
    metadata = {
        "description":"Numerical diagnostics from exact integer counting rows; not proofs.",
        "r":3, "rho":RHO, "y_c":Y_C, "P":P, "a":A,
        "limiting_tail_constant_a_over_P":TAIL,
        "limiting_mean_constant_2a_over_P":MEAN_LIMIT,
        "limiting_complex_zero_real_s":S_STAR,
        "limiting_complex_zero_imag_s":math.pi,
        "sizes":ns, "mixture_sizes":mixture_ns, "checks":checks,
        "elapsed_seconds":round(time.monotonic()-start,3),
        "zero_diagnostics":zero_records,
        "maximum_exact_row_decimal_digits":int(math.log10(max(rows[args.maximum])))+1,
        "critical_records":critical_records,
    }
    (outdir/"numerical_summary.json").write_text(json.dumps(metadata, indent=2)+"\n")
    print(json.dumps({key: value for key,value in metadata.items() if key != "critical_records"}, indent=2))


if __name__ == "__main__":
    main()
