#!/usr/bin/env python3
"""Optional, non-certifying numerical illustrations for the research note.

Dependencies: mpmath, numpy, matplotlib. No network access is used.
Run from the archive root: python3 code/numerical_checks.py
The exact proof and the standard-library verifier do not depend on this script.
"""
from __future__ import annotations
import argparse
import csv
import json
from pathlib import Path
import mpmath as mp
import numpy as np


def chebyshev_pair(n: int, s):
    """Return C_n(s), C_(n-1)(s); the latter is 0 when n = 0."""
    p, q = mp.mpc(1), mp.mpc(0)
    for _ in range(n):
        p, q = s * p - q, p
    return p, q


def numerical_eigenvalues(n: int):
    zeta = (1 + 1j * np.sqrt(3)) / 2
    matrix = np.diag(np.ones(n-1), 1).astype(complex)
    matrix += np.diag(np.ones(n-1), -1)
    matrix[-1, -1] = zeta
    return np.linalg.eigvals(matrix)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, default=Path("results"))
    parser.add_argument("--figure-dir", type=Path, default=Path("figures"))
    args = parser.parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    args.figure_dir.mkdir(parents=True, exist_ok=True)
    mp.mp.dps = 80
    zeta = (1 + 1j * mp.sqrt(3)) / 2
    rows = []
    for j in (1, 2):
        for n in (10, 20, 50, 100, 200, 500):
            estimate = j * mp.pi / (n + zeta)
            theta = mp.findroot(
                lambda q: mp.sin((n+1)*q) - zeta*mp.sin(n*q),
                (estimate, estimate * mp.mpf("1.001")), tol=mp.mpf("1e-75"))
            s = 2 * mp.cos(theta)
            root = -1 / (4 * mp.sin(theta/2)**2)
            cn, cnm1 = chebyshev_pair(n, s)
            residual = abs(cn-zeta*cnm1) / (abs(cn)+abs(cnm1))
            if not residual < mp.mpf("1e-65"):
                raise ArithmeticError(f"Insufficient precision at n={n}, j={j}")
            approx = -(n+zeta)**2 / (j*j*mp.pi**2) - mp.mpf(1)/12
            refined = approx - 1j*mp.sqrt(3)/(3*(n+zeta))
            rows.append({
                "n": n, "j": j,
                "real_root": mp.nstr(mp.re(root), 35),
                "imag_root": mp.nstr(mp.im(root), 35),
                "absolute_error_O1_over_n": mp.nstr(abs(root-approx), 20),
                "n_times_error": mp.nstr(n*abs(root-approx), 20),
                "refined_error": mp.nstr(abs(root-refined), 20),
                "n_squared_times_refined_error": mp.nstr(n*n*abs(root-refined), 20),
                "scaled_Chebyshev_residual": mp.nstr(residual, 8),
            })
    with (args.out_dir / "root_asymptotics.csv").open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)

    bounds = []
    for n in (1, 2, 5, 10, 20, 50, 100):
        eigenvalues = numerical_eigenvalues(n)
        rho = 2*np.cos(np.pi/(2*n+1))
        roots = 1/(eigenvalues-2)
        assert np.min(eigenvalues.imag) > 0
        assert np.max(np.abs(eigenvalues)) <= rho+1e-12
        assert np.max(roots.real) < -.25
        bounds.append({"n": n, "rho_n": float(rho),
                       "max_abs_s": float(np.max(np.abs(eigenvalues))),
                       "min_Im_s": float(np.min(eigenvalues.imag)),
                       "max_Re_t": float(np.max(roots.real)),
                       "upper_Re_t_bound": float(-1/(2+rho))})
    report = {"status": "PASS (floating-point diagnostics, not certified root isolation)",
              "mpmath_decimal_precision": mp.mp.dps,
              "versions": {"mpmath": mp.__version__, "numpy": np.__version__},
              "spectral_bound_checks": bounds,
              "asymptotic_cases": len(rows)}
    (args.out_dir / "numerical_verification.json").write_text(
        json.dumps(report, indent=2)+"\n", encoding="utf-8")

    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    fig, ax = plt.subplots(figsize=(7.5, 4.1), constrained_layout=True)
    for n, marker in ((5, "o"), (10, "s"), (20, "^")):
        lower = 1/(numerical_eigenvalues(n)-2)
        roots = np.concatenate((lower, lower.conjugate()))
        ax.scatter(roots.real, roots.imag, s=26, marker=marker, label=f"n = {n}")
    ax.axvline(-.25, linestyle="--", linewidth=1, label="Re(t) = -1/4")
    ax.set_xlabel("Real part of t")
    ax.set_ylabel("Imaginary part of t")
    ax.set_title("Zeros of the special Stern-polynomial family")
    ax.legend(loc="center left", frameon=False)
    ax.grid(alpha=.22)
    for extension in ("pdf", "png"):
        fig.savefig(args.figure_dir / f"root_geometry.{extension}", dpi=170)
    plt.close(fig)
    print(json.dumps(report, indent=2))
    print("Asymptotic data: root_asymptotics.csv")


if __name__ == "__main__":
    main()
