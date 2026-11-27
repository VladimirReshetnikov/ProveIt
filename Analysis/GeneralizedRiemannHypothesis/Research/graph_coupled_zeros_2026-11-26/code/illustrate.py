#!/usr/bin/env python3
"""Reproduce the finite examples and figures in Electrical Laws for Zeros.

The universal theorems are proved in report.tex.  Floating point eigenvalues
here are illustrations; code/verify_graph.py performs exact rational checks.
"""
from __future__ import annotations

import csv
import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from scipy.linalg import null_space
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
FIGURES = ROOT / "figures"
CHECKS = ROOT / "checks"


def model(root_lists, edges):
    n = len(root_lists)
    roots = np.array([r for row in root_lists for r in row], dtype=float)
    N = len(roots)
    V = np.zeros((N, n))
    offset = 0
    for i, row in enumerate(root_lists):
        V[offset:offset+len(row), i] = 1
        offset += len(row)
    L = np.zeros((n, n))
    for i, j, w in edges:
        b = np.eye(n)[:, i] - np.eye(n)[:, j]
        L += w * np.outer(b, b)
    J = np.ones((n, n)) / n
    Lplus = np.linalg.inv(L+J)-J
    U = null_space(np.ones((1, N)))
    A = U.T @ np.diag(roots) @ U
    B = U.T @ V @ Lplus @ V.T @ U
    return A, B


def main():
    FIGURES.mkdir(exist_ok=True)
    CHECKS.mkdir(exist_ok=True)
    plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 10,
                         "axes.spines.top": False, "axes.spines.right": False,
                         "savefig.bbox": "tight"})
    colors = ["#1b4965", "#357f87", "#8b7a42", "#b45c40", "#793e68"]

    # Two different root configurations, but the same graph and degrees.
    configs = [[[-1], [0], [1]], [[-6], [2], [9]]]
    grid = np.geomspace(0.12, 8, 240)
    fig, axes = plt.subplots(1, 3, figsize=(11.4, 3.35), gridspec_kw={"width_ratios": [1, 1, 1.05]})
    data = []
    for c, roots in enumerate(configs):
        A, B = model(roots, [(0, 1, 1), (1, 2, 1)])
        beta = np.linalg.eigvalsh(A)
        trajectories = np.array([np.linalg.eigvalsh(A-B/t) for t in grid])
        for k in range(2):
            axes[c].plot(grid, trajectories[:, k], color=colors[k], lw=2)
            axes[c].axhline(beta[k], color=colors[k], ls="--", lw=1, alpha=.7)
        axes[c].set_xscale("log")
        axes[c].set_xlabel("Common conductance t")
        axes[c].set_ylabel("Zero location")
        axes[c].set_title("Input roots " + str([r[0] for r in roots]), fontsize=10.5)
        axes[c].grid(alpha=.16)
        distances = np.mean(beta-trajectories, axis=1)
        axes[2].plot(grid[::14], distances[::14], "o" if c==0 else "x",
                     ms=4, color=colors[c], label="First roots" if c==0 else "Second roots")
        for t, lam, dist in zip(grid, trajectories, distances):
            data.append([c, t, lam[0], lam[1], beta[0], beta[1], dist, 2/(3*t)])
    axes[2].plot(grid, 2/(3*grid), color="#b45c40", lw=1.6, label="Exact law: 2 / (3t)")
    axes[2].set(xscale="log", yscale="log", xlabel="Common conductance t",
                ylabel="Mean ordered displacement", title="Same electrical budget")
    axes[2].grid(alpha=.16)
    axes[2].legend(frameon=False, fontsize=8)
    fig.tight_layout(w_pad=1.9)
    fig.savefig(FIGURES / "electrical_transport.pdf")
    fig.savefig(FIGURES / "electrical_transport.png", dpi=180)
    plt.close(fig)
    with (CHECKS / "transport_plot_data.csv").open("w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["configuration", "t", "lambda1", "lambda2", "beta1", "beta2", "mean_displacement", "exact_value"])
        writer.writerows(data)

    # A five-root example showing repeated limiting derivative zeros are not
    # needed for the phenomenon, and allowing a collision at an input root.
    A, B = model([[-1, 1], [-2, 2], [-3, 3]], [(0, 1, 1), (1, 2, 1)])
    grid2 = np.geomspace(.25, 12, 230)
    lam2 = np.array([np.linalg.eigvalsh(A-B/t) for t in grid2])
    beta2 = np.linalg.eigvalsh(A)
    fig, ax = plt.subplots(figsize=(7.6, 3.5))
    for k in range(5):
        ax.plot(grid2, lam2[:, k], color=colors[k], lw=1.9)
        ax.axhline(beta2[k], color=colors[k], ls="--", lw=.8, alpha=.65)
    ax.set(xscale="log", xlabel="Common conductance t", ylabel="Zero location",
           title="Three quadratic polynomials: all five zeros move monotonically")
    ax.grid(alpha=.16)
    fig.tight_layout()
    fig.savefig(FIGURES / "quadratic_flow.pdf")
    fig.savefig(FIGURES / "quadratic_flow.png", dpi=180)
    plt.close(fig)

    z, t = sp.symbols("z t", real=True)
    ps = [z*z-1, z*z-4, z*z-9]
    L = sp.Matrix([[t, -t, 0], [-t, 2*t, -t], [0, -t, t]])
    polynomial = sp.factor((L*sp.diag(*ps)+sp.diag(*[sp.diff(p, z) for p in ps])).det())
    tiny = 1+4*t*z+t*t*(3*z*z-1)
    figures_info = {
        "numeric_scope": "Floating point illustration only; exact identities are separately checked.",
        "linear_path_polynomial": str(tiny),
        "quadratic_path_polynomial": str(polynomial),
        "quadratic_path_at_t1": str(sp.factor(polynomial.subs(t, 1))),
        "quadratic_path_roots_at_t1": [str(a) for a in sp.nroots(polynomial.subs(t, 1), n=24)],
        "quadratic_derivative_roots": ["-sqrt(7)", "-sqrt(7/3)", "0", "sqrt(7/3)", "sqrt(7)"],
        "max_plot_distance_error": float(max(abs(row[-1]-row[-2]) for row in data)),
        "transport_expected": "2/(3*t) for both linear configurations; 8/(15*t) for quadratics"
    }
    (CHECKS / "illustrations.json").write_text(json.dumps(figures_info, indent=2)+"\n")
    print(json.dumps(figures_info, indent=2))


if __name__ == "__main__":
    main()
