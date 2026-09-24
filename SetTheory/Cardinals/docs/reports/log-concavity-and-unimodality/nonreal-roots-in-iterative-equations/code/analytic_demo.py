#!/usr/bin/env python3
"""Numerical illustration of the real-analytic quartic counterexample.

The mathematical proof is in article.tex. Bisection and floating-point residuals
are illustrations, not certificates. Plotting is optional and needs matplotlib.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Callable

EPSILON = 0.25
THETA = math.pi / 2.0


def h(t: float) -> float:
    return t + EPSILON * math.sin(THETA * t)


def h_inverse(x: float) -> float:
    if not math.isfinite(x):
        raise ValueError("x must be finite")
    # |h(t)-t|<=epsilon gives an a priori bracket.
    lo, hi = x - EPSILON, x + EPSILON
    for _ in range(80):
        mid = (lo + hi) / 2
        if mid == lo or mid == hi:
            break
        if h(mid) < x:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def analytic_f(x: float) -> float:
    return h(h_inverse(x) + 1)


def iterates(f: Callable[[float], float], x: float, count: int) -> list[float]:
    result = [x]
    for _ in range(count):
        result.append(f(result[-1]))
    return result


def cubic_float(x: float) -> float:
    if x == 0:
        return 0.0
    if x < 0:
        return -cubic_float(-x)
    scale = 1.0
    while x < 1:
        x *= 8
        scale /= 8
    while x >= 8:
        x /= 8
        scale *= 8
    return scale * ((x + 5) / 2 if x <= 3 else 4 * x - 8)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plots", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    points = [-10 + j / 100 for j in range(2001)]
    max_quartic = 0.0
    max_translation = 0.0
    for x in points:
        u = iterates(analytic_f, x, 4)
        max_quartic = max(max_quartic, abs(u[4]-2*u[3]+2*u[2]-2*u[1]+u[0]))
        max_translation = max(max_translation, abs(u[4] - x - 4))
    report = {
        "role": "Floating-point illustration only, not a proof",
        "sample_points": len(points),
        "interval": [-10, 10],
        "max_absolute_quartic_residual": max_quartic,
        "max_absolute_fourth_iterate_translation_residual": max_translation,
        "epsilon": EPSILON,
        "theta": THETA,
        "values_at_zero": iterates(analytic_f, 0.0, 4),
    }
    (root / "data" / "numerical_illustration.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
    if args.plots:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        figures = root / "figures"
        figures.mkdir(exist_ok=True)
        x = [j / 200 for j in range(1601)]
        fig, ax = plt.subplots(figsize=(6.8, 3.6))
        ax.plot(x, [cubic_float(t) for t in x], label=r"$F(x)$")
        ax.plot(x, [2*t for t in x], linestyle="--", label=r"$2x$")
        ax.set(xlabel=r"$x$", ylabel="value", xlim=(0, 8), ylim=(0, 25))
        ax.legend()
        ax.grid(True, alpha=0.25)
        fig.tight_layout()
        fig.savefig(figures / "cubic_counterexample.pdf")
        plt.close(fig)
        x = [j / 200 for j in range(-1600, 1601)]
        fig, ax = plt.subplots(figsize=(6.8, 3.3))
        ax.plot(x, [analytic_f(t)-t for t in x])
        ax.set(xlabel=r"$x$", ylabel=r"$f(x)-x$", xlim=(-8, 8))
        ax.grid(True, alpha=0.25)
        fig.tight_layout()
        fig.savefig(figures / "analytic_displacement.pdf")
        plt.close(fig)


if __name__ == "__main__":
    main()
