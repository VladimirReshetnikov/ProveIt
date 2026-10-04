#!/usr/bin/env python3
"""Reproduce the article's exact checks, floating-point checks, and figures.

Run from any directory:
    python verification/verification.py

Requires Python >= 3.10, mpmath, numpy, and matplotlib.  The coefficient and
combinatorial assertions use exact integers and fractions.  Numerical root
and integral checks use 110 decimal digits; they are not interval arithmetic.
No internet connection, article source, or repository checkout is required.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import json
import math
from pathlib import Path

import mpmath as mp


HERE = Path(__file__).resolve().parent
FIGURES = HERE.parent / "figures"


@dataclass(frozen=True)
class Gaussian:
    """A Gaussian rational, represented without floating-point arithmetic."""

    real: Fraction = Fraction(0)
    imag: Fraction = Fraction(0)

    def __add__(self, other: "Gaussian") -> "Gaussian":
        return Gaussian(self.real + other.real, self.imag + other.imag)

    def __neg__(self) -> "Gaussian":
        return Gaussian(-self.real, -self.imag)

    def __mul__(self, other: "Gaussian") -> "Gaussian":
        return Gaussian(
            self.real * other.real - self.imag * other.imag,
            self.real * other.imag + self.imag * other.real,
        )

    def scale(self, c: Fraction) -> "Gaussian":
        return Gaussian(c * self.real, c * self.imag)

    def __pow__(self, n: int) -> "Gaussian":
        assert n >= 0
        answer, base = ONE, self
        while n:
            if n & 1:
                answer = answer * base
            base = base * base
            n >>= 1
        return answer


ZERO = Gaussian()
ONE = Gaussian(Fraction(1))
MINUS_ONE = -ONE
MINUS_I = Gaussian(Fraction(0), Fraction(-1))
Polynomial = dict[tuple[int, int], Gaussian]


def clean(p: Polynomial) -> Polynomial:
    return {monomial: c for monomial, c in p.items() if c != ZERO}


def poly_add(p: Polynomial, q: Polynomial) -> Polynomial:
    answer = dict(p)
    for monomial, c in q.items():
        answer[monomial] = answer.get(monomial, ZERO) + c
    return clean(answer)


def poly_scale(p: Polynomial, c: Gaussian) -> Polynomial:
    return clean({monomial: value * c for monomial, value in p.items()})


def poly_mul(p: Polynomial, q: Polynomial, degree: int) -> Polynomial:
    answer: Polynomial = {}
    for (m, n), a in p.items():
        for (r, s), b in q.items():
            if m + n + r + s <= degree:
                key = m + r, n + s
                answer[key] = answer.get(key, ZERO) + a * b
    return clean(answer)


def poly_shift(p: Polynomial, dx: int, dy: int, degree: int) -> Polynomial:
    return {
        (m + dx, n + dy): c
        for (m, n), c in p.items()
        if m + n + dx + dy <= degree
    }


def poly_exp(p: Polynomial, c: Gaussian, degree: int) -> Polynomial:
    """Truncated exp(c*p), for p of positive total order."""
    assert p.get((0, 0), ZERO) == ZERO
    cp = poly_scale(p, c)
    result: Polynomial = {(0, 0): ONE}
    power: Polynomial = {(0, 0): ONE}
    for k in range(1, degree + 1):
        power = poly_mul(power, cp, degree)
        if not power:
            break
        result = poly_add(
            result,
            {monomial: value.scale(Fraction(1, math.factorial(k)))
             for monomial, value in power.items()},
        )
    return result


def inverse_polynomial(degree: int) -> Polynomial:
    return {
        (m, n): (Gaussian(Fraction(m), Fraction(n)) ** (m + n - 1)).scale(
            Fraction(-1, math.factorial(m) * math.factorial(n))
        )
        for m in range(degree + 1)
        for n in range(degree + 1 - m)
        if m + n >= 1
    }


def exact_inverse_checks(degree: int = 10) -> dict:
    delta = inverse_polynomial(degree)
    x_term = poly_shift(poly_exp(delta, MINUS_ONE, degree), 1, 0, degree)
    y_term = poly_shift(poly_exp(delta, MINUS_I, degree), 0, 1, degree)
    residual = poly_add(poly_add(delta, x_term), y_term)
    assert residual == {}, residual

    # An independent construction by formal fixed-point iteration.
    iterate: Polynomial = {}
    for _ in range(degree):
        x_term = poly_shift(poly_exp(iterate, MINUS_ONE, degree), 1, 0, degree)
        y_term = poly_shift(poly_exp(iterate, MINUS_I, degree), 0, 1, degree)
        iterate = poly_scale(poly_add(x_term, y_term), MINUS_ONE)
    assert iterate == delta

    return {
        "arithmetic": "exact Gaussian rationals (fractions.Fraction)",
        "total_degree": degree,
        "nonconstant_coefficients_checked": len(delta),
        "implicit_residual_is_zero": True,
        "independent_fixed_point_coefficients_agree": True,
        "coefficient_formula": "-(m+i*n)^(m+n-1)/(m!*n!)",
        "coefficients": [
            {"m": m, "n": n, "real": str(c.real), "imag": str(c.imag)}
            for (m, n), c in sorted(delta.items(), key=lambda item: (sum(item[0]), item[0]))
        ],
    }


def totient(n: int) -> int:
    return sum(math.gcd(k, n) == 1 for k in range(1, n + 1))


def wall_ratios(degree: int) -> set[Fraction]:
    return {
        Fraction(p, q)
        for p in range(1, degree + 1)
        for q in range(1, degree + 1)
        if math.gcd(p, q) == 1
    }


def exact_wall_checks(max_degree: int = 12) -> list[dict]:
    result = []
    for degree in range(1, max_degree + 1):
        support = [(m, n) for m in range(degree + 1)
                   for n in range(degree + 1 - m) if m + n > 0]
        induced = set()
        for m, n in support:
            for r, s in support:
                p, q = m - r, s - n
                if p > 0 and q > 0:
                    induced.add(Fraction(p, q))
        expected = wall_ratios(degree)
        assert induced == expected
        formula_count = 2 * sum(totient(k) for k in range(1, degree + 1)) - 1
        assert len(expected) == formula_count
        result.append({
            "degree": degree,
            "support_size": len(support),
            "interior_walls": len(expected),
            "open_chambers": len(expected) + 1,
            "count_formula": "2*sum(phi(k), k=1..N)-1",
            "pairwise_action_check_passed": True,
            "wall_slopes": [str(x) for x in sorted(expected)],
        })
    return result


def decimal(x: mp.mpf | mp.mpc, digits: int = 45) -> str | dict:
    if isinstance(x, mp.mpc):
        return {"real": mp.nstr(x.real, digits), "imag": mp.nstr(x.imag, digits)}
    return mp.nstr(x, digits)


def truncation(w: mp.mpc, a: mp.mpf, b: mp.mpf, degree: int) -> mp.mpc:
    terms = []
    for k in range(1, degree + 1):
        for m in range(k + 1):
            n = k - m
            action = mp.mpc(m, n)
            terms.append(
                -(action ** (k - 1)) * a ** m * b ** n * mp.exp(-action * w)
                / (mp.factorial(m) * mp.factorial(n))
            )
    return w + mp.fsum(terms)


def numerical_inverse_checks() -> list[dict]:
    a, b = mp.mpf(1) / 3, mp.mpf(1) / 4
    answer = []
    for w in [mp.mpc(4, -3), mp.mpc(6, -4)]:
        f = lambda z: z + a * mp.exp(-z) + b * mp.exp(-mp.j * z) - w
        root = mp.findroot(f, (w, w - mp.mpf("0.01")), tol=mp.mpf("1e-105"))
        residual = abs(f(root))
        assert residual < mp.mpf("1e-100")
        action_norm = abs(a) * mp.exp(-w.real) + abs(b) * mp.exp(w.imag)
        kappa = mp.e * action_norm
        assert kappa < 1
        assert abs(root - w) < 1
        rows = []
        for degree in [1, 2, 4, 8, 12]:
            approximation = truncation(w, a, b, degree)
            error = abs(approximation - root)
            bound = kappa ** (degree + 1) / ((degree + 1) * (1 - kappa))
            assert error < bound
            rows.append({
                "degree": degree,
                "approximation": decimal(approximation),
                "absolute_error": decimal(error),
                "theorem_tail_bound": decimal(bound),
                "error_over_bound": decimal(error / bound),
                "measured_error_less_than_bound": True,
            })
        answer.append({
            "a": "1/3", "b": "1/4", "w": decimal(w),
            "root": decimal(root), "root_residual": decimal(residual),
            "kappa": decimal(kappa), "radius": 1, "rows": rows,
        })
    return answer


def catalan(n: int) -> int:
    return math.comb(2 * n, n) // (n + 1)


def borel_checks(terms: int = 25) -> dict:
    # For F(z)=z+a/z, g(w)-w=-sum C_n*a^(n+1)*w^(-2n-1).
    # B(w^(-k-1))=zeta^k/k! gives the I_1 expression exactly.
    for n in range(terms):
        assert Fraction(catalan(n), math.factorial(2 * n)) == Fraction(
            1, math.factorial(n) * math.factorial(n + 1)
        )
        if n > 0:
            assert catalan(n) == sum(catalan(j) * catalan(n - 1 - j) for j in range(n))

    a = mp.mpf(1) / 4
    q = mp.mpf(2)
    kernel = lambda zeta: (
        a if zeta == 0 else a * mp.besseli(1, 2 * mp.sqrt(a) * zeta)
        / (mp.sqrt(a) * zeta)
    )
    laplace = mp.quad(lambda t: mp.exp(-q * t) * kernel(t), [0, 1, 5, mp.inf])
    displacement = (q - mp.sqrt(q * q - 4 * a)) / 2
    numerical_error = abs(laplace - displacement)
    assert numerical_error < mp.mpf("1e-100")
    return {
        "exact_Catalan_Bessel_coefficients_checked": terms,
        "exact_Catalan_quadratic_recurrences_checked": terms - 1,
        "borel_convention": "B(w^(-k-1))=zeta^k/k!",
        "inverse_borel_transform": "-a*I_1(2*sqrt(a)*zeta)/(sqrt(a)*zeta)",
        "positive_displacement": "w-g(w)",
        "positive_displacement_laplace": "(q-sqrt(q^2-4*a))/2",
        "numerical_parameters": {"a": "1/4", "q": "2"},
        "laplace_integral": decimal(laplace),
        "algebraic_displacement": decimal(displacement),
        "absolute_difference": decimal(numerical_error),
    }


def within_cost(m: int, n: int, budget: int) -> bool:
    """Exact test of |m|+|n|/sqrt(2) <= an integer budget."""
    remainder = budget - abs(m)
    return remainder >= 0 and n * n <= 2 * remainder * remainder


def cost_points(max_cost: int = 8) -> list[dict]:
    alpha = math.sqrt(2)
    result = []
    for m in range(-math.ceil(max_cost), math.ceil(max_cost) + 1):
        for n in range(-math.ceil(alpha * max_cost), math.ceil(alpha * max_cost) + 1):
            if m == 0 and n == 0:
                continue
            cost = abs(m) + abs(n) / alpha
            if within_cost(m, n, max_cost):
                result.append({"m": m, "n": n, "projection": m + n / alpha, "cost": cost})
    # The zero point records the nonempty return path +1/alpha,-1/alpha,
    # whose cost is 2/alpha.  It is not the cost-zero empty path.
    result.append({"m": None, "n": None, "projection": 0.0,
                   "cost": 2 / alpha, "nonempty_return_path": True})
    return sorted(result, key=lambda p: (p["cost"], p["projection"]))


def cost_checks() -> dict:
    points = cost_points()
    budgets = [2, 4, 6, 8]
    counts = []
    for budget in budgets:
        included = [p for p in points
                    if p.get("nonempty_return_path", False) and budget >= 2
                    or p["m"] is not None and within_cost(p["m"], p["n"], budget)]
        # Algebraic uniqueness of m+n/sqrt(2) is known exactly; this guards
        # accidental duplicate generation at the plotted finite scale.
        assert len({(p["m"], p["n"]) for p in included}) == len(included)
        counts.append({"budget": budget, "candidate_points_including_return_zero": len(included)})
    return {
        "alpha": "sqrt(2)",
        "max_cost": 8,
        "budget_membership_arithmetic": "exact integers: n^2 <= 2*(L-|m|)^2 and |m|<=L",
        "zero_return_cost": "2/sqrt(2)",
        "interpretation": "candidate filtered locations, not a claim that all are actual singularities",
        "budget_counts": counts,
        "points": points,
    }


def setup_matplotlib():
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    plt.rcParams.update({
        "font.family": "DejaVu Serif", "font.size": 9,
        "mathtext.fontset": "stix", "axes.titlesize": 12,
        "axes.labelsize": 10, "pdf.fonttype": 42, "ps.fonttype": 42,
        "savefig.facecolor": "white", "figure.facecolor": "white",
        "axes.spines.top": False, "axes.spines.right": False,
    })
    return plt


def angular_atlas_figure() -> None:
    import numpy as np
    from matplotlib.patches import Wedge
    plt = setup_matplotlib()
    fig, axes = plt.subplots(1, 3, figsize=(7.1, 2.75))
    blue, dark, gray = "#16617c", "#223343", "#8b969d"
    for ax, degree in zip(axes, [3, 6, 12]):
        ratios = sorted(wall_ratios(degree))
        ax.add_patch(Wedge((0, 0), 1, -90, 0, facecolor="#f1f6f8", edgecolor="none"))
        for ratio in ratios:
            theta = -math.atan(float(ratio))
            ax.plot([0, math.cos(theta)], [0, math.sin(theta)],
                    color=blue, lw=0.80 if degree < 12 else 0.43, alpha=0.82)
        theta = np.linspace(-math.pi / 2, 0, 400)
        ax.plot(np.cos(theta), np.sin(theta), color=gray, lw=0.7)
        ax.annotate("", xy=(1.11, 0), xytext=(-0.03, 0),
                    arrowprops=dict(arrowstyle="->", lw=0.8, color=dark))
        ax.annotate("", xy=(0, -1.10), xytext=(0, 0.04),
                    arrowprops=dict(arrowstyle="->", lw=0.8, color=dark))
        ax.text(1.105, 0.045, r"$\Re w$", ha="right", va="bottom", color=dark)
        ax.text(-0.01, -1.105, r"$\Im w$", ha="left", va="top", color=dark)
        ax.text(-0.055, 0.035, r"$0$", ha="right", va="bottom", color=dark)
        ax.text(0.99, -0.035, r"$0$", ha="right", va="top", fontsize=8, color=gray)
        ax.text(0.025, -0.975, r"$-\pi/2$", ha="left", va="top", fontsize=8, color=gray)
        ax.set_title(rf"$N={degree}$", pad=9, color=dark)
        ax.text(0.54, -1.23, f"{len(ratios)} walls  /  {len(ratios)+1} chambers",
                ha="center", va="top", fontsize=9, color=dark)
        ax.set(xlim=(-0.11, 1.15), ylim=(-1.32, 0.12), aspect="equal")
        ax.axis("off")
    fig.subplots_adjust(left=0.03, right=0.99, top=0.88, bottom=0.08, wspace=0.20)
    fig.savefig(FIGURES / "finite_angular_atlases.pdf", bbox_inches="tight", pad_inches=0.035)
    fig.savefig(FIGURES / "finite_angular_atlases.png", dpi=300, bbox_inches="tight", pad_inches=0.035)
    plt.close(fig)


def cost_filter_figure() -> None:
    import numpy as np
    plt = setup_matplotlib()
    points = cost_points()
    regular = [p for p in points if not p.get("nonempty_return_path", False)]
    xx = np.array([p["projection"] for p in regular])
    yy = np.array([p["cost"] for p in regular])
    fig = plt.figure(figsize=(7.1, 3.3))
    gs = fig.add_gridspec(1, 2, width_ratios=[1.9, 1], wspace=0.35)
    ax, rug = fig.add_subplot(gs[0, 0]), fig.add_subplot(gs[0, 1])
    palette = ["#aac5cf", "#6f9dae", "#36778e", "#174f6a"]
    colors = [palette[min(3, max(0, math.ceil(c / 2) - 1))] for c in yy]
    ax.scatter(xx, yy, s=13, c=colors, alpha=0.85, linewidths=0, zorder=3)
    ax.scatter([0], [math.sqrt(2)], s=35, c="#c46a30", marker="D", zorder=5)
    ax.annotate("nonempty return", xy=(0, math.sqrt(2)), xytext=(0.45, 0.28),
                fontsize=8, color="#9d4d1e",
                arrowprops=dict(arrowstyle="-", lw=0.7, color="#c46a30"))
    for budget in [2, 4, 6, 8]:
        ax.axhline(budget, color="#a8b4ba", lw=0.65, ls=(0, (3, 3)), zorder=1)
    ax.plot([-8, 0, 8], [8, 0, 8], color="#c9d1d5", lw=0.8, zorder=1)
    ax.set(xlim=(-8.5, 8.5), ylim=(0, 8.5), xticks=[-8, -4, 0, 4, 8], yticks=[0, 2, 4, 6, 8])
    ax.set_xlabel(r"Projected location $m+n/\sqrt{2}$")
    ax.set_ylabel(r"Continuation cost $|m|+|n|/\sqrt{2}$")
    ax.set_title("Finite sets at each cost", loc="left", pad=11)
    ax.tick_params(length=3, width=0.7, colors="#394c58")
    for spine in ["left", "bottom"]:
        ax.spines[spine].set_color("#acb8bf")

    budgets = [2, 4, 6, 8]
    for level, budget in enumerate(budgets):
        projected = [p["projection"] for p in points
                     if p["cost"] <= budget and abs(p["projection"]) <= 2]
        rug.vlines(projected, level - 0.22, level + 0.22,
                   color=palette[level], linewidth=0.95)
        rug.axhline(level, color="#e1e6e9", lw=0.65, zorder=0)
    rug.set(xlim=(-2.12, 2.12), ylim=(-0.55, 3.6),
            xticks=[-2, -1, 0, 1, 2], yticks=[0, 1, 2, 3],
            yticklabels=[r"$L=2$", r"$L=4$", r"$L=6$", r"$L=8$"])
    rug.set_title("Projections near zero", loc="left", pad=11)
    rug.set_xlabel("Projected location")
    rug.spines["left"].set_visible(False)
    rug.spines["bottom"].set_color("#acb8bf")
    rug.tick_params(axis="y", length=0, pad=4)
    rug.tick_params(axis="x", length=3, width=0.7, colors="#394c58")
    fig.subplots_adjust(left=0.082, right=0.98, top=0.87, bottom=0.18)
    fig.savefig(FIGURES / "cost_filtered_locations.pdf", bbox_inches="tight", pad_inches=0.04)
    fig.savefig(FIGURES / "cost_filtered_locations.png", dpi=300, bbox_inches="tight", pad_inches=0.04)
    plt.close(fig)


def scientific_tex(x: str) -> str:
    mantissa, exponent = mp.nstr(mp.mpf(x), 5, min_fixed=0, max_fixed=0).split("e")
    return rf"{mantissa}\mathbin{{\times}}10^{{{int(exponent)}}}"


def write_table(data: dict) -> None:
    lines = [
        "% Generated by verification.py. Numerical measurements are not interval arithmetic.",
        r"\begin{tabular}{@{}crrr@{}}",
        r"\toprule",
        r"$w$ & $N$ & Measured error & Proven tail bound \\",
        r"\midrule",
    ]
    for case_index, case in enumerate(data["numerical_inverse"]):
        w = "4-3i" if case_index == 0 else "6-4i"
        for row_index, row in enumerate(case["rows"]):
            label = rf"${w}$" if row_index == 0 else ""
            lines.append(
                rf"{label} & {row['degree']} & ${scientific_tex(row['absolute_error'])}$"
                rf" & ${scientific_tex(row['theorem_tail_bound'])}$ \\")
        if case_index == 0:
            lines.append(r"\addlinespace")
    lines.extend([r"\bottomrule", r"\end{tabular}", ""])
    (HERE / "numerical_table.tex").write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--no-figures", action="store_true", help="Run checks without creating plots.")
    args = parser.parse_args()
    mp.mp.dps = 110
    print("Checking Gaussian-rational coefficients through total degree 10...", flush=True)
    exact_inverse = exact_inverse_checks()
    print("Checking exact wall sets and Euler-totient counts...", flush=True)
    walls = exact_wall_checks()
    print("Checking two-action inverse values at 110 decimal digits...", flush=True)
    inverse = numerical_inverse_checks()
    print("Checking Catalan/Bessel normalization and Laplace integral...", flush=True)
    borel = borel_checks()
    costs = cost_checks()
    data = {
        "status": "all assertions passed",
        "precision_decimal_digits": mp.mp.dps,
        "numerical_status": "floating-point consistency checks, not interval arithmetic",
        "exact_inverse": exact_inverse,
        "angular_walls": walls,
        "numerical_inverse": inverse,
        "sharp_borel_example": borel,
        "cost_filtered_example": costs,
    }
    (HERE / "results.json").write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    write_table(data)
    if not args.no_figures:
        FIGURES.mkdir(parents=True, exist_ok=True)
        print("Exporting figures as PDF and 300 dpi PNG...", flush=True)
        angular_atlas_figure()
        cost_filter_figure()
    print("All assertions passed.", flush=True)
    for case in inverse:
        print("w =", case["w"], "kappa =", case["kappa"])
        for row in case["rows"]:
            print("  N =", row["degree"], "error =", row["absolute_error"],
                  "bound =", row["theorem_tail_bound"])
    print("Wall counts:", {r["degree"]: r["interior_walls"] for r in walls if r["degree"] in [3, 6, 12]})
    print("Filtered counts:", costs["budget_counts"])


if __name__ == "__main__":
    main()
