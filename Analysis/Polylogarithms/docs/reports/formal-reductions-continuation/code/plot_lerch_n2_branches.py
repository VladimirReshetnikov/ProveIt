#!/usr/bin/env python3
"""Numerical diagnostic figure for the two n=2,k=1 Lerch zero branches.

The complete zero count and nonmonotonicity are proved in the accompanying
TeX. This script plots numerical continuations. It uses the Appell--Laplace
integral with u=log(x), safeguarded Newton iteration, and independent
Lerch/Hurwitz spectral residual checks at selected parameters.

Dependencies: mpmath, matplotlib. No special LaTeX installation is required.
"""

from pathlib import Path
import argparse
import csv
import json
import time

import mpmath as mp
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt


def parameter_grid():
    initial = [format(j / 40, ".3f").rstrip("0").rstrip(".")
               for j in range(37)]
    initial[0] = "0"
    return initial + ["0.925", "0.95", "0.97", "0.98", "0.99",
                      "0.995", "0.9975", "0.999", "0.9995", "0.9999",
                      "0.99999", "0.999999", "0.9999999", "1"]


def render(rows, out):
    plt.rcParams.update({"font.family": "serif", "font.serif": ["DejaVu Serif"],
                         "mathtext.fontset": "dejavuserif", "font.size": 11,
                         "axes.labelsize": 12, "axes.titlesize": 13,
                         "pdf.fonttype": 42, "ps.fonttype": 42,
                         "axes.spines.top": False, "axes.spines.right": False})
    xs = [float(r["rho"]) for r in rows]
    ys = [[float(r[f"a{j}"]) for r in rows] for j in (1, 2)]
    fig, axes = plt.subplots(1, 2, figsize=(10.2, 4.6))
    colors = ["#174A7E", "#A34521"]
    titles = ["Smaller zero: a nonmonotone branch", "Larger zero"]
    for branch, (ax, values, color, title) in enumerate(zip(axes, ys, colors, titles), 1):
        ax.plot(xs, values, color=color, linewidth=2.2, zorder=3)
        ax.scatter(xs, values, color=color, s=9, alpha=0.48, linewidths=0, zorder=4)
        ax.scatter([0, 1], [values[0], values[-1]], s=42, edgecolor=color,
                   facecolor="white", linewidth=1.7, zorder=5)
        ax.set_xlim(-0.025, 1.025)
        ax.set_xlabel(r"Lerch parameter $\rho$")
        ax.set_ylabel(rf"Positive zero $a_{branch}(\rho)$")
        ax.set_title(title, loc="left", pad=13)
        ax.grid(axis="both", color="#DDE3E8", linewidth=0.65, alpha=0.8)
        span = max(values) - min(values)
        ax.set_ylim(min(values) - 0.17 * span, max(values) + 0.22 * span)
        endpoint_label = rf"$a_{branch}(1)\approx {values[-1]:.8f}$"
        ax.annotate(endpoint_label, (1, values[-1]), xytext=(-7, 12),
                    textcoords="offset points", ha="right", va="bottom", color=color,
                    fontsize=10)
    axes[0].axhline(1, color="#818C98", linewidth=1, linestyle=(0, (4, 3)), zorder=1)
    axes[0].annotate(r"$a_1(0)=1$", (0, 1), xytext=(9, 10), textcoords="offset points",
                     ha="left", color=colors[0], fontsize=10)
    axes[1].annotate(r"$a_2(0)=e^2$", (0, ys[1][0]), xytext=(9, 10),
                     textcoords="offset points", ha="left", color=colors[1], fontsize=10)
    fig.suptitle(r"Two zero branches of $\mathcal{D}_{2,1}^{\rho}(a)$", x=0.055,
                 ha="left", y=0.995, fontsize=17)
    fig.text(0.055, 0.025,
             "Numerical continuation at 51 parameters; selected residuals checked through a separate spectral formula.\n"
             "The exact two-zero theorem and nonmonotonicity proof do not depend on the plotted samples.",
             ha="left", va="bottom", fontsize=9, color="#47515C")
    fig.subplots_adjust(left=0.087, right=0.985, bottom=0.23, top=0.78, wspace=0.30)
    fig.savefig(out / "lerch_n2_branches.pdf", bbox_inches="tight")
    fig.savefig(out / "lerch_n2_branches.png", dpi=210, bbox_inches="tight")
    plt.close(fig)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--dps", type=int, default=38)
    parser.add_argument("--render-only", action="store_true")
    parser.add_argument("--output-dir", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data")
    parser.add_argument("--figure-dir", type=Path,
                        default=Path(__file__).resolve().parents[1] / "article" / "figures")
    args = parser.parse_args()
    out = args.output_dir
    out.mkdir(parents=True, exist_ok=True)
    args.figure_dir.mkdir(parents=True, exist_ok=True)
    if args.render_only:
        with (out / "lerch_n2_branches.csv").open(newline="") as handle:
            render(list(csv.DictReader(handle)), args.figure_dir)
        return
    mp.mp.dps = args.dps
    start = time.monotonic()
    euler = mp.euler
    zeta2 = mp.zeta(2)
    rootgap = mp.sqrt(zeta2)
    integration_intervals = [-100, -40, -20, -10, -5,
                             -euler - rootgap, -euler + rootgap, 2, 6]
    tolerance = mp.mpf("1e-29")

    def laplace_value_and_derivative(a, rho):
        one_minus_rho = 1 - rho

        def integrand(u):
            x = mp.exp(u)
            denominator = one_minus_rho - rho * mp.expm1(-x)
            kernel = (mp.exp(2 * u - a * x) / denominator
                      * ((u + euler) ** 2 - zeta2))
            return kernel * (1 - 1j * x)

        value = mp.quad(integrand, integration_intervals,
                        method="gauss-legendre")
        return mp.re(value), mp.im(value)

    def root(rho, old, lower, upper):
        left = mp.mpf(lower)
        right = mp.mpf(upper)
        fleft, _ = laplace_value_and_derivative(left, rho)
        fright, _ = laplace_value_and_derivative(right, rho)
        assert fleft * fright < 0, (rho, left, right, fleft, fright)
        a = min(max(old, left), right)
        for iterations in range(1, 81):
            value, derivative = laplace_value_and_derivative(a, rho)
            if abs(value) < tolerance:
                return a, value, derivative, iterations
            if fleft * value > 0:
                left, fleft = a, value
            else:
                right = a
            candidate = a - value / derivative
            a = candidate if left < candidate < right else (left + right) / 2
        raise RuntimeError(f"Newton/bisection did not converge at rho={rho}")

    rows = []
    first, second = mp.mpf(1), mp.exp(2)
    parameters = parameter_grid()
    for index, rho_string in enumerate(parameters):
        rho = mp.mpf(rho_string)
        if rho == 0:
            v1, d1 = laplace_value_and_derivative(first, rho)
            v2, d2 = laplace_value_and_derivative(second, rho)
            iterations1 = iterations2 = 0
        else:
            first, v1, d1, iterations1 = root(rho, first, "0.5", "1.3")
            second, v2, d2, iterations2 = root(rho, second, "1.3", mp.exp(2))
        assert first < mp.mpf("1.3") < second
        assert abs(v1) < mp.mpf("1e-27") and abs(v2) < mp.mpf("1e-27")
        rows.append({"rho": rho_string,
                     "a1": mp.nstr(first, args.dps),
                     "a2": mp.nstr(second, args.dps),
                     "laplace_residual1": mp.nstr(v1, 8),
                     "laplace_residual2": mp.nstr(v2, 8),
                     "derivative_a1": mp.nstr(d1, 16),
                     "derivative_a2": mp.nstr(d2, 16),
                     "iterations1": iterations1,
                     "iterations2": iterations2})
        if index % 10 == 0 or index == len(parameters) - 1:
            print(f"Computed {index+1}/{len(parameters)} parameters; rho={rho_string}",
                  flush=True)

    # Independent representation: G_{2,1} = Phi''(rho,2,a)+2 Phi'(rho,2,a).
    # At rho=1 replace Phi by the Hurwitz zeta; at zero use the elementary
    # closed form. These computations use higher precision and do not reuse
    # the Appell polynomial or the Laplace quadrature above.
    independent_checks = []
    wanted = {"0", "0.5", "0.9", "0.99", "0.9999", "0.9999999", "1"}
    with mp.workdps(args.dps + 7):
        for row in rows:
            if row["rho"] not in wanted:
                continue
            rho = mp.mpf(row["rho"])
            for branch in (1, 2):
                a = mp.mpf(row[f"a{branch}"])
                if rho == 0:
                    value = mp.log(a) * (mp.log(a) - 2) / a ** 2
                    representation = "elementary"
                else:
                    spectral = ((lambda s: mp.zeta(s, a)) if rho == 1 else
                                (lambda s: mp.lerchphi(rho, s, a)))
                    value = mp.diff(spectral, 2, 2) + 2 * mp.diff(spectral, 2)
                    representation = "Hurwitz spectral" if rho == 1 else "Lerch spectral"
                assert abs(value) < mp.mpf("1e-26"), (rho, branch, value)
                independent_checks.append({"rho": row["rho"], "branch": branch,
                                           "representation": representation,
                                           "absolute_residual": mp.nstr(abs(value), 14)})
            print(f"Independent spectral residuals checked at rho={row['rho']}", flush=True)

    csv_path = out / "lerch_n2_branches.csv"
    with csv_path.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)

    receipt = {
        "status": "PASS",
        "nature": "high-precision numerical diagnostic, not a zero-count certificate",
        "normalization": "G_{2,1}=(-1)^3 D_{2,1}",
        "precision_decimal_digits": args.dps,
        "parameters": len(rows),
        "newton_method": "safeguarded Newton using Appell--Laplace integral and derivative",
        "integration_variable": "u=log(x)",
        "integration_interval": [-100, 6],
        "residual_note": "finite quadrature tails are negligible at the recorded precision; not interval certified",
        "maximum_laplace_absolute_residual": mp.nstr(max(
            abs(mp.mpf(r[f"laplace_residual{j}"])) for r in rows for j in (1, 2)), 14),
        "independent_spectral_checks": independent_checks,
        "maximum_independent_spectral_residual": mp.nstr(max(
            mp.mpf(c["absolute_residual"]) for c in independent_checks), 14),
        "endpoint_values": {"rho0": {"a1": rows[0]["a1"], "a2": rows[0]["a2"]},
                            "rho1": {"a1": rows[-1]["a1"], "a2": rows[-1]["a2"]}},
        "sampled_minimum_a1": min(rows, key=lambda r: mp.mpf(r["a1"])),
        "elapsed_seconds_before_render": round(time.monotonic() - start, 3)
    }
    (out / "lerch_n2_branches.json").write_text(json.dumps(receipt, indent=2) + "\n")

    render(rows, args.figure_dir)
    print(json.dumps({"parameters": len(rows),
                      "independent_checks": len(independent_checks),
                      "maximum_independent_residual": receipt["maximum_independent_spectral_residual"],
                      "endpoint_rho1": receipt["endpoint_values"]["rho1"],
                      "sampled_minimum_rho": receipt["sampled_minimum_a1"]["rho"],
                      "elapsed_seconds": round(time.monotonic() - start, 2),
                      "output_dir": str(out)}, indent=2))


if __name__ == "__main__":
    main()
