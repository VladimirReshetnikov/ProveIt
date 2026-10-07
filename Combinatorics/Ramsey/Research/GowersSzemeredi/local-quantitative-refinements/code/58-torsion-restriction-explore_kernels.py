#!/usr/bin/env python3
"""Finite numerical exploration of repeated powered-cosine filters.

Run: python code/explore_kernels.py
Run without plotting dependencies: python code/explore_kernels.py --no-figure

The numerical search uses the Python standard library. Rendering the figure
requires matplotlib (and its numpy dependency). Search results are approximate
floating-point calculations and are NOT optimality certificates. Exact
exponent-54 arithmetic is checked independently by verify_constants.py.

Attribution: source 04, Section 4 (R8--R9), of the consolidated ProveIt Ramsey
report already introduces the powered-cosine kernel. Source 40 records
one-filter torsion signals. The repeated-filter objective and its asymptotic
comparison are proved in the accompanying article.
"""
import argparse
import csv
import json
from math import ceil, exp, floor, lgamma, log, log1p
from pathlib import Path


LOG2 = log(2)
LOG4 = log(4)
LOG10 = log(10)
ORDERS = (4, 8, 16, 32, 64, 128, 256)


def logsumexp(values):
    maximum = max(values)
    return maximum + log(sum(exp(value-maximum) for value in values))


def scientific_from_log(value):
    """Preserve tiny positive values that would underflow an ordinary exp."""
    exponent = floor(value / LOG10)
    mantissa = exp(value - exponent*LOG10)
    return f"{mantissa:.15f}e{exponent:+d}"


def kernel_values(m, q):
    central = lgamma(2*q+1) - q*LOG4
    logs = [(n, central-lgamma(q+n+1)-lgamma(q-n+1))
            for n in range(-q, q+1)]
    log_q2 = logsumexp([m*b for n, b in logs if n % 2 == 0])
    log_odd = logsumexp([m*b for n, b in logs if n % 2 != 0])
    # P/Q2 = 1 + (sum over odd frequencies)/(sum over even frequencies).
    # This avoids cancellation when q is small and m is large.
    log_ratio = log1p(exp(log_odd-log_q2))
    log_p = log_q2 + log_ratio
    log_r2 = lgamma(4*q+1)-2*lgamma(2*q+1)-2*q*LOG4
    a = -log_p / log_ratio
    z = (log_r2-log_p) / log_ratio
    return {
        "m": m,
        "q": q,
        "P": scientific_from_log(log_p),
        "Q2": scientific_from_log(log_q2),
        "R2": scientific_from_log(log_r2),
        "log_P": log_p,
        "log_Q2": log_q2,
        "log_R2": log_r2,
        "log_P_over_Q2": log_ratio,
        "P_over_Q2": exp(log_ratio),
        "a": a,
        "z": z,
        "a_over_m_log_m": a/(m*log(m)),
    }


def write_csv(path, rows):
    with path.open("w", newline="") as file:
        writer = csv.DictWriter(file, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def render_figure(package_root, best, profile):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.ticker import FixedLocator, FuncFormatter

    plt.rcParams.update({
        "font.family": "DejaVu Sans",
        "font.size": 9,
        "axes.titlesize": 9.4,
        "axes.labelsize": 9,
        "axes.edgecolor": "#84939C",
        "axes.linewidth": 0.8,
        "xtick.color": "#384953",
        "ytick.color": "#384953",
        "text.color": "#21343F",
        "axes.labelcolor": "#21343F",
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
    })
    fig, axes = plt.subplots(1, 2, figsize=(7.35, 3.55), constrained_layout=True)
    teal, plum, gold = "#087E8B", "#714C91", "#AF6F00"
    for axis in axes:
        axis.spines["top"].set_visible(False)
        axis.spines["right"].set_visible(False)
        axis.grid(axis="y", color="#DCE4E8", linewidth=0.7)
        axis.set_axisbelow(True)

    axis = axes[0]
    axis.plot([row["q"] for row in profile], [row["a"] for row in profile],
              color=teal, linewidth=2)
    best16 = min(profile, key=lambda row: row["a"])
    axis.scatter([best16["q"]], [best16["a"]], color=plum, s=43, zorder=4)
    axis.set_yscale("log")
    axis.set_xlim(0, 49)
    axis.set_ylim(40, 700000)
    axis.set_xticks([1, 8, 16, 25, 32, 40, 48])
    axis.set_xlabel(r"Cosine degree $q$")
    axis.set_ylabel(r"Exponent $a_{16}(q)$ (log scale)")
    axis.set_title("(a) Sixteen variables", loc="left", pad=10)
    axis.annotate(f"Best tested: q = {best16['q']}\na = {best16['a']:.6f}",
                  xy=(best16["q"], best16["a"]), xytext=(19, 650),
                  arrowprops={"arrowstyle": "-", "color": plum, "lw": 1},
                  color=plum, fontsize=8.0, va="bottom")
    degree1 = profile[0]
    axis.text(0.97, 0.97, f"Degree 1: a = {degree1['a']:,.1f}",
              transform=axis.transAxes, ha="right", va="top", fontsize=7.4)

    axis = axes[1]
    axis.plot([row["m"] for row in best],
              [row["a_over_m_log_m"] for row in best],
              color=teal, marker="o", markersize=5.4, linewidth=2,
              label=r"Best tested $q\in\{1,\ldots,3m\}$")
    limit = 1/(2*LOG2)
    axis.axhline(limit, color=gold, linestyle="--", linewidth=1.6,
                 label=r"Filter-class limit $1/(2\log 2)$")
    for row in best:
        axis.annotate(f"q={row['q']}",
                      (row["m"], row["a_over_m_log_m"]),
                      textcoords="offset points", xytext=(0, 9), ha="center",
                      fontsize=7.0, color="#526775")
    axis.set_xscale("log", base=2)
    axis.set_xlim(3, 320)
    axis.set_ylim(0.665, 1.53)
    axis.xaxis.set_major_locator(FixedLocator(list(ORDERS)))
    axis.xaxis.set_major_formatter(FuncFormatter(lambda value, _: str(int(value))))
    axis.set_xlabel(r"Tuple length $m$ (log scale)")
    axis.set_ylabel(r"$a_m(q)/(m\log m)$")
    axis.set_title("(b) Growth of the exponent", loc="left", pad=10)
    axis.legend(loc="lower left", bbox_to_anchor=(0.0, 0.12),
                frameon=False, fontsize=7.4, borderaxespad=0.3)

    figure_dir = package_root / "figures"
    figure_dir.mkdir(parents=True, exist_ok=True)
    metadata = {
        "Title": "Repeated cosine filters: finite numerical exploration",
        "Subject": "Finite searches are exploratory; exact exponent-54 proof is independent.",
        "Creator": "code/explore_kernels.py; matplotlib",
    }
    fig.savefig(figure_dir / "kernel_exponents.pdf", metadata=metadata)
    fig.savefig(figure_dir / "kernel_exponents.png", dpi=190)
    plt.close(fig)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--no-figure", action="store_true",
                        help="write numerical data using only the Python standard library")
    args = parser.parse_args()
    package_root = Path(__file__).resolve().parents[1]
    data_dir = package_root / "data"
    data_dir.mkdir(parents=True, exist_ok=True)

    all_rows, best = [], []
    for m in ORDERS:
        rows = [kernel_values(m, q) for q in range(1, ceil(3*m)+1)]
        all_rows.extend(rows)
        winner = min(rows, key=lambda row: row["a"])
        best.append(winner)
    profile = [row for row in all_rows if row["m"] == 16]
    write_csv(data_dir / "cosine_exploration.csv", all_rows)
    write_csv(data_dir / "cosine_best_sampled.csv", best)
    write_csv(data_dir / "cosine_m16_profile.csv", profile)

    metadata = {
        "status": "Finite approximate numerical search; no global optimality claim",
        "arithmetic": "Python double-precision math.lgamma, logsumexp, and log1p",
        "tuple_orders": list(ORDERS),
        "degree_search": "Every integer q from 1 through ceil(3*m), inclusive",
        "total_candidates": len(all_rows),
        "definitions": {
            "P": "sum_{n=-q}^q [4^(-q) binom(2q,q+n)]^m",
            "Q2": "same sum restricted to even n",
            "R2": "4^(-2q) binom(4q,2q)",
            "a": "-log(P)/log(P/Q2)",
            "z": "log(R2/P)/log(P/Q2)"
        },
        "underflow_handling": "P,Q2,R2 are written as scientific-notation strings generated from their logarithms",
        "cancellation_handling": "log(P/Q2) = log1p(exp(log_odd_sum - log_even_sum))",
        "rounded_ratio_note": "P_over_Q2 can round to 1.0 for small q and large m; log_P_over_Q2 retains the positive gap used to compute a and z",
        "best_sampled": best,
        "all_best_degrees_are_interior_to_the_tested_range":
            all(1 < row["q"] < 3*row["m"] for row in best),
        "asymptotic_reference": 1/(2*LOG2),
        "asymptotic_reference_scope": "Infimum over the article's entire positive-Fourier filter class, not a claim about the limit of the bounded search q<=3m",
        "exact_theorem": "Independent of these numerical searches; see verify_constants.py",
        "generated_by": "code/explore_kernels.py"
    }
    (data_dir / "exploration_metadata.json").write_text(json.dumps(metadata, indent=2)+"\n")
    if not args.no_figure:
        render_figure(package_root, best, profile)
    print(json.dumps({
        "candidates": len(all_rows),
        "status": metadata["status"],
        "best_sampled": [
            {key: row[key] for key in ("m", "q", "a", "z", "P_over_Q2")}
            for row in best
        ],
        "figures_rendered": not args.no_figure,
        "output_directory": str(package_root)
    }, indent=2))


if __name__ == "__main__":
    main()
