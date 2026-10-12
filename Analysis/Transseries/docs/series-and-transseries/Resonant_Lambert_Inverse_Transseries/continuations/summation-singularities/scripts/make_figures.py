#!/usr/bin/env python3
"""Regenerate article tables and vector figures from the retained JSON data.

This program formats existing diagnostics; it does not run the mathematical
checks. Run the three verify_*.py programs to regenerate their inputs.
"""
from pathlib import Path
import json
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import NullFormatter

ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / "results"
FIGURES = ROOT / "figures"


def sci(value, digits=3):
    coefficient, exponent = f"{float(value):.{digits - 1}e}".split("e")
    return rf"${coefficient}\times10^{{{int(exponent)}}}$"


def table(path, columns, headings, rows):
    lines = [rf"\begin{{tabular}}{{{columns}}}", r"\toprule",
             " & ".join(headings) + r" \\", r"\midrule"]
    lines.extend(" & ".join(map(str, row)) + r" \\" for row in rows)
    lines.extend([r"\bottomrule", r"\end{tabular}", ""])
    path.write_text("\n".join(lines), encoding="utf-8")


def main():
    angular = json.loads((RESULTS / "angular_checks.json").read_text())
    lambert = json.loads((RESULTS / "lambert_checks.json").read_text())
    table(RESULTS / "angular_table.tex", "rrrr",
          ["$a$", "$K$", "Numerical error", "Proved upper bound"],
          [(r["a"], r["K"], sci(r["error"]), sci(r["proved_bound"]))
           for r in angular["angular"] if r["K"] in [4, 8, 16]])
    table(RESULTS / "moving_table.tex", "rrrrr",
          ["$a$", "$M$", "$K$", "Numerical error", "Proved upper bound"],
          [(r["a"], r["M"], r["K"], sci(r["error"]), sci(r["proved_bound"]))
           for r in angular["moving_cutoff"]])
    lm = [r for r in lambert["rows"]
          if r["u"]["real"] == "0.1" and r["u"]["imag"] == "0.0"]
    table(RESULTS / "lambert_table.tex", "rrr",
          ["$n$", "Leading-term error", "Error with first correction"],
          [(r["n"], sci(r["absolute_leading_error"], 4),
            sci(r["absolute_refined_error"], 4))
           for r in lm if r["n"] in [40, 41, 80, 81, 200, 201]])

    plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 9,
                         "axes.labelsize": 9, "axes.titlesize": 10,
                         "axes.spines.top": False, "axes.spines.right": False,
                         "axes.edgecolor": "#667480", "axes.labelcolor": "#18374C",
                         "xtick.color": "#465663", "ytick.color": "#465663",
                         "pdf.fonttype": 42, "ps.fonttype": 42})
    fig, ax = plt.subplots(1, 2, figsize=(7.25, 3.05), constrained_layout=True)
    colors = ["#087F8C", "#BF5C31", "#665191"]
    for a, color in zip([6, 8, 10], colors):
        rows = [r for r in angular["angular"] if r["a"] == a]
        ax[0].semilogy([r["K"] for r in rows],
                       [float(r["error"]) for r in rows],
                       marker="o", ms=4, lw=1.4, color=color, label=rf"$a={a}$")
    ax[0].set(title="Angular degree reconstruction", xlabel="Retained degree K",
              ylabel="Absolute numerical error", xticks=[1, 4, 8, 12, 16])
    ax[0].legend(frameon=False, loc="lower left", fontsize=8)
    for parity, color, marker in [(0, colors[0], "o"), (1, colors[1], "s")]:
        rows = [r for r in lm if r["n"] % 2 == parity]
        label = "even n" if parity == 0 else "odd n"
        ax[1].loglog([r["n"] for r in rows],
                     [float(r["absolute_leading_error"]) for r in rows],
                     color=color, marker=marker, ms=4, lw=1.4, label=label)
        ax[1].loglog([r["n"] for r in rows],
                     [float(r["absolute_refined_error"]) for r in rows],
                     color=color, marker=marker, ms=4, lw=1.4, ls="--")
    ax[1].set(title="Lambert late coefficients, u = 0.1", xlabel="Coefficient index n",
              ylabel="Absolute error in normalized coefficient")
    ax[1].set_xticks([40, 80, 120, 200], labels=["40", "80", "120", "200"])
    ax[1].xaxis.set_minor_formatter(NullFormatter())
    ax[1].legend(frameon=False, fontsize=8, loc="lower left")
    for panel in ax:
        panel.grid(axis="y", color="#DEE5E8", lw=0.6, alpha=0.8)
        panel.set_axisbelow(True)
    FIGURES.mkdir(exist_ok=True)
    fig.savefig(FIGURES / "diagnostics.pdf", metadata={
        "Title": "Polylogarithmic reversion: numerical diagnostics",
        "Creator": "scripts/make_figures.py", "CreationDate": None,
        "ModDate": None})
    fig.savefig(FIGURES / "diagnostics.png", dpi=220)
    plt.close(fig)
    print("Generated three article tables and PDF/PNG diagnostics.")


if __name__ == "__main__":
    main()
