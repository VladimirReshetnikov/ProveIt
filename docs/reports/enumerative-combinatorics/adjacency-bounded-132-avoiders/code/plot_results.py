"""Recreate the report's two separate figures from its CSV tables.

Uses Matplotlib's default palette. No numerical assertions are made here.
"""
from pathlib import Path
import csv
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    out = ROOT / "figures"
    out.mkdir(exist_ok=True)
    with (ROOT / "data/growth_constants.csv").open() as f:
        growth = list(csv.DictReader(f))
    m = [int(r["m"]) for r in growth]
    fig, ax = plt.subplots(figsize=(7.1, 4.25))
    ax.plot(m, [float(r["lambda_U"]) for r in growth], "o-", label=r"$\lambda_U(m)$")
    ax.plot(m, [float(r["lambda_V"]) for r in growth], "s--", label=r"$\lambda_V(m)$")
    ax.axhline(4, linestyle=":", label="Catalan limit")
    ax.set(xlabel="Adjacency bound m", ylabel="Exponential growth rate",
           xlim=(1.5, 20.5), ylim=(0.85, 4.1))
    ax.set_xticks(range(2, 21, 2))
    ax.grid(alpha=0.25)
    ax.legend(loc="lower right")
    fig.tight_layout()
    fig.savefig(out / "component_growth.pdf")
    fig.savefig(out / "component_growth.png", dpi=160)
    plt.close(fig)

    with (ROOT / "data/large_m_scalar_bounds.csv").open() as f:
        bounds = list(csv.DictReader(f))
    mm = [int(r["m"]) for r in bounds]
    fig, ax = plt.subplots(figsize=(7.1, 4.25))
    ax.semilogx(mm, [float(r["remainder_lower_bound"]) for r in bounds], "o-",
                label="Scalar upper-growth bound: lower remainder")
    ax.semilogx(mm, [float(r["remainder_upper_bound"]) for r in bounds], "s--",
                label="Best block bound, d = 1, 2, 4, 8: upper remainder")
    ax.set(xlabel="Adjacency bound m",
           ylabel=r"$m(4-\alpha_m)-2\log m-4\log\log m$")
    ax.grid(alpha=0.25)
    ax.legend(loc="upper right", fontsize=8)
    fig.tight_layout()
    fig.savefig(out / "scalar_remainder_bounds.pdf")
    fig.savefig(out / "scalar_remainder_bounds.png", dpi=160)
    plt.close(fig)


if __name__ == "__main__":
    main()
