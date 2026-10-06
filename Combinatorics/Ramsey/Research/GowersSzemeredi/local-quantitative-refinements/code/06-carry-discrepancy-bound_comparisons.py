#!/usr/bin/env python3
"""Reproduce exact bound inputs and the report's comparison figure."""
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def regions(d, m):
    return sum(math.comb(m, j) for j in range(min(d, m) + 1))


def main():
    rows = []
    for k in range(1, 11):
        h = (k - 2) * 2 ** (k - 1) + 1
        affine_h = k * 2 ** (k - 1)
        C_bound = regions(k, h)
        D_bound = regions(k + 1, affine_h)
        K = (2 * (k + 1)) ** k * D_bound
        rows.append({
            "k": k, "h": h, "affine_h": affine_h,
            "C_bound": C_bound, "D_bound": D_bound,
            "K": K, "inverse_phase_constant": 8 * K ** 2,
            "old_floor_bound_bits_r1": 2 * k ** 3,
            "new_floor_bound_bits_r1": k + math.log2(C_bound),
            "old_phase_loss_bits": 2 * (k + 1) ** 3,
            "new_phase_loss_bits": math.log2(8 * K ** 2),
        })
    output = Path(__file__).with_name("bound_comparisons.json")
    output.write_text(json.dumps({"rows": rows}, indent=2) + "\n")

    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    matplotlib.rcParams.update({
        "font.family": "DejaVu Sans", "font.size": 10,
        "pdf.fonttype": 42, "ps.fonttype": 42,
        "axes.spines.top": False, "axes.spines.right": False,
    })
    fig, axes = plt.subplots(1, 2, figsize=(10.5, 3.8))
    x = [r["k"] for r in rows]
    plots = [
        ("old_floor_bound_bits_r1", "new_floor_bound_bits_r1",
         "Floor-pattern bound, r = 1", "log₂ of the count upper bound"),
        ("old_phase_loss_bits", "new_phase_loss_bits",
         "Localized phase-removal loss", "log₂ of the reciprocal constant"),
    ]
    for ax, (old, new, title, ylabel) in zip(axes, plots):
        ax.plot(x, [r[old] for r in rows], color="#697482", marker="s",
                markersize=3.5, label="Displayed source bound")
        ax.plot(x, [r[new] for r in rows], color="#047c83", marker="o",
                markersize=3.5, label="Bound proved here")
        ax.set(xlabel="Dimension k", ylabel=ylabel, title=title)
        ax.set_xticks([1, 2, 4, 6, 8, 10])
        ax.grid(axis="y", alpha=0.2)
        ax.legend(frameon=False, fontsize=8)
    fig.tight_layout(pad=1.4)
    figures = ROOT / "figures"
    figures.mkdir(exist_ok=True)
    fig.savefig(figures / "bound_comparisons.pdf", bbox_inches="tight")
    fig.savefig(figures / "bound_comparisons.png", dpi=180, bbox_inches="tight")
    for row in rows:
        if row["k"] in (1, 2, 3, 4, 6, 8, 10):
            print(f'k={row["k"]}: floor bits '
                  f'{row["old_floor_bound_bits_r1"]} -> '
                  f'{row["new_floor_bound_bits_r1"]:.3f}; phase bits '
                  f'{row["old_phase_loss_bits"]} -> '
                  f'{row["new_phase_loss_bits"]:.3f}')


if __name__ == "__main__":
    main()
