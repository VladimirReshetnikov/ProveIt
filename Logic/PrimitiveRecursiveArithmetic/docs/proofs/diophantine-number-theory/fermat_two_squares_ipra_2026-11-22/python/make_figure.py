"""Render the exact p=13 grid used in the report; requires Matplotlib."""
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch

root = Path(__file__).resolve().parents[1]
destination = root / "figures"
destination.mkdir(exist_ok=True)
plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 11})
fig, ax = plt.subplots(figsize=(6.8, 4.6))
fig.patch.set_facecolor("white")
ax.set_facecolor("white")

for u in range(4):
    for v in range(4):
        included = u + 4 * v <= 13
        special = (u, v) in {(0, 0), (3, 2)}
        color = "#b44736" if special else ("#15374a" if included else "#cdd3d8")
        ax.scatter([u], [v], s=440 if special else 350, color="white",
                   edgecolors=color, linewidths=2 if special else 1.2, zorder=4)
        ax.text(u, v, str((u + 5 * v) % 13), ha="center", va="center",
                color=color, fontweight="bold" if special else "normal", zorder=5)

arrow = FancyArrowPatch((0.13, 0.09), (2.84, 1.89), arrowstyle="-|>",
                        mutation_scale=13, linewidth=1.9,
                        color="#b44736", zorder=3)
ax.add_patch(arrow)
ax.plot([0, 3, 3], [0, 0, 2], color="#4d8798", linestyle="--",
        linewidth=1.4, zorder=2)
ax.text(1.5, -0.34, r"$\Delta u=3$", ha="center", color="#286172")
ax.text(3.30, 1.0, r"$\Delta v=2$", ha="left", color="#286172")
ax.text(1.05, 1.18, r"$3^2+2^2=13$", rotation=27,
        color="#a4392c", ha="center",
        bbox={"facecolor": "white", "edgecolor": "none", "pad": 3}, zorder=6)
ax.set_xlim(-0.6, 4.05)
ax.set_ylim(-0.65, 3.55)
ax.set_xticks(range(4))
ax.set_yticks(range(4))
ax.set_xlabel(r"$u$", loc="right", labelpad=8)
ax.set_ylabel(r"$v$", loc="top", rotation=0, labelpad=10)
ax.grid(color="#e7ecef", linewidth=0.8, zorder=1)
ax.set_aspect("equal")
for spine in ("top", "right"):
    ax.spines[spine].set_visible(False)
for spine in ("bottom", "left"):
    ax.spines[spine].set_color("#adb8c1")
ax.tick_params(length=0, colors="#42535f", pad=8)
ax.set_title(r"Residue labels in the integer grid:  $p=13$, $t=5$",
             loc="left", color="#15374a", fontsize=12, pad=16)
fig.tight_layout()
fig.savefig(destination / "grid_p13.pdf", bbox_inches="tight")
fig.savefig(destination / "grid_p13.png", dpi=160, bbox_inches="tight")
plt.close(fig)
print("Rendered figures/grid_p13.pdf and figures/grid_p13.png")
