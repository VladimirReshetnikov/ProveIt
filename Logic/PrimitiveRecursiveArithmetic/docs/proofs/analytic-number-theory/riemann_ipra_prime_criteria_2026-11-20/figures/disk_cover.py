"""Plot the upper boundaries of the Taylor disks near the critical line."""
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

fig, ax = plt.subplots(figsize=(6.0, 2.6), constrained_layout=True)
colors = ("#757681", "#778723", "#a85123", "#08666d")
for c, color in zip((5, 20, 36, 68), colors):
    left = .5 + 1/(2*c)
    x = np.linspace(left, 1.18, 700)
    y = np.sqrt((x-left)*(2*c-left-x))
    ax.plot(x, y, color=color, label=rf"$c={c}$", linewidth=1.65)
ax.axvline(.5, color="#344657", linestyle="--", linewidth=1)
ax.scatter([.75], [5], s=24, zorder=6, color="#111827")
ax.annotate(r"$3/4+5i$", (.75, 5), xytext=(6, -11), textcoords="offset points", size=9)
ax.set(xlim=(.46, 1.18), ylim=(0, 7.55), xlabel=r"$\mathrm{Re}\ s$", ylabel=r"$\mathrm{Im}\ s$")
ax.set_xticks((.5,.6,.7,.8,.9,1.0,1.1))
ax.grid(alpha=.15, linewidth=.6)
ax.spines[["top","right"]].set_visible(False)
ax.legend(ncol=4, loc="upper center", bbox_to_anchor=(.5,1.22), frameon=False, fontsize=8)
fig.savefig(Path(__file__).with_name("disk_cover.pdf"))
