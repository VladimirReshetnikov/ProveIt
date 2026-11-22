"""Regenerate variational.pdf (requires matplotlib and NumPy)."""
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

x = np.linspace(0, 1, 401)
square = x*x
fit = 1/8 + square - np.maximum(0, x-1/2)**2
fig, (curve, residual) = plt.subplots(1, 2, figsize=(7.0, 2.6), constrained_layout=True)
blue, amber = "#165879", "#99491c"
for ax in (curve, residual):
    ax.spines[["top", "right"]].set_visible(False)
    ax.set(xlim=(0, 1), xlabel="x", xticks=[0, .5, 1], xticklabels=["0", "1/2", "1"])
    ax.grid(axis="y", alpha=.22)
curve.plot(x, square, label="Target  $x^2$", color=blue, linewidth=2)
curve.plot(x, fit, label="Optimal 1-Lipschitz fit", color=amber, linewidth=2)
curve.legend(fontsize=8, frameon=False, loc="upper left")
curve.set(ylim=(-.02, 1.04), yticks=[0,.5,1], title="Function values")
residual.fill_between(x, -1/8, 1/8, color=blue, alpha=.09)
residual.axhline(0, color="0.55", lw=.7)
residual.plot(x, fit-square, color=amber, linewidth=2)
residual.scatter([.5,1],[1/8,-1/8], c=amber, s=25, zorder=4, clip_on=False)
residual.set(ylim=(-.155,.155), yticks=[-1/8,0,1/8], yticklabels=["−1/8","0","1/8"],
             title="Fit minus target")
for ax in (curve, residual):
    ax.tick_params(labelsize=8)
    ax.title.set_fontsize(10)
fig.savefig(Path(__file__).with_name("variational.pdf"))
