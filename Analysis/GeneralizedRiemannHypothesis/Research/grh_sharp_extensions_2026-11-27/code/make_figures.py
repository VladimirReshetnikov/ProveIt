#!/usr/bin/env python3
"""Reproduce the report's exact-formula illustrations, not statistical fits."""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

DEST = Path(__file__).resolve().parents[1] / "figures"
DEST.mkdir(exist_ok=True)
plt.rcParams.update({"font.size": 10, "axes.spines.top": False,
                     "axes.spines.right": False, "pdf.fonttype": 42,
                     "figure.dpi": 150})

n = np.arange(0, 8)
fig, ax = plt.subplots(figsize=(7.0, 3.4), constrained_layout=True)
ax.plot(n, np.minimum(n, 3) + 3*np.minimum(n, 2), "o-", color="#174c72",
        label="Sharp total length: min(n, 3) + 3 min(n, 2)")
ax.plot(n, np.minimum(n, 5), "s-", color="#b65c24",
        label="Sharp longest direction: min(n, 5)")
ax.plot(n, np.minimum(n, 3), "--", color="#657780",
        label="Trace depth alone: min(n, 3)")
ax.set(xlabel="Precision exponent n", ylabel="Module length", xticks=n,
       yticks=np.arange(0, 10), ylim=(-0.2, 9.5))
ax.grid(alpha=0.18)
ax.legend(loc="lower right", fontsize=9)
fig.savefig(DEST/"congruence_lengths.pdf")
fig.savefig(DEST/"congruence_lengths.png")
plt.close(fig)

k = 8
g = np.linspace(0, 4*np.pi*k, 4001)
u = np.abs(np.exp(1j*g[:,None]*np.arange(k+1)[None,:]/k).mean(axis=1))
fig, ax = plt.subplots(figsize=(7.0, 3.4), constrained_layout=True)
for m,c in [(1,"#7b8790"),(4,"#277f8e"),(12,"#174c72")]:
    ax.plot(g/(2*np.pi*k), u**m, color=c, label=f"Depth m = {m}")
for j in [0,1,2]:
    ax.axvline(j, color="#b65c24", linewidth=0.7, alpha=0.5)
ax.set(xlabel=r"Frequency / $(2\pi k)$, with $k=8$",
       ylabel=r"Multiplier magnitude $|U_k(i\gamma)|^m$",
       xlim=(0,2), ylim=(-0.02,1.05), xticks=np.arange(0,2.1,.25))
ax.grid(alpha=0.18)
ax.legend(loc="upper center", fontsize=9)
fig.savefig(DEST/"filter_aliases.pdf")
fig.savefig(DEST/"filter_aliases.png")
plt.close(fig)
print("Reproduced two exact-formula figures.")
