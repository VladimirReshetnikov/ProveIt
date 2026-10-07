#!/usr/bin/env python3
"""Regenerate the manuscript's vector scientific figure."""
from pathlib import Path
from math import comb
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt


ROOT = Path(__file__).resolve().parents[1]
plt.rcParams.update({
    "font.family": "DejaVu Sans", "font.size": 10,
    "axes.labelsize": 10, "axes.titlesize": 11,
    "axes.titleweight": "bold", "axes.spines.top": False,
    "axes.spines.right": False, "axes.edgecolor": "#8796A0",
    "axes.labelcolor": "#16334A", "text.color": "#16334A",
    "xtick.color": "#52616B", "ytick.color": "#52616B",
    "pdf.fonttype": 42,
})
fig, (ax, bx) = plt.subplots(1, 2, figsize=(10.0, 4.2))
ds = np.arange(3, 11)
bs = [2**(-.5)] + [
    2 / comb(2 * 2**(int(d)-2), 2**(int(d)-2))**(1/2**(int(d)-2))
    for d in ds[1:]
]
ax.axhline(2**(-.5), color="#88708F", linestyle="--", lw=1.4,
           label=r"Earlier upper bound $1/\sqrt{2}$")
ax.plot(ds, bs, color="#146A74", marker="o", lw=2,
        label="Proved upper bounds")
ax.axhline(.5, color="#729D9D", linestyle=":", lw=1.4,
           label=r"Upper-bound limit $1/2$")
ax.axhline(1/3, color="#BB8648", lw=1.5,
           label=r"Uniform lower bound $1/3$")
ax.scatter([4], [(8/111)**.25], marker="D", s=40, color="#BB8648", zorder=5)
ax.annotate(r"Cosine lower bound, $d=4$", (4, (8/111)**.25),
            xytext=(4.75, .456), fontsize=8.5,
            arrowprops={"arrowstyle": "-", "color": "#BB8648", "lw": .9})
ax.set(xlim=(2.7, 10.25), ylim=(.3, .75),
       xlabel=r"Dimension $d$", ylabel=r"Bounds on $c_d^{\mathrm{odd}}$")
ax.set_xticks(ds)
ax.set_title("Higher-norm comparison")
ax.grid(axis="y", color="#E6EAED", lw=.65)
ax.legend(loc="lower center", bbox_to_anchor=(.5, -0.54), fontsize=8.1,
          frameon=False, ncol=1)

tau = np.linspace(0, 1, 501)
m = 4
profile = sum(comb(2*m, 2*k)*comb(2*k, k) * tau**(m-k)
              * ((1-tau)/2)**k for k in range(m+1))
curve = profile**(-1/m)
bx.plot(tau, curve, color="#146A74", lw=2.3)
bx.scatter([0, 1], [curve[0], curve[-1]], color="#146A74", s=25, zorder=4)
bx.set(xlim=(-.025, 1.025), ylim=(.49, 1.045),
       xlabel=r"Self-inverse Fourier mass fraction $\tau$",
       ylabel=r"Moment-method bound $K_4(\tau)^{-1/4}$")
bx.set_title("Dependence on the torsion profile")
bx.grid(axis="y", color="#E6EAED", lw=.65)
bx.text(.04, .93, "Sharp for the moment estimate;\nGowers-norm sharpness is open here.",
        transform=bx.transAxes, fontsize=8.5, va="top",
        bbox={"facecolor": "#F2F6F7", "edgecolor": "none", "pad": 5})
fig.subplots_adjust(left=.08, right=.985, top=.89, bottom=.35, wspace=.30)
(ROOT / "figures").mkdir(exist_ok=True)
fig.savefig(ROOT / "figures/norm_bounds.pdf",
            metadata={"Title": "Bounds for higher Gowers norms",
                      "Author": "Prepared for Vladimir Reshetnikov",
                      "CreationDate": None, "ModDate": None})
fig.savefig(ROOT / "figures/norm_bounds.png", dpi=180)
print("Generated figures/norm_bounds.pdf and figures/norm_bounds.png")
