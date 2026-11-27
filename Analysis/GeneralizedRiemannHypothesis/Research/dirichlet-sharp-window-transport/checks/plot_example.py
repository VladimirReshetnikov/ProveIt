"""Rebuild the PDF figure from example.json with matplotlib 3.10 and NumPy 2.3."""
import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

here = Path(__file__).resolve().parent
with (here / "example.json").open() as stream:
    rows = json.load(stream)["gaps"]
starts = np.array([float(row["g_eq_0"]) for row in rows])
stops = np.array([float(row["g_eq_minus_1"]) for row in rows])
lo, hi = float(rows[0]["left_zeta_zero"]), float(rows[-1]["right_zeta_zero"])
t = np.unique(np.concatenate([np.linspace(lo, hi, 4000), starts, stops]))
measured = np.clip(t[:, None] - starts, 0, stops - starts).sum(axis=1)
scale = np.log(t / (2 * np.pi)) / 2
profile = (np.arctan((1 - np.pi / 4) / scale) + np.arctan((np.pi / 4) / scale)) / np.pi
model = np.r_[0, np.cumsum((profile[1:] + profile[:-1]) * np.diff(t) / 2)]

plt.rcParams.update({"font.size": 9, "pdf.fonttype": 42, "axes.spines.top": False,
                     "axes.spines.right": False, "axes.labelcolor": "#203446"})
fig, (top, bottom) = plt.subplots(2, 1, sharex=True, figsize=(6.35, 2.44),
                                  gridspec_kw={"height_ratios": [0.27, 1], "hspace": 0.03})
top.broken_barh(list(zip(starts, stops - starts)), (0, 0.30), facecolors="#347896")
top.set_ylim(-0.05, 1)
top.text(0, 0.68, "Ordinates with  −1 < g(t) < 0", transform=top.transAxes,
         ha="left", va="center", color="#245169")
top.axis("off")
bottom.plot(t, measured, color="#14597c", lw=1.5, label="Measured displacement")
bottom.plot(t, model, color="#a14822", lw=1.3, linestyle=(0, (4, 2)),
            label="Integrated profile")
bottom.set(xlim=(lo, hi), xlabel="Positive ordinate  t", ylabel="Cumulative length")
bottom.set_yticks([0, 5, 10, 15, 20])
bottom.tick_params(length=3, color="#667582", labelsize=8)
bottom.grid(axis="y", alpha=0.22, linewidth=0.6)
bottom.legend(loc="upper left", frameon=False, fontsize=8)
fig.subplots_adjust(left=0.10, right=0.985, bottom=0.19, top=0.98)
fig.savefig(here.parent / "zeta_transport.pdf", metadata={"Title": "Scalar zero transport in 23 zeta gaps"})
