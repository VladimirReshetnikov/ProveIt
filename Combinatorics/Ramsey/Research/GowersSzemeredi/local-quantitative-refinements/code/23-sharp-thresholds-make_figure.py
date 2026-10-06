"""Plot theorem bounds, not empirical estimates of the unknown threshold."""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

root = Path(__file__).resolve().parents[1]
out = root / "figures"
out.mkdir(exist_ok=True)
plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 10,
                     "axes.spines.top": False, "axes.spines.right": False,
                     "pdf.fonttype": 42})
fig, (ax, bx) = plt.subplots(1, 2, figsize=(11.0, 4.2), constrained_layout=True)
teal, blue, gray = "#167A7A", "#153D55", "#6B7280"
a = np.linspace(0, 1/3, 601)
near = np.maximum(0, (1-4*a)/2)
flex = np.maximum(0, (1-3*a)/2)
ax.fill_between(a, 0, near, color=teal, alpha=0.15)
ax.fill_between(a, near, flex, color=blue, alpha=0.10)
ax.plot(a[a <= 1/4], near[a <= 1/4], color=teal, lw=2,
        label="Consecutive lengths: 4a + 2b = 1")
ax.plot(a, flex, color=blue, lw=2, label="Flexible lengths: 3a + 2b = 1")
aa = np.linspace(0, .25, 80)
ax.plot(aa, 2*aa, ls="--", color=gray, label="b = 2a")
ax.scatter([1/8, 1/7], [1/4, 2/7], color=[teal, blue], s=32, zorder=5)
ax.annotate("a = 1/8", (1/8, 1/4), xytext=(.165, .19),
            arrowprops={"arrowstyle":"-", "color":teal}, color=teal)
ax.annotate("a = 1/7", (1/7, 2/7), xytext=(.19, .33),
            arrowprops={"arrowstyle":"-", "color":blue}, color=blue)
ax.set(xlim=(0, .345), ylim=(0, .515), xlabel="Length exponent a",
       ylabel="Accuracy exponent b", title="Sharp scaling boundaries (q = 2)")
ax.legend(loc="upper right", fontsize=7.6, frameon=False)
ax.grid(alpha=.15)

L = np.arange(10, 1001, dtype=np.int64)
C = L*(L-1)
lower = C*(4*L-5)**2/(16.0*L**4)
upper = C*(16*L**2-1)/(16.0*L**4)
bx.fill_between(L, lower, upper, color=teal, alpha=.18, label="Rigorous threshold band")
bx.plot(L, lower, color=teal, lw=1.8, label="Lower bound")
bx.plot(L, upper, color=blue, lw=1.8, label="Upper bound")
bx.axhline(1, color=gray, ls="--", lw=1, label="Sharp leading constant")
bx.set(xscale="log", xlim=(10, 1000), ylim=(.67, 1.015), xlabel="Minimum cell length L",
       ylabel=r"Threshold divided by $16L^4$",
       title=r"Consecutive lengths; $\varepsilon_1=\varepsilon_2=1/4$")
bx.set_xticks([10, 30, 100, 300, 1000], ["10", "30", "100", "300", "1000"])
bx.legend(loc="lower right", fontsize=8, frameon=False)
bx.grid(alpha=.15)
fig.savefig(out / "phase_thresholds.pdf", metadata={"Title":"Rigorous phase partition bounds"})
fig.savefig(out / "phase_thresholds.png", dpi=170)
print("Created figures/phase_thresholds.pdf and figures/phase_thresholds.png")
