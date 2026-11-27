"""Render the construction shown in the paper. Requires Matplotlib and NumPy."""
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from examples import columns, T, C
from math import gcd
from pathlib import Path

fig, ax = plt.subplots(1, 2, figsize=(10, 3.28), gridspec_kw={"width_ratios": [1, 1.1]})
fig.subplots_adjust(left=.072, right=.98, bottom=.18, top=.86, wspace=.32)
ink, teal, rust = "#182f47", "#007e79", "#ad4b2e"
n = 160
p = np.array(columns(n))
t = float(T)
x = np.linspace(-1, 1, 500)
L = (n - 1) / (2*float(C))
ax[0].plot(x * L/t, t*np.sqrt(1-x*x), color=teal, lw=1.0)
ax[0].scatter(p[:, 0], p[:, 1], s=8, color=ink, linewidths=0)
ax[0].scatter([1], [0], s=20, color=rust, zorder=5)
ax[0].set(xlabel="First coordinate", ylabel="Lattice row", yticks=range(7), ylim=(-.55,6.8),
          title="An integer construction with 160 columns")
q=np.arange(1,20)
w=np.array([sum(gcd(j,int(k))==1 for j in range(1,int(k)+1))/k for k in q])
xx=np.linspace(4.5,16,3000)
f=lambda z: 4/(3*z)*sum(w*np.maximum(0,1-(q/z)**2)**1.5)
ax[1].plot(xx,[f(z) for z in xx],color=ink,lw=1.35)
ax[1].axhline(3/(2*np.pi),ls="--",lw=.95,color=teal, label="Limit at infinity")
ax[1].scatter([t],[f(t)],s=20,color=rust,zorder=5,label="Global maximum")
ax[1].set(xlabel="Scaled row cutoff  T",ylabel="F(T)",title="The arithmetic optimization")
ax[1].legend(loc="lower right", fontsize=8, frameon=False)
for a in ax:
    a.spines[['top','right']].set_visible(False)
    a.tick_params(labelsize=8)
    a.title.set_fontsize(10)
fig.savefig(Path(__file__).with_name('six_rows.pdf'),metadata={"Title":"Six lattice rows and the extremal profile"})
