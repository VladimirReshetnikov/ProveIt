"""Regenerate the root plot included in the paper; requires matplotlib and numpy."""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

n = 16
s = 1 + 1 / n**2
epsilon = 2 / n
h = np.arccosh(2) / n
theta = np.arange(n) * (2*np.pi/n) + np.pi/n
roots = np.cos(theta + 1j*h)/s
v = np.linspace(0, 2*np.pi, 500)
fig, ax = plt.subplots(figsize=(6.6, 1.72), layout="constrained")
ax.plot(np.cos(v), np.sin(v), color="#365674", linewidth=1.35, label="Boundary of the prescribed ellipse")
ax.plot(np.cosh(h)*np.cos(v)/s, np.sinh(h)*np.sin(v)/(epsilon*s),
        color="#999999", linewidth=.8, linestyle="--", label="Ellipse carrying the roots")
ax.scatter(roots.real, roots.imag/epsilon, color="#8e3d2b", s=18, zorder=3, label="Zeros")
ax.axhline(0, color=".80", linewidth=.6, zorder=0)
ax.set(xlim=(-1.05,1.05), ylim=(-1.15,1.15), yticks=[-1,0,1], xlabel="Real part", ylabel="Imaginary part / ε")
for side in ("top","right"):
    ax.spines[side].set_visible(False)
ax.tick_params(labelsize=8)
fig.savefig(Path(__file__).with_name("ellipse_zeros.pdf"), bbox_inches="tight")
