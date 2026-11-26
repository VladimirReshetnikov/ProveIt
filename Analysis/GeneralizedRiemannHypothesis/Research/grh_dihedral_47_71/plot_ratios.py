"""Render the illustrative figure. Requires NumPy and Matplotlib."""
from pathlib import Path
import math
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from numpy.polynomial.legendre import leggauss


def theta_coeffs(form, terms):
    a, b, c = form
    counts = np.zeros(terms + 1)
    # 4aQ=(2ax+by)^2+47y^2 gives finite bounds on x and y.
    for y in range(-math.isqrt(4*a*terms//47), math.isqrt(4*a*terms//47)+1):
        bound = math.isqrt(4*a*terms) + abs(y)
        for x in range(-bound//(2*a)-1, bound//(2*a)+2):
            n = a*x*x + b*x*y + c*y*y
            if 0 < n <= terms:
                counts[n] += 1
    return counts[1:]


def draw():
    forms = [(1, 1, 12), (2, 1, 6), (3, 1, 4)]
    b0, b1, b2 = (theta_coeffs(form, 72) for form in forms)
    phi = (1 + math.sqrt(5)) / 2
    a1 = (b0 + (phi-1)*b1 - phi*b2) / 2
    a2 = (b0 - phi*b1 + (phi-1)*b2) / 2
    # Integrate in u on [0,7]. The graph is numerical illustration only.
    nodes, weights = leggauss(160)
    u, w = 3.5*(nodes+1), 3.5*weights
    basis = np.exp(-2*math.pi/math.sqrt(47)*np.outer(np.exp(u), np.arange(1,73)))
    k1 = np.exp(u/2)*(basis@a1)
    k2 = np.exp(u/2)*(basis@a2)
    t = np.linspace(0, 7, 240)
    fig, ax = plt.subplots(figsize=(6.5, 2.8), layout="constrained")
    for m, color in enumerate(["#174C73", "#AA5329", "#427761"]):
        quadrature = np.cosh(np.outer(t,u))*(w*u**(2*m))
        ax.plot(t, (quadrature@k1)/(quadrature@k2), color=color, lw=2, label=f"m = {m}")
    ax.set(xlim=(0,7), ylim=(.995,1.47), xlabel="Distance from the center,  t = |s − 1/2|",
           ylabel="Ratio of even derivatives")
    ax.set_yticks([1, 1.1, 1.2, 1.3, 1.4])
    ax.grid(axis="y", lw=.5, alpha=.35)
    ax.legend(frameon=False, ncol=3, loc="upper right")
    ax.spines[["top","right"]].set_visible(False)
    fig.savefig(Path(__file__).with_name("ratios.pdf"))


if __name__ == "__main__":
    draw()
