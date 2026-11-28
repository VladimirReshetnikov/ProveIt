#!/usr/bin/env python3
"""Plot a finite window of Ehrhart roots. Requires numpy, matplotlib and mpmath.

Run from any directory. Creates roots.pdf and root_positions.csv next to this
script. The winding-number grid supplies numerical seeds. It is not relied
upon as a proof of completeness or a certified root-isolation method.
"""
from fractions import Fraction
from math import comb, factorial
from pathlib import Path
import csv

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np

OUT = Path(__file__).resolve().parent
D = 1023


def recurrences(d, s):
    """Return H_d and C_d-C_(d-2) simultaneously; accepts array arguments."""
    a = 2*s + 1
    older_h, old_h = 1, a
    older_c, old_c = 1, a
    for n in range(2, d + 1):
        h = ((2*n - 1)*a*old_h + (n-1)**2*older_h) / n**2
        c = (a*old_c + (n-1)*older_c) / n
        diff = c - older_c
        older_h, old_h = old_h, h
        older_c, old_c = old_c, c
    return h, diff


def general_binom(s, n):
    product = Fraction(1)
    for k in range(n):
        product *= s - k
    return product / factorial(n)


def check_recurrences():
    # Equality at d+1 rational arguments checks each polynomial identically.
    for d in range(2, 16):
        for j in range(d + 1):
            s = Fraction(3*j - 2*d, 7)
            h, diff = recurrences(d, s)
            h_points = sum(comb(d, k)**2 * general_binom(s + d - k, d)
                           for k in range(d + 1))
            def cross(n):
                return sum(2**k * comb(n, k) * general_binom(s, k)
                           for k in range(n + 1))
            if (h, diff) != (h_points, cross(d) - cross(d-2)):
                raise AssertionError((d, s))


def grid_seeds(d):
    # An odd horizontal cell count keeps Re(s)=-1/2 inside cells.
    x = np.linspace(-1.02, 0.02, 56)
    y = np.linspace(0.005, 4, 137)
    grid = x[None, :] + 1j*y[:, None]
    h, diff = recurrences(d, grid)
    result = {}
    for m in (0, (d + 1) // 2):
        f = h - (m/2)*diff
        corners = [f[:-1, :-1], f[:-1, 1:], f[1:, 1:], f[1:, :-1]]
        turns = sum(np.angle(b / a) for a, b in zip(corners, corners[1:] + corners[:1]))
        result[m] = [complex((x[j]+x[j+1])/2, (y[i]+y[i+1])/2)
                     for i, j in np.argwhere(turns > np.pi)]
    return result


def refine(d, m, seed):
    def f(s):
        h, diff = recurrences(d, s)
        return h - m * diff / 2
    # The table retains 24 digits; refinement checks the residual at 48 digits.
    z = mp.findroot(f, (mp.mpc(seed), mp.mpc(seed) + mp.mpc("0.0003", "0.0004")),
                    tol=mp.mpf("1e-35"), maxsteps=18)
    if abs(f(z)) > mp.mpf("1e-35") or abs(z - seed) > mp.mpf("0.045"):
        raise ArithmeticError((seed, z))
    return z


def plot(roots):
    fig, axes = plt.subplots(1, 2, figsize=(7.0, 3.55), sharex=True, sharey=True)
    fig.subplots_adjust(left=.11, right=.982, top=.88, bottom=.19, wspace=.15)
    for ax, (m, values) in zip(axes, roots.items()):
        ax.axvline(-.5, color="#a9afb2", linewidth=1, dashes=(3, 3), zorder=1)
        ax.grid(axis="y", linewidth=.55, color="#e4e6e9")
        for z in values:
            off = abs(float(z.real) + .5) > .001
            ax.scatter(float(z.real), float(z.imag), s=24, zorder=3,
                       marker="D" if off else "o", color="#ae482f" if off else "#265c70",
                       linewidths=.4, edgecolors="white")
        ax.set_title("Complete graph" if m == 0 else "Perfect matching deleted",
                     loc="left", fontsize=10.5, pad=8, weight="bold")
        ax.set_xlim(-1.04, .04)
        ax.set_ylim(0, 4.02)
        ax.set_xticks([-1, -.75, -.5, -.25, 0],
                      [r"$-1$",r"$-0.75$",r"$-0.5$",r"$-0.25$",r"$0$"])
        ax.set_yticks(range(5))
        ax.tick_params(labelsize=8.2, width=.6, length=3)
        for spine in ("top", "right"):
            ax.spines[spine].set_visible(False)
        for spine in ("bottom", "left"):
            ax.spines[spine].set_color("#8b9498")
            ax.spines[spine].set_linewidth(.65)
    axes[0].set_ylabel(r"Imaginary part of $s$", fontsize=9)
    fig.text(.54, .045, r"Real part of $s$", ha="center", fontsize=9)
    fig.savefig(OUT / "roots.pdf", metadata={"Title":"Ehrhart roots in dimension 1023",
                                             "CreationDate":None, "ModDate":None})
    plt.close(fig)


def main():
    check_recurrences()
    mp.mp.dps = 48
    roots = {}
    for m, seeds in grid_seeds(D).items():
        values = sorted((refine(D, m, z) for z in seeds),
                        key=lambda w: (round(float(w.imag), 12), float(w.real)))
        for j, z in enumerate(values):
            if any(abs(z - w) < mp.mpf("1e-16") for w in values[:j]):
                raise ValueError("Duplicate refined root")
        roots[m] = values
    with (OUT / "root_positions.csv").open("w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["dimension", "matching_size", "real_part", "imaginary_part"])
        for m, values in roots.items():
            for z in values:
                writer.writerow([D, m, mp.nstr(z.real, 24), mp.nstr(z.imag, 24)])
    plot(roots)
    print("Dimension 1023. Points plotted by matching size:",
          {m: len(values) for m, values in roots.items()})


if __name__ == "__main__":
    main()
