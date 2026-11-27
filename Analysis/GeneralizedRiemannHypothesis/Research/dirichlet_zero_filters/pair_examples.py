"""Reproduce the moment checks and illustrations in the paper with Python 3.

Zeta ordinates are rounded LMFDB data. These numerical calculations illustrate
the analytic theorems. Run with --plot to regenerate pair_width.pdf (matplotlib).
"""
from math import acos, cos, exp, floor, pi, sin, sqrt
import argparse
import cmath

ORDINATES = {1: 14.134725141734694, 2: 21.022039638771555,
             10: 49.773832477672302, 20: 77.144840068874805}


def bisect_decreasing(f, lo, hi):
    """Find a bracketed zero, assuming positive then negative signs."""
    for _ in range(75):
        mid = (lo + hi) / 2
        if f(mid) > 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def pair(r):
    """Return angular half-width and a centered probability law as (node,weight)."""
    if r <= 1:
        raise ValueError("require r > 1")
    if r == int(r) and int(r) % 2:
        return pi / 2, [(-pi / 2, .5), (pi / 2, .5)]
    if r < 3:
        A = 2 * pi / (1 + r)
        x = 0
    else:
        odd = 2 * floor((r - 1) / 2) + 1
        u = (r - odd) * pi / 2
        def derivative(y):
            v = (u + y) / r
            return cos(y) * sin(v) - sin(y) * cos(v) / r
        y = bisect_decreasing(derivative, 0, pi / 2)
        S = sin(y) / sin((u + y) / r)
        z = bisect_decreasing(lambda v: sin(u + v) - S * sin(v / r),
                              0, pi - u)
        A = pi / 2 + z / r
        x = pi / 2 - (u + y) / r
    w = cos(x) / (cos(x) - cos(A))
    law = [(-A, w / 2), (A, w / 2)]
    if x == 0:
        law.append((0., 1 - w))
    else:
        law.extend([(-x, (1 - w) / 2), (x, (1 - w) / 2)])
    return A, sorted(law)


def verify():
    for r in [1.01, 1.5, 2., 3., 3.0001, 3.2, 4., 4.99, 5., 5.01,
              6., 8.1, 17.7, 40.23]:
        A, law = pair(r)
        assert abs(sum(w for t, w in law) - 1) < 2e-15
        assert all(w > 0 for t, w in law)
        assert all(abs(sum(w * cmath.exp(1j * f * t) for t, w in law)) < 1e-12
                   for f in (1, r))
        assert pi <= 2*A + 1e-14 and 2*A <= pi + pi/r + 1e-13
    X = sqrt((2 + sqrt(10)) / 12)
    V = -X + sqrt(1 - 2*X**2)
    assert abs(pair(4.)[0] - acos(V)) < 5e-15
    print("Moment checks passed for 14 ratios, including the algebraic r=4 example.")
    print("zeta pair | r | width | dilation factor | separate-filter width")
    for n in (2, 10, 20):
        a, b = ORDINATES[1], ORDINATES[n]
        A, law = pair(b/a)
        width = 2*A/a
        print(f"1,{n:2d}  {b/a:.9f}  {width:.9f}  {exp(width):.9f}  {pi/a+pi/b:.9f}")
        # Start the filter at u=0 and remove the critical-line weight.
        atoms = [((t+A)/a, w*exp(-(t+A)/(2*a))) for t, w in law]
        C = sum(w for u, w in atoms)
        for f in [a, b]:
            assert abs(sum(w*cmath.exp((.5+1j*f)*u)/C for u, w in atoms)) < 2e-12
        print("  tilted (u, mass):",
              " ".join(f"({u:.9f},{w/C:.9f})" for u,w in atoms))
    print("Cusp for n=3: measured coefficient and limit")
    expected = 4/3*(3*pi/(2*(1-1/9)))**(1/3)
    for h in [1e-3, 1e-5, 1e-7]:
        print(f"  h={h:.0e}  {(2*pair(3+h)[0]-pi)/h**(1/3):.8f}  limit {expected:.8f}")


def plot():
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    # Add points on both sides of each odd ratio to resolve the cusp.
    ratios = {1.03 + i*.006 for i in range(1500)}
    for n in (3., 5., 7., 9.):
        ratios.add(n)
        for j in range(1, 42):
            ratios.update([n - 10**(-j/8), n + 10**(-j/8)])
    ratios = sorted(r for r in ratios if 1.03 <= r <= 10)
    fig, ax = plt.subplots(figsize=(6.6, 2.65), layout="constrained")
    ax.plot(ratios, [1+1/r for r in ratios], color="#9a7045", ls="--",
            lw=1.45, label="Two separate filters, convolved")
    ax.plot(ratios, [2*pair(r)[0]/pi for r in ratios], color="#174d69",
            lw=2, label="Shortest joint filter")
    ax.scatter([3,5,7,9], [1]*4, color="#174d69", s=15, zorder=3)
    ax.set(xlim=(1,10), ylim=(.965,2.02), xlabel="Frequency ratio  r",
           ylabel="Width in units of π/a", xticks=range(1,11))
    ax.grid(axis="y", alpha=.22)
    ax.spines[["top", "right"]].set_visible(False)
    ax.legend(frameon=False, fontsize=9)
    fig.savefig("pair_width.pdf")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plot", action="store_true")
    args = parser.parse_args()
    verify()
    if args.plot:
        plot()
