#!/usr/bin/env python3
"""Exact model checks and a scientific illustration of averaged control.

The picture is synthetic; it is not prime data or evidence for a new RH case.
The exact calculations use Fraction. Only drawing uses floating point.
"""
from fractions import Fraction
from pathlib import Path
from math import gcd, lcm
import json


def main():
    base = Path(__file__).resolve().parents[1]
    rows = []
    # k divisible by four makes every displayed power a rational integer.
    for k in range(4, 33, 4):
        X = 2**k
        height = Fraction(1, 2**(k//4))
        width = Fraction(2**(3*k//4), 4)
        area = height * width
        squared_area = Fraction(2, 3) * height**2 * width
        assert width <= Fraction(X, 4)
        assert area == Fraction(2**(k//2), 4)
        assert height / width == Fraction(4, X)
        rows.append(dict(k=k, X=X, height=str(height), half_width=str(width),
                         area=str(area), squared_area=str(squared_area),
                         normalized_area="1/4"))
    # The row maximum is the correct valuation operation for alternative
    # full length bounds. Products overstate it when branches share primes.
    array = [[4, 8], [8, 4]]
    C = gcd(*(lcm(*row) for row in array))
    P = gcd(*(row[0]*row[1] for row in array))
    assert (C, P) == (8, 32)
    result = {
        "all_checks_passed": True,
        "scope": "Exact synthetic models and integer identities only.",
        "tent_models": rows,
        "branch_length_example": {"array": array, "gcd_lcm": C,
                                  "gcd_products": P},
    }
    (base/"checks"/"mean_models.json").write_text(json.dumps(result, indent=2)+"\n")

    import numpy as np
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 10,
                         "axes.spines.top": False, "axes.spines.right": False})
    fig, axes = plt.subplots(1, 2, figsize=(10.2, 3.45),
                             gridspec_kw={"width_ratios": [1.65, 1]})
    axis = axes[0]
    t = np.linspace(2, 12.99, 9000)
    x = 2**t
    R = np.zeros_like(x)
    for k in range(2, 13):
        X = 2.**k
        height = X**(-.25)
        width = X**.75/4
        R += height*np.maximum(1-np.abs(x-1.5*X)/width, 0)
    axis.plot(t, np.sqrt(x)*R, color="#087E8B", lw=1.55)
    axis.axhline(1, color="#B06A20", lw=1, ls="--", label="Constant pointwise envelope")
    axis.set(xlabel=r"$\log_2 x$", ylabel=r"$\sqrt{x}\,R(x)$",
             title="Thin positive spikes exceed a pointwise bound", xlim=(2, 13))
    axis.legend(frameon=False, fontsize=8, loc="upper left")
    axis.grid(axis="y", alpha=.16)
    ks = np.arange(2, 13)
    axes[1].bar(ks, np.full(len(ks), .25), color="#17324D", width=.65)
    axes[1].set(xlabel=r"Dyadic block $X=2^k$", ylabel=r"$X^{-1/2}\int_X^{2X}R(x)\,dx$",
                title="Their averaged cost stays constant", ylim=(0, .32))
    axes[1].set_xticks([2, 4, 6, 8, 10, 12])
    axes[1].grid(axis="y", alpha=.16)
    fig.tight_layout()
    fig.savefig(base/"figures"/"averaged_spikes.pdf", bbox_inches="tight")
    fig.savefig(base/"figures"/"averaged_spikes.png", dpi=180, bbox_inches="tight")
    plt.close(fig)
    print("PASS: exact tent areas, slopes, and branch-length identities; figure created.")


if __name__ == "__main__":
    main()
