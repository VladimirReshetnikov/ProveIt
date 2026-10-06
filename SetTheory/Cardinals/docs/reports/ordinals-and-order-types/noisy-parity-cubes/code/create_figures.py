#!/usr/bin/env python3
"""Regenerate the article's three vector figures and its checked examples.

Requires numpy and matplotlib for plotting. All finite example assertions and
the infinite-product bracket use exact fractions. Plotted curves use ordinary
floating-point arithmetic and illustrate proved formulas; they are not proofs.
Run from any directory: python3 /path/to/code/create_figures.py
"""

from decimal import Decimal, localcontext, ROUND_FLOOR, ROUND_CEILING
from fractions import Fraction as Q
from pathlib import Path
import json

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import MultipleLocator

ROOT = Path(__file__).resolve().parents[1]
FIGURES = ROOT / "figures"
DATA = ROOT / "data"
INK = "#183044"
TEAL = "#126d80"
RUST = "#bd5939"
GRAY = "#728190"
PALE = "#dce5ea"

plt.rcParams.update({
    "font.family": "DejaVu Sans",
    "font.size": 9,
    "axes.titlesize": 11,
    "axes.labelsize": 10,
    "axes.edgecolor": "#8b9aa5",
    "axes.labelcolor": INK,
    "text.color": INK,
    "xtick.color": INK,
    "ytick.color": INK,
    "axes.spines.top": False,
    "axes.spines.right": False,
    "axes.grid": True,
    "grid.color": PALE,
    "grid.linewidth": 0.6,
    "grid.alpha": 0.85,
    "legend.frameon": False,
    "pdf.fonttype": 42,
    "savefig.facecolor": "white",
})


def parity_scores(probabilities, eta):
    """Exact prefix-parity scores including the empty parity."""
    a = 1 - 2 * eta
    p = Q(0)
    scores = [Q(0)]
    for k, weight in enumerate(probabilities, 1):
        p += weight
        scores.append((1 + a**k * (2*p-1)) / 2)
    return scores


def walsh_coefficients(values):
    npoints = len(values)
    transformed = list(values)
    stride = 1
    while stride < npoints:
        for start in range(0, npoints, 2*stride):
            for j in range(start, start+stride):
                left, right = transformed[j], transformed[j+stride]
                transformed[j] = left + right
                transformed[j+stride] = left - right
        stride *= 2
    return [Q(value, npoints) for value in transformed]


def fraction_decimal(value, rounding, digits=32):
    with localcontext() as context:
        context.prec = digits
        context.rounding = rounding
        return str(Decimal(value.numerator) / Decimal(value.denominator))


def check_examples():
    """Check the table, the nonlinear optimizer, and a product interval."""
    eta = Q(1, 10)
    dyadic = [Q(1, 2**i) for i in range(1, 13)]
    scores = parity_scores(dyadic, eta)
    assert scores[:5] == [Q(0), Q(1, 2), Q(33, 50),
                          Q(173, 250), Q(849, 1250)]
    assert scores.index(max(scores)) == 3
    assert (scores[2]+scores[3])/2 == Q(169, 250)

    uniform = parity_scores([Q(1, 4)]*4, Q(1, 4))
    finite_geom = parity_scores([Q(8, 15), Q(4, 15), Q(2, 15), Q(1, 15)],
                                Q(1, 4))
    low_noise = parity_scores(dyadic, Q(1, 100))
    assert uniform[3] == uniform[4] == max(uniform) == Q(17, 32)
    assert finite_geom.index(max(finite_geom)) == 2
    assert max(finite_geom) == Q(23, 40)
    assert low_noise.index(max(low_noise)) == 6
    assert max(low_noise) == Q(929079903231, 10**12)

    # The nonlinear five-bit optimizer in Section 6.
    values = []
    for x in range(32):
        z = [1 - 2*((x >> i) & 1) for i in range(5)]
        numerator = z[0]*(z[1]*z[2] + z[2]*z[3]
                          + z[3]*z[4] - z[1]*z[4])
        assert numerator in (-2, 2)
        values.append(numerator//2)
    coefficients = walsh_coefficients(values)
    support = {s: c for s, c in enumerate(coefficients) if c}
    expected_support = {0b00111: Q(1, 2), 0b01101: Q(1, 2),
                        0b11001: Q(1, 2), 0b10011: Q(-1, 2)}
    assert support == expected_support
    probabilities = [Q(3, 5)] + [Q(1, 10)]*4
    nonlinear_eta = Q(3, 20)
    score = Q(0)
    for s, coefficient in support.items():
        p_s = sum((probabilities[i] for i in range(5) if (s >> i) & 1), Q(0))
        w_s = (1 + (1-2*nonlinear_eta)**s.bit_count()*(2*p_s-1))/2
        score += coefficient**2 * w_s
    assert score == Q(6029, 10000)
    assert score == max(parity_scores(probabilities, nonlinear_eta))

    # A rational enclosure, not merely a floating-point product.
    # For x_i in [0,1], product(1-x_i) >= 1-sum(x_i).
    cutoff = 40
    partial = Q(1)
    for i in range(1, cutoff+1):
        partial *= 1-Q(1, 4**i)
    tail_sum = Q(1, 3*4**cutoff)
    lower = partial*(1-tail_sum)
    upper = partial
    score_lower, score_upper = (1+lower)/2, (1+upper)/2

    examples = {
        "all_checks_passed": True,
        "arithmetic_for_assertions": "Exact fractions",
        "dyadic_eta_1_10": {
            "scores_k_0_to_4": [str(w) for w in scores[:5]],
            "first_optimal_degree": 3,
            "optimal_score": "173/250",
            "budget_5_2_score": "169/250",
        },
        "finite_uniform_n4_eta_1_4": {
            "optimal_degrees": [3, 4], "optimal_score": "17/32",
        },
        "finite_geometric_n4_eta_1_4": {
            "optimal_degrees": [2], "optimal_score": "23/40",
        },
        "dyadic_eta_1_100": {
            "optimal_degrees": [6], "optimal_score": str(max(low_noise)),
        },
        "nonlinear_five_bit_optimizer": {
            "truth_table_minus_plus_one": values,
            "nonzero_walsh_coefficients_mask_as_integer":
                {str(s): str(c) for s, c in support.items()},
            "score": str(score),
            "total_influence": str(sum((s.bit_count()*c*c
                                        for s, c in support.items()), Q(0))),
        },
        "summable_noise_product": {
            "model": "p_i=2^-i, eta_i=p_i^2/2, product_i(1-4^-i)",
            "cutoff": cutoff,
            "tail_sum_exact": str(tail_sum),
            "product_lower_outward_decimal":
                fraction_decimal(lower, ROUND_FLOOR),
            "product_upper_outward_decimal":
                fraction_decimal(upper, ROUND_CEILING),
            "optimal_score_lower_outward_decimal":
                fraction_decimal(score_lower, ROUND_FLOOR),
            "optimal_score_upper_outward_decimal":
                fraction_decimal(score_upper, ROUND_CEILING),
            "bound_proof": "P_N*(1-sum_{i>N}4^-i) <= P_infinity <= P_N",
        },
    }
    DATA.mkdir(parents=True, exist_ok=True)
    (DATA / "examples.json").write_text(json.dumps(examples, indent=2)+"\n")
    return examples


def inspection_frontier():
    k = np.arange(0, 11)
    w = (1 + 0.8**k*(1-2.0**(1-k)))/2
    w[0] = 0.0
    fig, ax = plt.subplots(figsize=(6.8, 3.35), layout="constrained")
    ax.plot([0, 1, 2, 3, 10], [w[0], w[1], w[2], w[3], w[3]],
            color=TEAL, lw=2.3, label="Optimal score with an expected budget")
    ax.scatter(k, w, color=RUST, s=29, zorder=4,
               label="A fixed parity of size k")
    ax.plot(2.5, 0.676, "D", color=INK, markersize=4.7, zorder=5)
    ax.annotate("2.5 queries: 0.676", xy=(2.5, 0.676), xytext=(3.15, 0.39),
                arrowprops={"arrowstyle": "-", "color": GRAY, "lw": 0.8},
                fontsize=9, color=INK)
    ax.annotate("Maximum: 0.692", xy=(3, w[3]), xytext=(4.6, 0.77),
                arrowprops={"arrowstyle": "-", "color": GRAY, "lw": 0.8},
                fontsize=9, color=TEAL)
    ax.set(xlim=(-0.12, 10.15), ylim=(-0.015, 0.85),
           xlabel="Expected coordinate inspections, c",
           ylabel="Probability that the label changes",
           title="Exact inspection frontier  |  $p_i=2^{-i}$, $\\eta=0.1$")
    ax.xaxis.set_major_locator(MultipleLocator(1))
    ax.legend(loc="lower right", fontsize=8.5)
    fig.savefig(FIGURES / "inspection_frontier.pdf")
    plt.close(fig)


def uniform_transition():
    c = np.linspace(0.025, 4, 1400)
    s = np.where(c <= 1, 1, (1+1/c)/2)
    advantage = np.where(c <= 1, np.exp(-2*c), np.exp(-c-1)/c)
    fig, axes = plt.subplots(1, 2, figsize=(7, 3.15), layout="constrained")
    colors = [RUST, "#b6a268", "#7b95a5"]
    for n, color in zip([32, 128, 512], colors):
        eta = c/n
        k = np.minimum(n, np.floor((n+1/eta)/2)).astype(int)
        v = np.exp(k*np.log1p(-2*eta))*(2*k/n-1)
        axes[0].plot(c, k/n, lw=1.0, color=color, alpha=0.9, label=f"n = {n}")
        axes[1].plot(c, v, lw=1.0, color=color, alpha=0.9, label=f"n = {n}")
    axes[0].plot(c, s, color=TEAL, lw=2, ls="--", label="Limit")
    axes[1].plot(c, advantage, color=TEAL, lw=2, ls="--", label="Limit")
    for ax in axes:
        ax.axvline(1, color=GRAY, ls=":", lw=1)
        ax.set(xlim=(0, 4), xlabel="Scaled noise, $c=n\\eta$")
        ax.xaxis.set_major_locator(MultipleLocator(1))
    axes[0].set(ylim=(0.57, 1.03), ylabel="Optimal fraction $k/n$",
                title="Optimal parity size")
    axes[1].set(ylim=(-0.02, 1.015), ylabel="Optimal advantage $2V_n-1$",
                title="Success above one half")
    axes[1].legend(fontsize=8, loc="upper right")
    fig.savefig(FIGURES / "uniform_transition.pdf")
    plt.close(fig)


def geometric_correction():
    t = np.linspace(11.05, 18.05, 2801)
    eta = 2.0**(-t)
    x = np.log2((1+2*eta)/eta)
    k = np.floor(x).astype(int)
    u = x-np.floor(x)
    # expm1 avoids subtracting two nearly equal numbers in the leading loss.
    log_a_k = k*np.log1p(-2*eta)
    loss = -np.expm1(log_a_k)/2 + np.exp(log_a_k)*2.0**(-k)
    residual = (loss-eta*t)/eta
    phi = -u+2.0**u
    fig, axes = plt.subplots(2, 1, figsize=(6.8, 4.45), sharex=True,
                             layout="constrained",
                             gridspec_kw={"height_ratios": [1, 1.3]})
    axes[0].plot(t, k, color=TEAL, lw=1.7, drawstyle="steps-post")
    axes[0].plot(t, x, color=GRAY, ls=":", lw=1, label="Continuous crossover")
    axes[0].set(ylabel="Optimal degree $k$", title="Geometric tails retain an integer-scale oscillation")
    axes[0].yaxis.set_major_locator(MultipleLocator(2))
    axes[0].legend(fontsize=8, loc="upper left")
    axes[1].plot(t, residual, color=RUST, lw=1.8,
                 label="Exact loss after removing its leading term")
    axes[1].plot(t, phi, color=TEAL, lw=1.7, ls="--",
                 label="Periodic coefficient $-u+2^u$")
    axes[1].set(xlabel="Logarithmic inverse noise, $t=\\log_2(1/\\eta)$",
                ylabel="$(L-\\eta t)/\\eta$", xlim=(t[0], t[-1]), ylim=(0.865, 1.055))
    axes[1].xaxis.set_major_locator(MultipleLocator(1))
    axes[1].legend(fontsize=8, loc="upper right")
    fig.savefig(FIGURES / "geometric_correction.pdf")
    plt.close(fig)


def main():
    FIGURES.mkdir(parents=True, exist_ok=True)
    examples = check_examples()
    inspection_frontier()
    uniform_transition()
    geometric_correction()
    print("Exact examples and nonlinear optimizer: PASS")
    print("Summable-noise optimal score enclosed in:")
    print(examples["summable_noise_product"]["optimal_score_lower_outward_decimal"])
    print(examples["summable_noise_product"]["optimal_score_upper_outward_decimal"])
    print("Wrote three vector PDF figures and data/examples.json.")


if __name__ == "__main__":
    main()
