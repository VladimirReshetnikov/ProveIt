#!/usr/bin/env python3
"""Exact prefix checks and a reproducible supercritical profile figure.

Run from any directory: python code/verify_supercritical.py
Requires numpy and matplotlib only for arrays and the figure.
The mathematical inequality checks use integer arithmetic.
"""

from __future__ import annotations

import json
import math
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


ROOT = Path(__file__).resolve().parents[1]
FIGURES = ROOT / "figures"
DATA = ROOT / "data"
FIGURES.mkdir(exist_ok=True)
DATA.mkdir(exist_ok=True)

A_PARAM, B_PARAM, Q, LAM = 8, 1, 2, 4
VERIFY_DEPTH, FIGURE_DEPTH = 9, 8
TAU_ONE = "1" + "0" * A_PARAM + "1" * B_PARAM


def substitute(word: str) -> str:
    return "".join("1" if char == "0" else TAU_ONE for char in word)


def prefix_arrays(word: str):
    letters = np.frombuffer(word.encode("ascii"), dtype=np.uint8)
    zeros = np.concatenate(([0], np.cumsum(letters == 48, dtype=np.int64)))
    indices = np.arange(len(word) + 1, dtype=np.int64)
    weights = 3 * zeros - 2 * indices
    lengths = 2 * indices - weights
    return indices, weights, lengths


words = ["1"]
for depth in range(1, VERIFY_DEPTH + 1):
    words.append(substitute(words[-1]))
    assert words[-1].startswith(words[-2])
    assert len(words[-1]) == 2 * 4**depth - (-2)**depth

word = words[-1]
indices, weights, lengths = prefix_arrays(word)
assert len(word) == 524800
assert np.array_equal(lengths, 2 * indices - weights)

# The eigenlength theorem is X^2 <= 5 L. This is an exact check, not
# a floating-point assertion of the physical asymptotic envelope.
gap = 5 * lengths - weights * weights
assert np.all(gap >= 0)
assert np.array_equal(gap, 10 * indices - weights * weights - 5 * weights)

extremal_rows = []
prefix = ""
for k in range(1, 6):
    prefix = substitute(substitute(prefix)) + "1" + "0" * A_PARAM
    predicted_length = (2 * 16**k + 5 * 4**k - 7) // 5
    predicted_weight = 2 * (4**k - 1)
    predicted_geometric_length = 4 * (16**k - 1) // 5
    assert (2 * 16**k + 5 * 4**k - 7) % 5 == 0
    assert len(prefix) == predicted_length
    assert word.startswith(prefix)
    observed_weight = prefix.count("0") - 2 * prefix.count("1")
    observed_geometric_length = prefix.count("0") + 4 * prefix.count("1")
    assert observed_weight == predicted_weight == int(weights[len(prefix)])
    assert observed_geometric_length == predicted_geometric_length
    image = substitute(prefix)
    assert image.count("0") - 2 * image.count("1") == -2 * observed_weight
    if len(image) <= len(word):
        assert word.startswith(image)
    extremal_rows.append({
        "k": k,
        "length": len(prefix),
        "weight": observed_weight,
        "geometric_length": observed_geometric_length,
        "normalized_weight": observed_weight / math.sqrt(len(prefix)),
    })

ratios = weights[1:] / np.sqrt(indices[1:])
maximum_index = int(np.argmax(ratios)) + 1
minimum_index = int(np.argmin(ratios)) + 1
record = {
    "parameters": {"a": 8, "b": 1, "q": 2, "lambda": 4, "alpha": 0.5},
    "substitution_word_depth": VERIFY_DEPTH,
    "prefixes_checked_including_empty": len(word) + 1,
    "exact_checks": [
        "|tau^k(1)| = 2*4^k - (-2)^k for k=0,...,9",
        "L_N = 2*N - X(N) for every checked prefix",
        "X(N)^2 <= 5*L_N for every checked prefix",
        "X(N)^2 + 5*X(N) <= 10*N for every checked prefix",
        "Explicit P_k length, weight and legality for k=1,...,5",
        "X(tau(P_k)) = -2*X(P_k) for k=1,...,5",
    ],
    "all_exact_checks_passed": True,
    "positive_prefix_gap_minimum": int(np.min(gap[1:])),
    "predicted_physical_amplitude": math.sqrt(10),
    "predicted_geometric_amplitude": math.sqrt(5),
    "largest_observed_physical_ratio": {
        "N": maximum_index, "value": float(ratios[maximum_index - 1])},
    "smallest_observed_physical_ratio": {
        "N": minimum_index, "value": float(ratios[minimum_index - 1])},
    "extremal_prefixes": extremal_rows,
    "figure_profile_depth": FIGURE_DEPTH,
    "figure_profile_uniform_error_bound": 3 / 2**FIGURE_DEPTH,
    "note": "Finite negative physical ratios may exceed sqrt(10) in modulus; "
            "the symmetric physical envelope is asymptotic. The quadratic "
            "integer inequality checked here is valid at every prefix.",
}

# A depth-eight profile and its exact contact points.
_, fig_weights, fig_lengths = prefix_arrays(words[FIGURE_DEPTH])
profile_x = fig_lengths / 4**FIGURE_DEPTH
profile_y = fig_weights / (-2)**FIGURE_DEPTH
t_star, vertical_amplitude = 16 / 5, 4
breaks = t_star * 16.0 ** (-np.arange(12, -1, -1))
values = vertical_amplitude * 4.0 ** (-np.arange(12, -1, -1))
envelope_x = np.concatenate(([0.0], breaks, [4.0]))
envelope_y = np.concatenate(([0.0], values, [4.0]))

plt.rcParams.update({
    "font.family": "serif", "font.serif": ["DejaVu Serif"],
    "mathtext.fontset": "stix", "font.size": 10,
    "axes.spines.top": False, "axes.spines.right": False,
    "path.simplify": True, "path.simplify_threshold": 0.06,
    "savefig.bbox": "tight",
})
fig, axes = plt.subplots(1, 2, figsize=(12.4, 4.45))
blue, orange, muted = "#163d66", "#b86429", "#6f7b85"

ax = axes[0]
ax.plot(profile_x, profile_y, color=blue, linewidth=0.95,
        label=r"Depth-eight profile $f_{1,8}$")
ax.plot(envelope_x, -envelope_y, color=orange, linestyle="--", linewidth=1,
        label="Invariant polygon bounds")
upper_x = np.linspace(0, 4, 2400)
upper_y = np.interp(4 * upper_x, envelope_x, envelope_y, right=4) / 2
ax.plot(upper_x, upper_y, color=orange, linestyle="--", linewidth=1)
ax.scatter([0.8, 3.2], [2, -4], s=25, color=orange, zorder=5)
ax.annotate(r"$(4/5,2)$", (0.8, 2), xytext=(8, 8), textcoords="offset points")
ax.annotate(r"$(16/5,-4)$", (3.2, -4), xytext=(-75, -20),
            textcoords="offset points")
ax.set(xlim=(0, 4), ylim=(-4.65, 2.65), xlabel="Geometric coordinate $t$",
       ylabel=r"Profile value $f_1(t)$", title="(a) Self-affine profile and exact contacts")
ax.grid(alpha=0.15)
ax.legend(loc="lower left", frameon=False, fontsize=8.5)

fundamental_mask = profile_x >= 1
fundamental_t = profile_x[fundamental_mask]
fundamental_phase = np.log(fundamental_t) / math.log(4)
fundamental_curve = (math.sqrt(2) * profile_y[fundamental_mask]
                     / np.sqrt(fundamental_t))
phase = np.concatenate((fundamental_phase, 1 + fundamental_phase[1:]))
phase_curve = np.concatenate((fundamental_curve, -fundamental_curve[1:]))
sample_n = np.unique(np.rint(4 ** (8 + np.linspace(0, 2, 6001)) / 2).astype(int))
cycle_start, cycle_stop = 32768, 524288
cycle_ratios = ratios[cycle_start - 1:cycle_stop]
cycle_extrema = [cycle_start + int(np.argmin(cycle_ratios)),
                cycle_start + int(np.argmax(cycle_ratios))]
sample_n = np.unique(np.concatenate((sample_n, cycle_extrema)))
sample_phase = np.log(2 * sample_n) / math.log(4) - 8
sample_ratios = weights[sample_n] / np.sqrt(sample_n)
ax = axes[1]
ax.scatter(sample_phase, sample_ratios, s=2.5, color="#79a9b8", alpha=0.65,
           linewidths=0, label=r"Finite prefixes: $32768\leq N\leq524288$")
ax.plot(phase, phase_curve, color=blue, linewidth=1,
        label="Limiting phase curve (profile approximation)")
for sign in [-1, 1]:
    ax.axhline(sign * math.sqrt(10), color=orange, linestyle="--", linewidth=0.9)
contact_phase = math.log(t_star) / math.log(4)
ax.scatter([contact_phase, contact_phase + 1], [-math.sqrt(10), math.sqrt(10)],
           s=21, color=orange, zorder=6)
ax.text(1.96, math.sqrt(10) + 0.10, r"$\sqrt{10}$", ha="right", color=orange)
ax.text(1.96, -math.sqrt(10) - 0.10, r"$-\sqrt{10}$", va="top", ha="right", color=orange)
ax.set(xlim=(0, 2), ylim=(-3.8, 3.8), xlabel=r"Phase $\log_4(2N)-8$",
       ylabel=r"$X(N)/\sqrt{N}$", title="(b) Physical normalization and the phase law")
ax.grid(alpha=0.15)
ax.legend(loc="upper left", frameon=True, framealpha=0.94, fontsize=7.8)
fig.tight_layout(w_pad=2.2)
fig.savefig(FIGURES / "supercritical_profile.pdf")
fig.savefig(FIGURES / "supercritical_profile.png", dpi=180)
plt.close(fig)

caption = (
    "Supercritical example tau(0)=1, tau(1)=1 0^8 1: q=2, lambda=4, alpha=1/2. "
    "Left: the depth-eight geometric profile, whose uniform distance from the "
    "limit is at most 3/256, with the invariant polygon bounds and exact limiting "
    "contacts (4/5,2) and (16/5,-4). Right: finite prefix ratios over one logarithmic "
    "phase cycle compared with the limiting phase curve obtained from that profile. "
    "The dashed levels +/-sqrt(10) are asymptotic physical amplitudes; finite "
    "negative ratios can lie slightly beyond them. Every prefix instead satisfies "
    "the exact quadratic envelope X(N)^2+5X(N)<=10N."
)
record["figure_caption"] = caption
(DATA / "supercritical_checks.json").write_text(json.dumps(record, indent=2) + "\n")
(DATA / "supercritical_figure_caption.txt").write_text(caption + "\n")
print(json.dumps({key: record[key] for key in [
    "prefixes_checked_including_empty", "all_exact_checks_passed",
    "predicted_physical_amplitude", "largest_observed_physical_ratio",
    "smallest_observed_physical_ratio"]}, indent=2))
