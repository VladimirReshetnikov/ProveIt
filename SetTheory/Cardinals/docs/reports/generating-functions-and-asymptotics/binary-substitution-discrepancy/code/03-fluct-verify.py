#!/usr/bin/env python3
"""Reproduce exact checks and figures for critical morphic discrepancy.

Substitution: sigma_a(0) = 1, sigma_a(1) = 1 0^a 1^(a-2), a >= 3.
For a word w, the histogram counts its PROPER prefixes, including the empty
prefix and excluding w itself, by X(prefix) = number of 0s - number of 1s.

All verification assertions use Python integers or fractions.Fraction.  No
random samples, floating-point comparisons, or Gaussian assumptions enter
those assertions.  Floating-point operations are confined to the explicitly
labelled numerical diagnostics and scientific figures.

Run from any directory:
    python code/verify.py
or:
    python code/verify.py --output-dir /path/to/results

The exact checks require only the Python standard library.  Figures also
require NumPy, Matplotlib, and SciPy; use --skip-figures to omit plotting.
Existing files in the selected data/ and figures/ subdirectories with the
same names will be replaced.  No article or README file is modified.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from itertools import combinations
import json
import math
from pathlib import Path
import platform
from typing import Iterable


Poly = dict[int, int]  # Laurent polynomial: exponent -> coefficient.
ONE: Poly = {0: 1}


def poly_add(*polynomials: Poly) -> Poly:
    result: Counter[int] = Counter()
    for polynomial in polynomials:
        for exponent, coefficient in polynomial.items():
            result[exponent] += coefficient
    return {e: c for e, c in result.items() if c}


def poly_scale(polynomial: Poly, multiplier: int) -> Poly:
    return {e: c * multiplier for e, c in polynomial.items() if c * multiplier}


def poly_multiply(left: Poly, right: Poly) -> Poly:
    result: Counter[int] = Counter()
    for e, c in left.items():
        for f, d in right.items():
            result[e + f] += c * d
    return {e: c for e, c in result.items() if c}


def poly_reverse(polynomial: Poly) -> Poly:
    return {-e: c for e, c in polynomial.items()}


def poly_moment(polynomial: Poly, order: int) -> int:
    return sum(c * e**order for e, c in polynomial.items())


def normalized_moments(polynomial: Poly) -> tuple[Fraction, Fraction]:
    mass = poly_moment(polynomial, 0)
    mean = Fraction(poly_moment(polynomial, 1), mass)
    variance = Fraction(poly_moment(polynomial, 2), mass) - mean**2
    return mean, variance


def parameters(a: int) -> tuple[Poly, Poly, Poly, tuple[Poly, Poly]]:
    if a < 3:
        raise ValueError("The family treated in this article has a >= 3.")
    s = {j: 1 for j in range(-1, a - 1)}
    t = {j: 1 for j in (0, *range(2, a))}
    delta = poly_multiply(s, poly_reverse(s))
    k0 = poly_add(s, t, {0: -1})
    k1 = poly_add(poly_reverse(k0), poly_multiply(poly_reverse(t), k0))
    return s, t, delta, (k0, k1)


def histogram_step(histograms: tuple[Poly, Poly], a: int, r: int) -> tuple[Poly, Poly]:
    """F_(r+1) = B(t^((-1)^r)) F_r, implemented as one-step composition."""
    s, t, _, _ = parameters(a)
    if r % 2:
        s, t = poly_reverse(s), poly_reverse(t)
    f0, f1 = histograms
    return f1, poly_add(poly_multiply(s, f0), poly_multiply(t, f1))


def mixture_histograms(a: int, m: int) -> tuple[Poly, Poly]:
    """1 + K_c(t) sum_(j=0)^(m-1) Delta(t)^j; m=0 is the atom at 0."""
    _, _, delta, seeds = parameters(a)
    geometric: Poly = {}
    power = dict(ONE)
    for _ in range(m):
        geometric = poly_add(geometric, power)
        power = poly_multiply(power, delta)
    return tuple(poly_add(ONE, poly_multiply(k, geometric)) for k in seeds)  # type: ignore[return-value]


def literal_substitute(word: str, a: int) -> str:
    images = {"0": "1", "1": "1" + "0" * a + "1" * (a - 2)}
    return "".join(images[c] for c in word)


def literal_histogram(word: str) -> Poly:
    histogram: Counter[int] = Counter()
    discrepancy = 0
    for symbol in word:
        histogram[discrepancy] += 1  # Count before appending: proper prefixes.
        discrepancy += 1 if symbol == "0" else -1
    return dict(histogram)


def length_even(a: int, m: int, c: int) -> int:
    if c == 0:
        numerator = 2 * a ** (2 * m) + a - 1
    else:
        numerator = 2 * a ** (2 * m + 1) - a + 1
    quotient, remainder = divmod(numerator, a + 1)
    if remainder:
        raise AssertionError("Closed length formula is not integral.")
    return quotient


def seed_moment_formula(a: int, c: int) -> tuple[Fraction, Fraction]:
    b = a - 1
    if c == 0:
        mean = Fraction(b, 2) - Fraction(1, b)
        variance = Fraction(b * b, 12) + Fraction(7, 6) - Fraction(1, b * b)
    else:
        mean = -Fraction(a - 2, b)
        variance = Fraction(a * a - a + 7, 6) - Fraction(1, b * b)
    return mean, variance


def full_moment_formula(a: int, m: int, c: int) -> tuple[Fraction, Fraction]:
    if m == 0:
        return Fraction(0), Fraction(0)
    d = a * a
    n = length_even(a, m, c)
    weight = Fraction(n - 1, n)
    mean_y, variance_y = seed_moment_formula(a, c)
    mean_j = Fraction(m * d**m, d**m - 1) - Fraction(d, d - 1)
    variance_step = Fraction(d - 1, 6)
    mean = weight * mean_y
    variance = (
        weight * (variance_y + variance_step * mean_j)
        + weight * (1 - weight) * mean_y**2
    )
    return mean, variance


class ExactChecks:
    def __init__(self) -> None:
        self.counts: Counter[str] = Counter()

    def equal(self, actual: object, expected: object, category: str, label: str) -> None:
        if actual != expected:
            raise AssertionError(f"{category}: {label}\nactual={actual}\nexpected={expected}")
        self.counts[category] += 1

    def true(self, condition: bool, category: str, label: str) -> None:
        self.equal(bool(condition), True, category, label)


def matrix_multiply(left, right):
    return tuple(
        tuple(poly_add(*(poly_multiply(left[i][k], right[k][j]) for k in range(2)))
              for j in range(2))
        for i in range(2)
    )


def verify_seed_identities(checks: ExactChecks, a_values: Iterable[int]) -> None:
    for a in a_values:
        s, t, delta, seeds = parameters(a)
        tag = f"a={a}"
        expected_delta = {j: a - abs(j) for j in range(-(a - 1), a)}
        checks.equal(delta, expected_delta, "kernel", f"triangular coefficients, {tag}")
        checks.equal(poly_moment(delta, 0), a * a, "kernel", f"mass, {tag}")
        checks.equal(normalized_moments(delta), (Fraction(0), Fraction(a * a - 1, 6)),
                     "kernel", f"mean and variance, {tag}")
        fourth_cumulant = Fraction(poly_moment(delta, 4), a * a) - 3 * Fraction(a * a - 1, 6)**2
        checks.equal(fourth_cumulant, -Fraction(a**4 - 1, 60),
                     "kernel", f"fourth cumulant, {tag}")
        b = (({}, dict(ONE)), (s, t))
        br = tuple(tuple(poly_reverse(p) for p in row) for row in b)
        pair = matrix_multiply(br, b)
        trace = poly_add(pair[0][0], pair[1][1])
        determinant = poly_add(poly_multiply(pair[0][0], pair[1][1]),
                               poly_scale(poly_multiply(pair[0][1], pair[1][0]), -1))
        checks.equal(trace, poly_add(ONE, delta), "transfer", f"trace, {tag}")
        checks.equal(determinant, delta, "transfer", f"determinant, {tag}")
        for c, seed in enumerate(seeds):
            checks.true(all(coefficient > 0 for coefficient in seed.values()),
                        "seed", f"positive coefficients, {tag}, c={c}")
            checks.equal(poly_moment(seed, 0), 2 * a**c * (a - 1),
                         "seed", f"mass, {tag}, c={c}")
            checks.equal(normalized_moments(seed), seed_moment_formula(a, c),
                         "seed", f"mean and variance, {tag}, c={c}")


def verify_recurrence(checks: ExactChecks, a_values: Iterable[int], max_m: int) -> None:
    for a in a_values:
        s, t, delta, seeds = parameters(a)
        histograms = (dict(ONE), dict(ONE))
        geometric: Poly = {}
        power = dict(ONE)
        for m in range(max_m + 1):
            expected = tuple(poly_add(ONE, poly_multiply(seed, geometric)) for seed in seeds)
            checks.equal(histograms, expected, "mixture", f"a={a}, m={m}")
            for c, histogram in enumerate(histograms):
                tag = f"a={a}, m={m}, c={c}"
                checks.equal(poly_moment(histogram, 0), length_even(a, m, c),
                             "length", tag)
                checks.equal(normalized_moments(histogram), full_moment_formula(a, m, c),
                             "full_moments", tag)
                checks.true(all(count > 0 for count in histogram.values()),
                            "histogram", f"positivity, {tag}")
                if m:
                    minimum = -m * (a - 1) - 1 if c == 1 else -m * (a - 1) + a - 2
                    maximum = m * (a - 1)
                    checks.equal((min(histogram), max(histogram)), (minimum, maximum),
                                 "extrema", tag)
                    checks.equal((histogram[minimum], histogram[maximum]), (1, 1),
                                 "endpoint_multiplicity", tag)
                    checks.equal(set(histogram), set(range(minimum, maximum + 1)),
                                 "support", f"no missing discrepancies, {tag}")
                    if a == 3 and c == 1:
                        centered = poly_add(histogram, {0: -1})
                        reflection = {-1 - exponent: count for exponent, count in centered.items()}
                        checks.equal(centered, reflection, "a3_reflection", tag)
            if m != max_m:
                histograms = histogram_step(histograms, a, 2 * m)
                histograms = histogram_step(histograms, a, 2 * m + 1)
                geometric = poly_add(geometric, power)
                power = poly_multiply(power, delta)


def verify_literal_words(checks: ExactChecks, a_values: Iterable[int], max_chars: int) -> list[dict]:
    records = []
    for a in a_values:
        # Build both letter words and compare to independently iterated transfer histograms.
        words = ("0", "1")
        histograms = (dict(ONE), dict(ONE))
        r = 0
        while max(map(len, words)) <= max_chars:
            for c, word in enumerate(words):
                tag = f"a={a}, r={r}, c={c}"
                checks.equal(literal_histogram(word), histograms[c], "literal_histogram", tag)
                expected_total = (-1)**r * (1 if c == 0 else -1)
                checks.equal(word.count("0") - word.count("1"), expected_total,
                             "literal_total_discrepancy", tag)
                records.append({"a": a, "r": r, "c": c, "length": len(word)})
            next_lengths = [word.count("0") + (2 * a - 1) * word.count("1") for word in words]
            if max(next_lengths) > max_chars:
                break
            words = tuple(literal_substitute(word, a) for word in words)
            histograms = histogram_step(histograms, a, r)
            r += 1
    return records


def general_word_parameters(word: str) -> tuple[Poly, Poly, Poly, tuple[Poly, Poly]]:
    """Obtain transfer polynomials from literal starting heights of letters."""
    zero_heights: Counter[int] = Counter()
    one_heights: Counter[int] = Counter()
    height = 0
    for symbol in word:
        (zero_heights if symbol == "0" else one_heights)[height] += 1
        height += 1 if symbol == "0" else -1
    s, t = dict(zero_heights), dict(one_heights)
    delta = poly_multiply(s, poly_reverse(s))
    k0 = poly_add(s, t, {0: -1})
    k1 = poly_add(poly_reverse(k0), poly_multiply(poly_reverse(t), k0))
    return s, t, delta, (k0, k1)


def general_literal_substitute(word: str, image_one: str) -> str:
    return "".join("1" if c == "0" else image_one for c in word)


def verify_generalized_words(checks: ExactChecks, a_values: Iterable[int]) -> list[dict]:
    """Exhaust all words beginning with 1 having a zeros and a-1 ones.

    This is independent of the canonical explicit S,T constructors.  It tests
    the sharp variance classifications and transfer identity from literal
    zero-start heights.  The endpoint-rate coefficient is checked algebraically;
    no floating-point rate comparison is used as an assertion.
    """
    records = []
    for a in a_values:
        lower, upper = Fraction(a - 1, a * a), Fraction(a * a - 1, 12)
        minimizing_words, maximizing_words = [], []
        minimum_variance = maximum_variance = None
        endpoint_products = set()
        word_count = deeper_word_count = 0
        expected_minimizers = {"10" * (a - 1) + "0", "10" + "01" * (a - 2) + "0"}
        for zero_positions in combinations(range(1, 2 * a - 1), a):
            position_set = set(zero_positions)
            word = "".join("0" if j in position_set else "1" for j in range(2 * a - 1))
            s, t, delta, seeds = general_word_parameters(word)
            _, variance = normalized_moments(s)
            tag = f"a={a}, word={word}"
            checks.true(lower <= variance <= upper, "general_variance_bounds", tag)
            consecutive_zeros = zero_positions[-1] - zero_positions[0] + 1 == a
            checks.equal(variance == upper, consecutive_zeros,
                         "general_maximum_classification", tag)
            minimum_multiset = (
                len(s) == 2 and max(s) - min(s) == 1
                and sorted(s.values()) == [1, a - 1]
            )
            checks.equal(variance == lower, minimum_multiset,
                         "general_minimum_multiset", tag)
            checks.equal(variance == lower, word in expected_minimizers,
                         "general_minimum_words", tag)
            shifted_s = {exponent + 1: count for exponent, count in s.items()}
            checks.equal(t, poly_add(shifted_s, {1: -1}), "general_telescoping", tag)
            trace = poly_add(s, poly_reverse(s), poly_multiply(t, poly_reverse(t)))
            checks.equal(trace, poly_add(ONE, delta), "general_transfer_trace", tag)
            width = max(s) - min(s)
            product = s[min(s)] * s[max(s)]
            checks.equal((delta[-width], delta[width]), (product, product),
                         "general_endpoint_coefficient", tag)
            endpoint_products.add(product)

            # Every enumerated word is checked directly at r=2, c=1.
            literal_r2 = general_literal_substitute(word, word)
            checks.equal(literal_histogram(literal_r2), poly_add(ONE, seeds[1]),
                         "general_literal_r2", tag)

            # Exhaust deeper words for a<=6; thereafter use a deterministic spread.
            if a <= 6 or word_count % 97 == 0 or variance in (lower, upper):
                literal_r3 = general_literal_substitute(literal_r2, word)
                literal_r4 = general_literal_substitute(literal_r3, word)
                mixed_r4 = poly_add(ONE, poly_multiply(seeds[1], poly_add(ONE, delta)))
                checks.equal(literal_histogram(literal_r4), mixed_r4,
                             "general_literal_r4", tag)
                kmin, kmax = min(seeds[1]), max(seeds[1])
                checks.equal((min(mixed_r4), max(mixed_r4)), (kmin - width, kmax + width),
                             "general_endpoint_positions", tag)
                checks.equal((mixed_r4[kmin - width], mixed_r4[kmax + width]),
                             (seeds[1][kmin] * product, seeds[1][kmax] * product),
                             "general_endpoint_multiplicity", tag)
                deeper_word_count += 1

            if variance == lower:
                minimizing_words.append(word)
            if variance == upper:
                maximizing_words.append(word)
            minimum_variance = variance if minimum_variance is None else min(minimum_variance, variance)
            maximum_variance = variance if maximum_variance is None else max(maximum_variance, variance)
            word_count += 1

        checks.equal(minimum_variance, lower, "general_attained_bounds", f"minimum a={a}")
        checks.equal(maximum_variance, upper, "general_attained_bounds", f"maximum a={a}")
        checks.equal(set(minimizing_words), expected_minimizers,
                     "general_complete_minimizers", f"a={a}")
        expected_maximizers = {"1" * b + "0" * a + "1" * (a - 1 - b) for b in range(1, a)}
        checks.equal(set(maximizing_words), expected_maximizers,
                     "general_complete_maximizers", f"a={a}")
        records.append({
            "a": a, "words_enumerated": word_count, "words_checked_at_r4": deeper_word_count,
            "minimum_variance_exact": fraction_string(lower),
            "maximum_variance_exact": fraction_string(upper),
            "minimizing_words": sorted(minimizing_words),
            "maximizing_words": sorted(maximizing_words),
            "endpoint_coefficient_products_exact": sorted(endpoint_products),
            "endpoint_rate_note": "Per substitution depth r=2m, endpoint rate is log(a)-log(c_min*c_max)/2; the coefficient product was checked exactly.",
        })
    return records


def fraction_string(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def normal_cdf(x: float) -> float:
    return 0.5 * math.erfc(-x / math.sqrt(2))


def normal_density(x: float) -> float:
    return math.exp(-0.5 * x * x) / math.sqrt(2 * math.pi)


def numerical_diagnostics(a: int, m: int, c: int, histogram: Poly) -> dict:
    """Floating-point diagnostics of an exactly computed distribution."""
    n = sum(histogram.values())
    exact_mean, exact_variance = normalized_moments(histogram)
    mean, variance = float(exact_mean), float(exact_variance)
    sd = math.sqrt(variance)
    cdf_before = 0.0
    cdf_error = 0.0
    local_error = 0.0
    for k in range(min(histogram) - 1, max(histogram) + 2):
        probability = histogram.get(k, 0) / n
        z = (k - mean) / sd
        gaussian_cdf = normal_cdf(z)
        cdf_after = cdf_before + probability
        cdf_error = max(cdf_error, abs(cdf_before - gaussian_cdf), abs(cdf_after - gaussian_cdf))
        local_error = max(local_error, abs(sd * probability - normal_density(z)))
        cdf_before = cdf_after
    _, tau = seed_moment_formula(a, c)
    beta = tau - Fraction(a * a, 6)
    variance_remainder = exact_variance - Fraction(m * (a * a - 1), 6) - beta
    return {
        "arithmetic_note": "Histogram, length, and exact moments are exact; all fields marked floating use binary64.",
        "a": a, "m": m, "r": 2 * m, "c": c,
        "length_decimal_exact": str(n),
        "support_min_exact": min(histogram), "support_max_exact": max(histogram),
        "mean_rational_exact": fraction_string(exact_mean),
        "variance_rational_exact": fraction_string(exact_variance),
        "mean_floating": mean, "variance_floating": variance, "sd_floating": sd,
        "cdf_normal_error_floating": cdf_error,
        "local_mass_normal_error_floating": local_error,
        "cdf_accumulation_defect_floating": abs(cdf_before - 1.0),
        "endpoint_probability_floating": 1 / n,
        "variance_constant_exact": fraction_string(beta),
        "scaled_variance_remainder_floating": float(variance_remainder * a ** (2 * m) / m),
    }


def write_json(path: Path, data: object) -> None:
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def pressure(theta: float, a: int) -> float:
    """chi_a(theta): limiting pressure per substitution depth r=2m."""
    theta = abs(theta)
    if theta < 1e-4:
        return ((a * a - 1) * theta**2 / 24
                - (a**4 - 1) * theta**4 / 2880
                + (a**6 - 1) * theta**6 / 181440)

    def log_sinh(x: float) -> float:
        return x + math.log1p(-math.exp(-2 * x)) - math.log(2)

    return log_sinh(a * theta / 2) - math.log(a) - log_sinh(theta / 2)


def pressure_derivative(theta: float, a: int) -> float:
    if abs(theta) < 1e-4:
        return ((a * a - 1) * theta / 12
                - (a**4 - 1) * theta**3 / 720
                + (a**6 - 1) * theta**5 / 30240)
    return (a / math.tanh(a * theta / 2) - 1 / math.tanh(theta / 2)) / 2


def rate_function(x: float, a: int) -> float:
    from scipy.optimize import brentq
    x = abs(x)
    if x == 0:
        return 0.0
    if x > (a - 1) / 2:
        return math.inf
    if x == (a - 1) / 2:
        return math.log(a)
    upper = 1.0
    while pressure_derivative(upper, a) < x:
        upper *= 2
    theta = brentq(lambda y: pressure_derivative(y, a) - x, 0, upper,
                   xtol=5e-14, rtol=5e-14)
    return theta * x - pressure(theta, a)


def stable_moments_floating(a: int, m: int, c: int) -> tuple[float, float]:
    """Evaluate the proved exact moment formula without constructing huge integers."""
    d = a * a
    qinv = math.exp(-2 * m * math.log(a))
    seed_mass = 2 * a**c * (a - 1)
    inverse_n = qinv * (d - 1) / (qinv * (d - 1) + seed_mass * (1 - qinv))
    weight = 1 - inverse_n
    mean_y_exact, variance_y_exact = seed_moment_formula(a, c)
    mean_y, variance_y = float(mean_y_exact), float(variance_y_exact)
    mean_j = m / (1 - qinv) - d / (d - 1)
    variance = weight * (variance_y + (d - 1) * mean_j / 6) + weight * inverse_n * mean_y**2
    return weight * mean_y, variance


def make_figures(directory: Path, histograms: dict[int, Poly], diagnostics: dict[int, dict]) -> dict:
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    import numpy as np
    import scipy

    plt.rcParams.update({
        "font.family": "DejaVu Serif", "font.size": 8.2,
        "axes.labelsize": 8.8, "axes.titlesize": 9.2,
        "xtick.labelsize": 7.6, "ytick.labelsize": 7.6,
        "legend.fontsize": 7.4, "axes.spines.top": False,
        "axes.spines.right": False, "axes.linewidth": 0.65,
        "grid.alpha": 0.18, "grid.linewidth": 0.5,
        "savefig.bbox": "tight", "pdf.fonttype": 42,
        "ps.fonttype": 42, "figure.dpi": 140,
    })
    navy, orange, gray = "#24486B", "#BB4A28", "#777777"

    def save(figure, name: str) -> None:
        figure.savefig(directory / f"{name}.pdf")
        figure.savefig(directory / f"{name}.png", dpi=220)
        plt.close(figure)

    fig, axes = plt.subplots(1, 3, figsize=(7.25, 2.8), sharex=True, sharey=True,
                             layout="constrained")
    z_grid = np.linspace(-4.6, 4.6, 601)
    normal = np.exp(-0.5 * z_grid**2) / np.sqrt(2 * np.pi)
    for panel, (ax, m) in enumerate(zip(axes, (8, 32, 128))):
        histogram, diagnostic = histograms[m], diagnostics[m]
        mean, sd = diagnostic["mean_floating"], diagnostic["sd_floating"]
        n = sum(histogram.values())
        keys = np.array(sorted(histogram), dtype=float)
        z = (keys - mean) / sd
        density = np.array([histogram[int(k)] / n * sd for k in keys])
        ax.bar(z, density, width=1 / sd, color=navy, alpha=0.62,
               linewidth=0.25, edgecolor="white", label="Exact histogram")
        ax.plot(z_grid, normal, color=orange, lw=1.25, label="Normal density")
        ax.set(xlim=(-4.55, 4.55), ylim=(0, 0.435), xticks=(-4, -2, 0, 2, 4),
               xlabel=r"$(k-\mathbb{E}X)/\sqrt{\operatorname{Var}X}$",
               title=f"({chr(97 + panel)})  $m={m}$")
        ax.grid(axis="y")
    axes[0].set_ylabel(r"$\sqrt{\operatorname{Var}X}\;\mathbb{P}(X=k)$")
    axes[1].legend(loc="upper center", bbox_to_anchor=(0.5, -0.25), ncol=2,
                   frameon=False, handlelength=2)
    save(fig, "gaussian_histograms")

    a = 3
    m_grid = np.unique(np.rint(np.geomspace(1, 1024, 160)).astype(int))
    log_lengths = np.array([
        (2 * int(m) + 1) * math.log(a) + math.log(2 / (a + 1))
        + math.log1p(-(a - 1) * math.exp(-(2 * int(m) + 1) * math.log(a)) / 2)
        for m in m_grid
    ])
    std = np.array([math.sqrt(stable_moments_floating(a, int(m), 1)[1]) for m in m_grid])
    extreme = (a - 1) * m_grid + 1
    std_asymptote = np.sqrt((a * a - 1) * log_lengths / (12 * math.log(a)))
    extreme_asymptote = (a - 1) * log_lengths / (2 * math.log(a))
    fig, ax = plt.subplots(figsize=(6.25, 3.65), layout="constrained")
    ax.loglog(log_lengths, extreme, color=orange, lw=1.7, label=r"Exact $\max |X|=2m+1$")
    ax.loglog(log_lengths, extreme_asymptote, color=orange, lw=1.0, ls="--",
              label=r"$(\log L)/\log 3$")
    ax.loglog(log_lengths, std, color=navy, lw=1.7, label=r"Exact $\sqrt{\operatorname{Var}X}$")
    ax.loglog(log_lengths, std_asymptote, color=navy, lw=1.0, ls="--",
              label=r"$\sqrt{2\log L/(3\log 3)}$")
    ax.set(xlabel=r"$\log L_{2m,1}$  (logarithmic axis)",
           ylabel="Discrepancy magnitude  (logarithmic axis)")
    ax.grid(which="both")
    ax.legend(loc="upper left", frameon=True, framealpha=0.95, ncol=1)
    ax.text(0.98, 0.04, r"$a=3,\quad 1\leq m\leq 1024$", transform=ax.transAxes,
            ha="right", va="bottom", fontsize=8.2)
    save(fig, "extreme_and_typical_scales")

    theta_grid = np.linspace(-3, 3, 501)
    pressure_values = np.array([pressure(float(theta), a) for theta in theta_grid])
    x_grid = np.linspace(-(a - 1) / 2, (a - 1) / 2, 601)
    rate_values = np.array([rate_function(float(x), a) for x in x_grid])
    fig, axes = plt.subplots(1, 2, figsize=(7.25, 3.2), layout="constrained")
    axes[0].plot(theta_grid, pressure_values, color=navy, lw=1.6, label=r"$\chi_3(s)$")
    axes[0].plot(theta_grid, (a * a - 1) * theta_grid**2 / 24, color=gray, lw=1.0,
                  ls="--", label="Quadratic at zero")
    axes[0].set(xlabel=r"$s$", ylabel="Pressure per substitution depth",
                title="(a)  Pressure", xlim=(-3, 3), ylim=(0, 3.1))
    axes[0].legend(frameon=False, loc="upper center")
    axes[1].plot(x_grid, rate_values, color=navy, lw=1.5, label=r"$I_3(x)$")
    h = histograms[128]
    log_n = math.log(sum(h.values()))
    keys = np.array([k for k in sorted(h) if -256 <= k <= 256])
    finite_rate = np.array([(log_n - math.log(h[int(k)])) / 256 for k in keys])
    axes[1].plot(keys / 256, finite_rate, color=orange, lw=0.95, ls="--",
                  label=r"$-\log\mathbb{P}(X=k)/256$")
    axes[1].plot(x_grid, 3 * x_grid**2 / 4, color=gray, lw=0.9, ls=":",
                  label="Quadratic at zero")
    axes[1].set(xlabel=r"$x$  (finite curve: $x=k/256$)", ylabel="Rate per substitution depth",
                title="(b)  Rate function", xlim=(-1, 1), ylim=(0, 1.175))
    axes[1].legend(frameon=False, loc="upper center", fontsize=7.0)
    for ax in axes:
        ax.grid()
    save(fig, "pressure_and_rate")
    return {"numpy": np.__version__, "matplotlib": matplotlib.__version__, "scipy": scipy.__version__}


def write_report(path: Path, checks: ExactChecks, literal_records: list[dict],
                 generalized_records: list[dict], diagnostics: dict[int, dict], versions: dict) -> None:
    lines = [
        "COMPUTATION REPORT: CRITICAL MORPHIC DISCREPANCY",
        "",
        "Conventions",
        "-----------",
        "sigma_a(0)=1; sigma_a(1)=1 0^a 1^(a-2), a >= 3.",
        "X=#0-#1. Histograms count 0 <= n < |sigma_a^r(c)|: the empty",
        "prefix is included and the complete word is excluded.",
        "All algebraic checks below use exact integers and rational numbers.",
        "Finite checks corroborate the article's proofs; they are not proofs",
        "of statements quantified over all a or all iteration depths.",
        "",
        "Exact verification",
        "------------------",
        "Kernel, transfer, and seed identities: every integer 3 <= a <= 20.",
        "Recurrence versus geometric-mixture histogram: 3 <= a <= 9, 0 <= m <= 32, c=0,1.",
        "Lengths, full mean/variance, support, extrema, and endpoint multiplicities",
        "are checked on the same complete family of even histograms.",
        "Literal substitution histograms: 3 <= a <= 9, both initial letters,",
        "all depths until the larger word would exceed 200,000 symbols.",
        f"Literal words inspected: {len(literal_records)}; total symbols inspected: "
        f"{sum(row['length'] for row in literal_records):,}.",
        "Generalized words: every word beginning with 1 and containing a zeros and",
        "a-1 ones, for 2 <= a <= 8. This includes the a=2 limiting case.",
        f"Generalized words enumerated: {sum(row['words_enumerated'] for row in generalized_records):,}.",
        "For each, literal zero-start heights verify the sharp variance bounds,",
        "all equality classifications, telescoping and transfer identities,",
        "extreme kernel coefficients, and the literal histogram at r=2.",
        f"A deterministic subset of {sum(row['words_checked_at_r4'] for row in generalized_records):,} words",
        "is checked by literal substitution through r=4, including every word",
        "with a<=6 and all variance extremizers. Endpoint multiplicities are also checked.",
        "",
    ]
    for category, count in sorted(checks.counts.items()):
        lines.append(f"  {category}: {count} passed assertions")
    lines.extend([f"  TOTAL: {sum(checks.counts.values())} passed assertions", "",
                  "Deeper exact histograms with floating-point diagnostics",
                  "-------------------------------------------------------",
                  "The plotted histograms use a=3, c=1, and exact integer multiplicities.",
                  "Their means and variances are exact rational numbers in JSON.",
                  "The values below and the rendered figures use binary64 arithmetic.",
                  "CDF error is the maximum discrepancy from the normal CDF on both",
                  "sides of every jump. Local mass error is max_k |sd*p(k)-phi(z_k)|.",
                  "These diagnostic errors have no interval-arithmetic certification.", ""])
    for m, diagnostic in sorted(diagnostics.items()):
        lines.extend([
            f"m={m}; |W_(2m,1)|={diagnostic['length_decimal_exact']}",
            f"  support: [{diagnostic['support_min_exact']}, {diagnostic['support_max_exact']}]",
            f"  mean={diagnostic['mean_floating']:.12g}; variance={diagnostic['variance_floating']:.12g}",
            f"  CDF normal error={diagnostic['cdf_normal_error_floating']:.8g}",
            f"  local mass normal error={diagnostic['local_mass_normal_error_floating']:.8g}",
            f"  endpoint probability={diagnostic['endpoint_probability_floating']:.8g}", "",
        ])
    lines.extend([
        "Figure conventions",
        "------------------",
        "gaussian_histograms: z=(k-E[X])/sd, bar width 1/sd and height sd*p(k).",
        "The displayed density is normalized with the exact finite mean and variance.",
        "extreme_and_typical_scales: both axes logarithmic; the horizontal quantity",
        "is already log L. Solid curves use the exact closed formulas; dashed curves",
        "use the leading asymptotic expressions. Floating evaluation is stable at",
        "large m and does not enumerate long words.",
        "pressure_and_rate: pressure and Legendre transform are numerical evaluations",
        "of the formulas in the article, normalized per substitution depth r=2m:",
        "chi_a(s)=log(sinh(a*s/2)/(a*sinh(s/2))). The rate domain is",
        "|x|<=(a-1)/2, with endpoint rate log(a). The finite rate curve uses",
        "exact m=128 counts, coordinates x=k/256, and rate -log(p(k))/256.",
        "All PNG figures are 220 dpi; PDF figures retain vector text and curves.", "",
        "Reproduction",
        "------------",
        "python code/verify.py",
        "python code/verify.py --skip-figures  # standard-library run without figures",
        "", "Software versions", "-----------------",
    ])
    lines.extend(f"{key}: {value}" for key, value in sorted(versions.items()))
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--output-dir", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--skip-figures", action="store_true")
    args = parser.parse_args()
    output = args.output_dir.resolve()
    data_dir, figure_dir = output / "data", output / "figures"
    data_dir.mkdir(parents=True, exist_ok=True)
    figure_dir.mkdir(parents=True, exist_ok=True)

    checks = ExactChecks()
    verify_seed_identities(checks, range(3, 21))
    verify_recurrence(checks, range(3, 10), max_m=32)
    literal_records = verify_literal_words(checks, range(3, 10), max_chars=200_000)
    write_json(data_dir / "literal_checks.json", literal_records)
    generalized_records = verify_generalized_words(checks, range(2, 9))
    write_json(data_dir / "generalized_word_audit.json", generalized_records)

    histograms: dict[int, Poly] = {}
    diagnostics: dict[int, dict] = {}
    for m in (8, 32, 128):
        histogram = mixture_histograms(3, m)[1]
        checks.equal(sum(histogram.values()), length_even(3, m, 1), "deep_length", f"m={m}")
        checks.equal(normalized_moments(histogram), full_moment_formula(3, m, 1),
                     "deep_moments", f"m={m}")
        checks.equal((min(histogram), max(histogram)), (-2 * m - 1, 2 * m),
                     "deep_extrema", f"m={m}")
        histograms[m] = histogram
        diagnostics[m] = numerical_diagnostics(3, m, 1, histogram)
        write_json(data_dir / f"histogram_a3_m{m:03d}_c1.json", {
            "a": 3, "m": m, "c": 1,
            "convention": "proper prefixes, X=#0-#1; exact integer coefficients stored as decimal strings",
            "length_decimal_exact": str(sum(histogram.values())),
            "coefficients": {str(k): str(histogram[k]) for k in sorted(histogram)},
        })
    write_json(data_dir / "diagnostics.json", list(diagnostics.values()))

    versions = {"python": platform.python_version()}
    if not args.skip_figures:
        versions.update(make_figures(figure_dir, histograms, diagnostics))
    summary = {
        "status": "all exact assertions passed",
        "exact_assertion_count": sum(checks.counts.values()),
        "assertions_by_category": dict(sorted(checks.counts.items())),
        "seed_identity_parameters": {"a_min": 3, "a_max": 20},
        "recurrence_parameters": {"a_min": 3, "a_max": 9, "m_min": 0, "m_max": 32, "letters": [0, 1]},
        "literal_word_count": len(literal_records),
        "literal_symbols_inspected": sum(row["length"] for row in literal_records),
        "generalized_word_count": sum(row["words_enumerated"] for row in generalized_records),
        "generalized_r4_word_count": sum(row["words_checked_at_r4"] for row in generalized_records),
        "versions": versions,
        "proof_status": "Finite exact checks corroborate, but do not replace, the mathematical proofs.",
    }
    write_json(data_dir / "verification_summary.json", summary)
    write_report(data_dir / "computation_report.txt", checks, literal_records,
                 generalized_records, diagnostics, versions)
    print(f"PASS: {sum(checks.counts.values())} exact assertions; {len(literal_records)} literal words.")
    for m, diagnostic in diagnostics.items():
        print(f"m={m:3d}: Var={diagnostic['variance_floating']:.10f}, "
              f"CDF error={diagnostic['cdf_normal_error_floating']:.7f}, "
              f"local mass error={diagnostic['local_mass_normal_error_floating']:.7f}")
    print(f"Results: {output}")


if __name__ == "__main__":
    main()
