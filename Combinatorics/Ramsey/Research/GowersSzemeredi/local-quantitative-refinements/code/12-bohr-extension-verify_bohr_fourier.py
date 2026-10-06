#!/usr/bin/env python3
"""Reproducible finite checks for one-scale Bohr regularization and smoothing.

The regularization checks use exact rational arithmetic in cyclic and product
groups. Fourier checks compute the fourfold convolution directly and compare it
with the spectral bound numerically. These checks illustrate the proved
theorems; they are not substitutes for the proofs or a Lean certification.

Run: python verify_bohr_fourier.py --output verification_bohr_fourier.json
Requires Python 3 and NumPy. The random seed is fixed and recorded.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
from fractions import Fraction
from pathlib import Path
import random

import numpy as np


SEED = 20261006


def elements(moduli: tuple[int, ...]) -> list[tuple[int, ...]]:
    return list(itertools.product(*(range(n) for n in moduli)))


def torus_norm(x: Fraction) -> Fraction:
    y = x - math.floor(x)
    return min(y, 1 - y)


def exact_bohr_checks() -> dict:
    rng = random.Random(SEED)
    moduli_list = [(3,), (5,), (7,), (11,), (13,), (31,), (61,), (3, 3), (3, 5),
                   (5, 5), (2, 4), (2, 3, 3)]
    radii = [Fraction(1, 6), Fraction(1, 4), Fraction(1, 3),
             Fraction(2, 5), Fraction(1, 2)]
    counts = {"frequency_sets": 0, "covering_cases": 0,
              "selected_radius_cases": 0, "overlap_checks": 0,
              "nonzero_shift_overlap_checks": 0}
    min_selected_ratio = {3: Fraction(1), 4: Fraction(1)}
    proper_overlap_counts = {3: 0, 4: 0}
    witnesses = []
    for moduli in moduli_list:
        group = elements(moduli)
        zero = tuple(0 for _ in moduli)
        index = {x: i for i, x in enumerate(group)}
        frequencies = group
        choices: set[tuple[tuple[int, ...], ...]] = set()
        choices.update((chi,) for chi in frequencies)
        # Include all pairs in the small groups; sample pairs in larger ones.
        pairs = list(itertools.combinations(frequencies, 2))
        choices.update(pairs if len(pairs) <= 35 else rng.sample(pairs, 35))
        if len(frequencies) >= 3:
            for _ in range(25):
                choices.add(tuple(sorted(rng.sample(frequencies, 3))))
        for gamma in sorted(choices):
            d = len(gamma)
            counts["frequency_sets"] += 1
            norms = []
            for x in group:
                norms.append(max(torus_norm(sum(
                    (Fraction(a * b, n) for a, b, n in
                     zip(chi, x, moduli)), Fraction(0))) for chi in gamma))

            def bohr(radius: Fraction) -> set[int]:
                return {i for i, value in enumerate(norms) if value <= radius}

            for rho in radii:
                outer = bohr(rho)
                half = bohr(rho / 2)
                assert len(outer) <= 4 ** d * len(half)
                counts["covering_cases"] += 1
                for factor in (3, 4):
                    cells = factor * d
                    step = rho / (2 * cells)
                    previous = half
                    candidates = []
                    for j in range(1, cells + 1):
                        radius = rho / 2 + j * step
                        current = bohr(radius)
                        # ratio >= 4^(-1/factor), checked without radicals.
                        if 4 * len(previous) ** factor >= len(current) ** factor:
                            candidates.append((Fraction(len(previous), len(current)),
                                               radius, previous, current))
                        previous = current
                    assert candidates, (moduli, gamma, rho, factor)
                    ratio, radius, inner, selected = max(candidates, key=lambda x: x[0])
                    min_selected_ratio[factor] = min(min_selected_ratio[factor], ratio)
                    counts["selected_radius_cases"] += 1
                    for h_index in bohr(step):
                        h = group[h_index]
                        translated = {index[tuple((a + b) % n for a, b, n in
                                                  zip(group[i], h, moduli))]
                                      for i in selected}
                        overlap = selected & translated
                        assert inner <= overlap
                        assert 4 * len(overlap) ** factor >= len(selected) ** factor
                        counts["overlap_checks"] += 1
                        if h != zero:
                            counts["nonzero_shift_overlap_checks"] += 1
                            if overlap != selected:
                                proper_overlap_counts[factor] += 1
                            if (sum(w["factor"] == factor for w in witnesses) < 2
                                    and overlap != selected):
                                witnesses.append({
                                    "group": moduli, "frequencies": gamma,
                                    "rho": str(rho), "selected_radius": str(radius),
                                    "step_radius": str(step), "shift": h,
                                    "B_size": len(selected), "overlap_size": len(overlap),
                                    "factor": factor})
    assert counts["nonzero_shift_overlap_checks"] > 0
    assert min(proper_overlap_counts.values()) > 0
    return {
        "status": "passed",
        "arithmetic": "exact fractions and integer cardinality comparisons",
        "groups": moduli_list,
        **counts,
        "smallest_selected_overlap_fraction": {
            str(f): str(value) for f, value in min_selected_ratio.items()},
        "proper_nonempty_boundary_overlap_checks": proper_overlap_counts,
        "nontrivial_examples": witnesses,
    }


def direct_fourfold(f: np.ndarray) -> np.ndarray:
    """H=f*tilde(f)*f*tilde(f), using direct normalized correlations."""
    n = len(f)
    autocorrelation = np.array([np.mean(f * np.roll(f, j)) for j in range(n)])
    return np.array([np.mean(autocorrelation * np.roll(autocorrelation, j))
                     for j in range(n)])


def fourier_checks() -> dict:
    rng = np.random.default_rng(SEED)
    tests = 0
    nonzero_shifts = 0
    positive_residuals = 0
    maximum_identity_error = 0.0
    maximum_bound_violation = 0.0
    maximum_ratio_to_bound = 0.0
    examples = []
    for n in (7, 13, 31, 61):
        x = np.arange(n)
        profiles = [np.ones(n), np.full(n, 0.2),
                    (x < n // 3).astype(float), (x < 2 * n // 3).astype(float),
                    0.4 + 0.25 * np.cos(2 * math.pi * x / n)]
        profiles.extend(rng.random(n) for _ in range(3))
        profiles.extend((rng.random(n) < p).astype(float) for p in (0.2, 0.5, 0.8))
        for profile_index, f in enumerate(profiles):
            alpha = float(np.mean(f))
            spectrum = np.fft.fft(f) / n
            fourth_moment = float(np.sum(np.abs(spectrum) ** 4))
            H = direct_fourfold(f)
            identity_error = abs(float(H[0]) - fourth_moment)
            maximum_identity_error = max(maximum_identity_error, identity_error)
            assert identity_error <= 2e-13
            assert alpha ** 4 - 2e-13 <= fourth_moment <= alpha ** 3 + 2e-13
            for tau in (0.05, 0.1, 0.2, 0.35):
                gamma = np.flatnonzero(np.abs(spectrum) >= tau)
                assert len(gamma) <= alpha / tau ** 2 + 2e-12
                for rho in (0.02, 0.06, 0.125, 0.25, 0.49):
                    for h in range(n):
                        phases = ((gamma * h) % n) / n
                        if len(phases) and np.max(np.minimum(phases, 1 - phases)) > rho:
                            continue
                        residual = float(np.max(np.abs(np.roll(H, -h) - H)))
                        bound = 2 * math.pi * rho * fourth_moment + 2 * tau ** 2 * alpha
                        coarse_bound = 2 * math.pi * rho * alpha ** 3 + 2 * tau ** 2 * alpha
                        assert residual <= bound + 2e-13
                        assert bound <= coarse_bound + 2e-13
                        maximum_bound_violation = max(maximum_bound_violation, residual - bound)
                        if bound > 0:
                            maximum_ratio_to_bound = max(maximum_ratio_to_bound, residual / bound)
                        tests += 1
                        if h:
                            nonzero_shifts += 1
                        if residual > 1e-10:
                            positive_residuals += 1
                            if len(examples) < 4 and rho <= 0.125:
                                examples.append({"n": n, "profile_index": profile_index,
                                                 "alpha": alpha, "tau": tau,
                                                 "rho": rho, "rank": len(gamma), "shift": h,
                                                 "residual": residual, "proved_bound": bound})
    assert positive_residuals > 0 and nonzero_shifts > 0
    return {"status": "passed", "arithmetic": "IEEE double, tolerance 2e-13",
            "profiles": 44, "bound_checks": tests,
            "nonzero_shift_checks": nonzero_shifts,
            "positive_residual_checks": positive_residuals,
            "maximum_fourth_moment_identity_error": maximum_identity_error,
            "maximum_positive_bound_violation": maximum_bound_violation,
            "maximum_observed_ratio_to_bound": maximum_ratio_to_bound,
            "examples": examples}


def parameter_checks() -> dict:
    eta = Fraction(1, 2 ** 43)
    assert 360 ** 5 < 2 ** 43  # Exactly proves theta < 1/36 and sqrt(theta) < 1/6.
    theta = 10 * float(eta) ** 0.2
    assert math.sqrt(theta) < Fraction(1, 6)
    rows = []
    for alpha in (Fraction(1, 100), Fraction(1, 10), Fraction(1, 6),
                  Fraction(1, 4), Fraction(1, 2), Fraction(1)):
        # Main schedule in the article: retain the minimum rather than replacing
        # it by a smaller expression that is merely convenient at all densities.
        main_component_radius = min(alpha / 192, alpha ** 2 / 32)
        main_sigma = eta * alpha * main_component_radius ** 4 / 384
        assert main_component_radius > 0
        assert main_component_radius <= alpha / 192
        assert main_component_radius <= alpha ** 2 / 32
        assert main_sigma <= eta * alpha ** 2
        assert main_sigma <= eta * main_component_radius * alpha ** 2 / 16
        assert main_sigma < alpha ** 2 / 16
        main_lambda_squared = main_sigma * alpha ** 2 / 4
        main_rank_bound = alpha / main_lambda_squared
        main_rho_times_pi = main_sigma / 4
        main_zeta_times_pi = main_rho_times_pi / (6 * main_rank_bound)
        assert main_rank_bound == 4 / (main_sigma * alpha)
        assert 2 * main_rho_times_pi + 2 * main_lambda_squared / alpha ** 2 == main_sigma
        assert main_zeta_times_pi == main_sigma ** 2 * alpha / 96

        # This smaller all-density schedule is retained as a labelled safe
        # alternative, not confused with the article's optimized minimum.
        varrho = alpha ** 2 / 192
        sigma = eta * varrho ** 4 * alpha / 384
        assert varrho <= min(alpha / 192, alpha ** 2 / 32)
        assert sigma <= eta * alpha ** 2
        assert sigma <= eta * varrho * alpha ** 2 / 16
        assert sigma < alpha ** 2 / 16
        assert sigma <= main_sigma
        assert sigma == Fraction(1, 2 ** 74 * 3 ** 5) * alpha ** 9
        tau_squared = sigma * alpha ** 2 / 4
        rank_bound = alpha / tau_squared
        assert rank_bound == 4 / (sigma * alpha)
        # Remove pi to make the radius identities exactly rational.
        rho_times_pi = sigma / 4
        zeta_times_pi = rho_times_pi / (6 * rank_bound)
        assert zeta_times_pi == sigma ** 2 * alpha / 96
        row = {"alpha": str(alpha),
               "main_component_radius": str(main_component_radius),
               "main_sigma": str(main_sigma),
               "main_lambda_squared": str(main_lambda_squared),
               "main_rank_bound": str(main_rank_bound),
               "main_rho_times_pi": str(main_rho_times_pi),
               "main_zeta_times_pi": str(main_zeta_times_pi),
               "safe_alternative_component_radius": str(varrho),
               "safe_sigma": str(sigma),
               "safe_rank_bound": str(rank_bound),
               "safe_rho_times_pi": str(rho_times_pi),
               "safe_zeta_times_pi": str(zeta_times_pi)}
        if alpha <= Fraction(1, 6):
            # Optimized sparse branch of the main schedule (different spectrum
            # from the next, original-threshold specialization).
            assert main_component_radius == alpha ** 2 / 32
            assert main_sigma == alpha ** 9 / (3 * 2 ** 70)
            assert main_lambda_squared == alpha ** 11 / (3 * 2 ** 72)
            assert main_rank_bound == 3 * 2 ** 72 / alpha ** 10
            assert main_zeta_times_pi == alpha ** 19 / (27 * 2 ** 145)
            low_varrho = alpha ** 2 / 32
            low_sigma = Fraction(1, 2 ** 72) * alpha ** 9
            assert low_varrho <= alpha / 192
            assert low_sigma <= eta * low_varrho ** 4 * alpha / 384
            assert low_sigma <= eta * low_varrho * alpha ** 2 / 16
            assert low_sigma / sigma == 972
            assert (low_sigma / 4) / (6 * 4 / (low_sigma * alpha)) == (
                alpha ** 19 / (3 * 2 ** 149))
            fixed_spectrum_zeta_times_pi = alpha ** 19 / (3 * 2 ** 149)
            assert main_sigma / low_sigma == Fraction(4, 3)
            assert main_zeta_times_pi / fixed_spectrum_zeta_times_pi == Fraction(16, 9)
            row["optimized_sparse_sigma"] = str(main_sigma)
            row["optimized_sparse_lambda_squared"] = str(main_lambda_squared)
            row["optimized_sparse_zeta_times_pi"] = str(main_zeta_times_pi)
            row["optimized_vs_fixed_spectrum_radius_factor"] = "16/9"
            row["low_density_sigma"] = str(low_sigma)
            row["low_density_rank_improvement_factor"] = 972
            row["low_density_radius_improvement_factor"] = 972 ** 2
        else:
            assert main_component_radius == alpha / 192
            assert main_sigma == alpha ** 5 / (2 ** 74 * 3 ** 5)
            assert main_zeta_times_pi == alpha ** 11 / (2 ** 153 * 3 ** 11)
        rows.append(row)
    boundary_4 = 1 - 4 ** (-1 / 4)
    boundary_3 = 1 - 4 ** (-1 / 3)
    assert 3 / 8 + 2 * boundary_4 < 1
    assert Fraction(11, 8) ** 2 < 2  # Exact equivalent of the preceding strict inequality.
    assert Fraction(5, 8) ** 3 < Fraction(1, 4)  # Exactly gives boundary_3 < 3/8.
    assert 3 * theta + 2 * boundary_3 < 1
    assert 1 - 2 * theta - boundary_3 > 2 * math.sqrt(theta)
    return {"status": "passed", "arithmetic": "rational except displayed radicals",
            "schedule_descriptions": {
                "main": "component radius min(alpha/192,alpha^2/32); sigma=eta*alpha*radius^4/384",
                "safe_alternative": "component radius alpha^2/192; sigma=2^-74*3^-5*alpha^9",
                "fixed_original_spectrum": "alpha<=1/6; sigma=2^-72*alpha^9",
                "optimized_sparse_branch": "alpha<=1/6; main sigma=2^-70*alpha^9/3"},
            "schedule_checks": {"main": 6, "safe_alternative": 6,
                                "fixed_original_spectrum": 3, "optimized_sparse_branch": 3},
            "theta": theta, "sqrt_theta": math.sqrt(theta),
            "density_7_over_8_extension_slack": 1 - 3 / 8 - 2 * boundary_4,
            "section_10_extension_slack": 1 - 3 * theta - 2 * boundary_3,
            "section_10_common_fibre_slack": 1 - 2 * theta - boundary_3 - 2 * math.sqrt(theta),
            "rows": rows}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("verification_bohr_fourier.json"))
    args = parser.parse_args()
    report = {"seed": SEED, "scope": "finite examples and parameter arithmetic; not formal proof",
              "bohr_regularization": exact_bohr_checks(),
              "fourier_smoothing": fourier_checks(), "parameters": parameter_checks()}
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": "passed", "report": str(args.output),
                      "bohr_selected_radius_cases": report["bohr_regularization"]["selected_radius_cases"],
                      "bohr_overlap_checks": report["bohr_regularization"]["overlap_checks"],
                      "fourier_bound_checks": report["fourier_smoothing"]["bound_checks"],
                      "maximum_identity_error": report["fourier_smoothing"]["maximum_fourth_moment_identity_error"]},
                     indent=2))


if __name__ == "__main__":
    main()
