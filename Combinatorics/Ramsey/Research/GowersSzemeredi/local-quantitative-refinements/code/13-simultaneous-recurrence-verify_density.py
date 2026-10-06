#!/usr/bin/env python3
"""Numerical checks of the sharp real-phase and weighted selection bounds.

These checks audit formulas and extremizers; they are not replacements for
the proofs in the article. Only the Python standard library is required.
"""

from __future__ import annotations

import cmath
import json
import math
from pathlib import Path
import random


def frontier(a: float, b: float, s: float, t: float) -> dict[str, float]:
    v = (2 * a * b + (b - a) * t) / (a + b)
    h = math.sqrt((1 - s * s) * t * t + s * s * v * v)
    baseline = a * (t + h) / (a + t)
    gain = (a + b) * (v - h) / (a + t)
    return {"v": v, "h": h, "H": baseline, "K": gain}


def binary_cell(a: float, b: float, x: float, mass: float,
                radius: float) -> dict[str, float]:
    positive_frequency = (a + x) / (a + b)
    p = mass * positive_frequency * b
    n = mass * (1 - positive_frequency) * a
    angle = math.asin(radius)
    correlation = abs(p * cmath.exp(1j * angle)
                      - n * cmath.exp(-1j * angle))
    return {"mass": mass, "average": x, "positive": p, "negative": n,
            "variation": p + n, "discrepancy": abs(p - n),
            "correlation": correlation}


def check_close(x: float, y: float, tolerance: float = 3e-12) -> None:
    assert abs(x - y) <= tolerance * max(1.0, abs(x), abs(y)), (x, y)


def sharp_examples() -> list[dict]:
    output = []
    for a, b, s, t, u, e in [
        (.2, .8, .1, .005, .04, .01),
        (.2, .8, .1, .01, .07, .015),
        (.5, .5, .35, .07, .12, .025),
        (.9, .1, .0, .02, .3, .04),
        (.11, .34, .7, .021, .12, .02),
    ]:
        y = (a - (a + b) * u) / (a + t)
        z = (t + (b - t) * u) / (a + t)
        cells = [binary_cell(a, b, b, e, 1),
                 binary_cell(a, b, b, u - e, s),
                 binary_cell(a, b, t, y, s),
                 binary_cell(a, b, -a, z, s)]
        law = frontier(a, b, s, t)
        total = sum(c["correlation"] for c in cells)
        check_close(sum(c["mass"] for c in cells), 1)
        check_close(sum(c["mass"] * c["average"] for c in cells), 0)
        check_close(total, law["H"] + law["K"] * u)
        check_close((total - law["H"]) / law["K"] - e, u - e)
        output.append({"a": a, "b": b, "radius": s, "threshold": t,
                       "unrestricted_mass": u, "exceptional_mass": e,
                       "good_high_mass": u - e, "correlation": total,
                       "extremizer_cell_masses": [c["mass"] for c in cells],
                       "extremizer_cell_averages": [c["average"] for c in cells],
                       **law})
    return output


def randomized_checks(trials: int = 50000) -> dict:
    rng = random.Random(6141525)
    worst_joint_slack = math.inf
    worst_affine_slack = math.inf
    worst_squared_slack = math.inf
    worst_selection_slack = math.inf
    for _ in range(trials):
        count = rng.randrange(2, 20)
        raw_weights = [rng.uniform(.001, 1) for _ in range(count)]
        weights = [w / sum(raw_weights) for w in raw_weights]
        densities = [rng.random() for _ in range(count)]
        a = sum(w * d for w, d in zip(weights, densities))
        b = 1 - a
        s = rng.random() * .99
        t = rng.random() * b * .99
        exceptions = [rng.random() < .2 for _ in range(count)]
        cells = []
        for w, d, exceptional in zip(weights, densities, exceptions):
            radius = rng.random() if exceptional else s * rng.random()
            cells.append(binary_cell(a, b, d - a, w, radius))
        correlation = sum(c["correlation"] for c in cells)
        e = sum(w for w, flag in zip(weights, exceptions) if flag)
        q = sum(c["mass"] for c, flag in zip(cells, exceptions)
                if not flag and c["average"] > t)
        law = frontier(a, b, s, t)
        slack = law["H"] + law["K"] * (e + q) - correlation
        assert slack >= -1e-12, (law, e, q, correlation)
        worst_joint_slack = min(worst_joint_slack, slack)

        # All cells at the common allowed radius test the squared and affine
        # estimates; the squared bound is attained by each binary cell.
        controlled = [binary_cell(a, b, d - a, w, s)
                      for w, d in zip(weights, densities)]
        for c in controlled:
            squared_slack = ((1 - s * s) * c["discrepancy"] ** 2
                            + s * s * c["variation"] ** 2
                            - c["correlation"] ** 2)
            assert squared_slack >= -1e-12
            worst_squared_slack = min(worst_squared_slack, squared_slack)
        C = sum(c["correlation"] for c in controlled)
        V = sum(c["variation"] for c in controlled)
        D = sum(c["discrepancy"] for c in controlled)
        affine_slack = s * V + (1 - s) * D - C
        assert affine_slack >= -1e-12
        worst_affine_slack = min(worst_affine_slack, affine_slack)

        p = D / 2
        mass_high = sum(c["mass"] for c in controlled if c["average"] > t)
        rho = (p * (1 + t / a) - t) / (b - t)
        selection_slack = mass_high - rho
        assert selection_slack >= -1e-12
        worst_selection_slack = min(worst_selection_slack, selection_slack)
    return {"trials": trials, "seed": 6141525,
            "minimum_joint_slack": worst_joint_slack,
            "minimum_affine_slack": worst_affine_slack,
            "minimum_squared_slack": worst_squared_slack,
            "minimum_selection_slack": worst_selection_slack,
            "status": "all inequalities satisfied within 1e-12 tolerance"}


def illustrative_values() -> list[dict]:
    a, b, alpha, s = .2, .8, .04, .1
    V = 2 * a * b
    p = (alpha - s * V) / (2 * (1 - s))
    output = []
    for t in [.005, .01]:
        law = frontier(a, b, s, t)
        simple_mass = max(0, (p * (1 + t / a) - t) / (b - t))
        exact_mass = max(0, (alpha - law["H"]) / law["K"])
        output.append({"delta": a, "alpha": alpha, "radius": s,
                       "threshold": t, **law,
                       "guaranteed_high_mass_joint": exact_mass,
                       "guaranteed_high_mass_composed_affine": simple_mass})
    lo, hi = 0., b
    for _ in range(100):
        mid = (lo + hi) / 2
        if frontier(a, b, s, mid)["H"] < alpha:
            lo = mid
        else:
            hi = mid
    output.append({"delta": a, "alpha": alpha, "radius": s,
                   "max_increment_joint": (lo + hi) / 2,
                   "max_increment_composed_affine": a * p / (a - p)})
    return output


def fourier_endpoint_checks() -> dict:
    count = 0
    for a in [.000001, .0001, .001, .01, .05, .1, .2, .5, .8, .95, .999]:
        b = 1 - a
        for fraction in [.0001, .01, .1, .5, 1.]:
            alpha = fraction * min(a, b)
            radius = alpha / (4 * a * b)
            epsilon = math.asin(radius) / math.pi
            p = alpha / (4 * (1 - radius))
            increment = a * p / (a - p)
            other_formula = alpha / (4 - alpha * (1 + b) / (a * b))
            check_close(increment, other_formula)
            assert 0 < radius <= .5 + 1e-12
            assert 0 < increment <= b + 1e-12
            assert increment >= alpha / 4 - 1e-12
            for N in [1, 2, 3, 10, 100, 1000, 10**6, 10**12]:
                L = max(1, math.floor(math.sqrt(epsilon * N / 2)))
                bound = math.sqrt(alpha * N / (32 * math.pi * a * b))
                assert L >= bound - 1e-8 * max(1, bound)
                count += 1
    return {"parameter_checks": count,
            "note": "Analytic parameter/rounding checks; not a search over sets A.",
            "status": "all endpoint and length inequalities satisfied"}


def main() -> None:
    results = {"scope": "Numerical audit, not a proof or a Lean formalization",
               "sharp_extremizers": sharp_examples(),
               "randomized_checks": randomized_checks(),
               "illustrations": illustrative_values(),
               "fourier_endpoint_checks": fourier_endpoint_checks()}
    destination = Path(__file__).with_name("density_summary.json")
    destination.write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps({"saved": str(destination),
                      "randomized_checks": results["randomized_checks"],
                      "illustrations": results["illustrations"],
                      "fourier_endpoint_checks": results["fourier_endpoint_checks"]},
                     indent=2))


if __name__ == "__main__":
    main()
