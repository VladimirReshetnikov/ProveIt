#!/usr/bin/env python3
"""Exact finite-moment certificates for an infinite integer spectrum.

This module uses only the Python standard library. Every decision in
``certify`` is made with fractions.Fraction; floats are used only to display
short decimal summaries in the example output.

Run the reproducible infinite-tail examples with::

    python3 code/certify.py

The default output is artifacts/certificate_results.json, relative to this
file's parent directory. To verify other certified moment enclosures::

    python3 code/certify.py --input input.json --output result.json

Input format (all numeric strings are exact integers, decimals, or a/b):

    {
      "centers": ["1", "1/2", "1/4"],
      "radii": ["1/20", "1/40", "1/80"],
      "K": 25,
      "threshold": "1/8",
      "moments": {
        "25": {"mid": "...", "error": "..."},
        "26": {"mid": "...", "error": "..."}
      }
    }

All moments from K through K+2*m must be supplied. An enclosure is trusted
input: this verifier proves the consequences of the supplied bounds; it does
not prove that arbitrary user-supplied moments describe the intended spectrum.
The exact examples below derive their moments from a convergent geometric
series, so their inputs require no floating-point or truncated-tail assumption.

This is executable exact arithmetic, not a Lean or other proof-assistant
formalization of the general analytic theorem.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path
from typing import Iterable, Mapping, Sequence

F = Fraction
Polynomial = list[Fraction]  # coefficients in ascending power order
MomentEnclosure = tuple[Fraction, Fraction]  # midpoint, absolute error


def q(value: str | int | Fraction) -> Fraction:
    """Parse exact values; reject binary floats at the API boundary."""
    if isinstance(value, float):
        raise TypeError("Use an exact rational/decimal string, not a float")
    return Fraction(value)


def poly_trim(a: Sequence[Fraction]) -> Polynomial:
    out = list(a)
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out or [F(0)]


def poly_add(a: Sequence[Fraction], b: Sequence[Fraction]) -> Polynomial:
    out = [F(0)] * max(len(a), len(b))
    for i, c in enumerate(a):
        out[i] += c
    for i, c in enumerate(b):
        out[i] += c
    return poly_trim(out)


def poly_scale(a: Sequence[Fraction], c: Fraction) -> Polynomial:
    return poly_trim([c * v for v in a])


def poly_mul(a: Sequence[Fraction], b: Sequence[Fraction]) -> Polynomial:
    out = [F(0)] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                if bj:
                    out[i + j] += ai * bj
    return poly_trim(out)


def poly_pow(a: Sequence[Fraction], n: int) -> Polynomial:
    if n < 0:
        raise ValueError("Polynomial exponent must be nonnegative")
    result = [F(1)]
    base = list(a)
    while n:
        if n & 1:
            result = poly_mul(result, base)
        n //= 2
        if n:
            base = poly_mul(base, base)
    return result


def poly_eval(a: Sequence[Fraction], x: Fraction) -> Fraction:
    result = F(0)
    for coefficient in reversed(a):
        result = result * x + coefficient
    return result


def poly_derivative(a: Sequence[Fraction]) -> Polynomial:
    return poly_trim([i * a[i] for i in range(1, len(a))])


def product(values: Iterable[Fraction]) -> Fraction:
    result = F(1)
    for value in values:
        result *= value
    return result


def annihilator(centers: Sequence[Fraction]) -> Polynomial:
    result = [F(1)]
    for center in centers:
        result = poly_mul(result, [-center, F(1)])
    return result


def hermite_polynomials(
    centers: Sequence[Fraction], K: int
) -> list[Polynomial]:
    """Return Q_i=(x/a_i)^K(1-d_i(x-a_i))L_i(x)^2."""
    result: list[Polynomial] = []
    for i, ai in enumerate(centers):
        others = [aj for j, aj in enumerate(centers) if j != i]
        D = product(ai - aj for aj in others)
        L = poly_scale(annihilator(others), 1 / D)
        d = F(K) / ai + 2 * sum((1 / (ai - aj) for aj in others), F(0))
        linear = [1 + d * ai, -d]
        core = poly_scale(poly_mul(linear, poly_pow(L, 2)), ai ** (-K))
        result.append([F(0)] * K + core)
    return result


def count_constant(
    centers: Sequence[Fraction], radii: Sequence[Fraction], i: int, K: int
) -> Fraction:
    ai, ri = centers[i], radii[i]
    others = [aj for j, aj in enumerate(centers) if j != i]
    b = ai - ri
    gaps = [abs(ai - aj) - ri for aj in others]
    D = product(ai - aj for aj in others)
    d = F(K) / ai + 2 * sum((1 / (ai - aj) for aj in others), F(0))
    A = product(g ** (-2) for g in gaps)
    T = F(K) / b + 2 * sum((1 / g for g in gaps), F(0))
    U = F(K) / b**2 + 2 * sum((1 / g**2 for g in gaps), F(0))
    inside = F(1, 2) * b ** (-K) * A * (T**2 + U)
    outside = ai ** (-K) / D**2 * (ri ** (-2) + abs(d) / ri)
    return max(inside, outside)


def linear_enclosure(
    polynomial: Sequence[Fraction], moments: Mapping[int, MomentEnclosure]
) -> MomentEnclosure:
    mid, error = F(0), F(0)
    for degree, coefficient in enumerate(polynomial):
        if coefficient:
            moment_mid, moment_error = moments[degree]
            mid += coefficient * moment_mid
            error += abs(coefficient) * moment_error
    return mid, error


def floor_fraction(value: Fraction) -> int:
    return value.numerator // value.denominator


def ceil_fraction(value: Fraction) -> int:
    return -((-value.numerator) // value.denominator)


def certify(
    centers: Sequence[Fraction],
    radii: Sequence[Fraction],
    K: int,
    threshold: Fraction,
    moments: Mapping[int, MomentEnclosure],
) -> dict:
    """Verify the theorem's residual and integer-count inequalities exactly.

    Return values contain Fraction objects until ``json_safe`` is called.
    "success" means complete coverage of all atoms >= threshold and a unique
    exact integer count in each proposed open interval. The theorem requires
    the true spectrum to be positive, summable, and of integer multiplicity.
    """
    centers, radii = [q(a) for a in centers], [q(r) for r in radii]
    threshold = q(threshold)
    m = len(centers)
    if type(K) is not int or K < 1:
        raise ValueError("K must be a positive integer")
    if len(radii) != m:
        raise ValueError("There must be one radius per center")
    if threshold <= 0:
        raise ValueError("The threshold must be positive")
    for i, (ai, ri) in enumerate(zip(centers, radii)):
        if not (0 < ri < ai):
            raise ValueError("Each radius must satisfy 0 < radius < center")
        for j in range(i):
            if abs(ai - centers[j]) <= ri + radii[j]:
                raise ValueError("Proposed intervals must be strictly disjoint")
    prepared = {}
    for j in range(K, K + 2 * m + 1):
        if j not in moments:
            raise ValueError(f"Missing moment p_{j}")
        mid, error = moments[j]
        mid, error = q(mid), q(error)
        if error < 0:
            raise ValueError("Moment error bounds must be nonnegative")
        prepared[j] = (mid, error)

    P = annihilator(centers)
    residual_polynomial = [F(0)] * K + poly_pow(P, 2)
    Rmid, Rerror = linear_enclosure(residual_polynomial, prepared)
    Rplus = Rmid + Rerror
    if Rplus < 0:
        raise ValueError("Input enclosures contradict residual nonnegativity")

    missing_denominator = threshold**K * product(r * r for r in radii)
    missing_bound = Rplus / missing_denominator
    no_missing = missing_bound < 1
    above_threshold = all(ai - ri > threshold for ai, ri in zip(centers, radii))
    counts = []
    for i, Q in enumerate(hermite_polynomials(centers, K)):
        Smid, Serror = linear_enclosure(Q, prepared)
        C = count_constant(centers, radii, i, K)
        total_error = Serror + C * Rplus
        lower, upper = Smid - total_error, Smid + total_error
        integer_lower = max(0, ceil_fraction(lower))
        integer_upper = floor_fraction(upper)
        unique = integer_lower == integer_upper and integer_lower >= 0
        counts.append(
            {
                "center": centers[i],
                "radius": radii[i],
                "interval": [centers[i] - radii[i], centers[i] + radii[i]],
                "S_mid": Smid,
                "S_moment_error": Serror,
                "C": C,
                "count_error": total_error,
                "count_enclosure": [lower, upper],
                "possible_integer_counts": [integer_lower, integer_upper],
                "certified_count": integer_lower if unique else None,
            }
        )

    success = no_missing and above_threshold and all(
        row["certified_count"] is not None for row in counts
    )
    return {
        "success": success,
        "K": K,
        "m": m,
        "moment_indices": list(range(K, K + 2 * m + 1)),
        "moment_count": 2 * m + 1,
        "residual_mid": Rmid,
        "residual_moment_error": Rerror,
        "residual_upper": Rplus,
        "missing_denominator": missing_denominator,
        "missing_upper_bound": missing_bound,
        "missing_integer_upper_bound": floor_fraction(missing_bound),
        "no_missing_atoms": no_missing,
        "intervals_strictly_above_threshold": above_threshold,
        "counts": counts,
    }


def exact_model_moment(j: int) -> Fraction:
    """Spectrum: 1 (once), 1/2 (twice), 1/4 (once), 2^-n, n>=4."""
    if j < 1:
        raise ValueError("Only positive moments converge")
    return F(1) + 2 * F(1, 2) ** j + F(1, 4) ** j + F(1, 16) ** j / (
        1 - F(1, 2) ** j
    )


def rounded_enclosure(value: Fraction, decimal_places: int) -> MomentEnclosure:
    """Round to nearest decimal, retaining a proved half-unit error bound."""
    scale = 10**decimal_places
    scaled = value * scale
    rounded = floor_fraction(scaled + F(1, 2))
    midpoint, error = F(rounded, scale), F(1, 2 * scale)
    if abs(value - midpoint) > error:
        raise AssertionError("Internal decimal enclosure failure")
    return midpoint, error


def model_enclosures(
    K: int, m: int, decimal_places: int | None = None
) -> dict[int, MomentEnclosure]:
    return {
        j: (
            (exact_model_moment(j), F(0))
            if decimal_places is None
            else rounded_enclosure(exact_model_moment(j), decimal_places)
        )
        for j in range(K, K + 2 * m + 1)
    }


def input_record(
    centers: Sequence[Fraction],
    radii: Sequence[Fraction],
    K: int,
    threshold: Fraction,
    moments: Mapping[int, MomentEnclosure],
) -> dict:
    return {
        "centers": list(centers),
        "radii": list(radii),
        "K": K,
        "threshold": threshold,
        "moments": {
            str(j): {"mid": mid, "error": error}
            for j, (mid, error) in sorted(moments.items())
        },
    }


def brief(result: dict) -> dict:
    return {
        "K": result["K"],
        "success": result["success"],
        "missing_bound_decimal": format(float(result["missing_upper_bound"]), ".10g"),
        "counts": [r["certified_count"] for r in result["counts"]],
        "count_error_decimals": [
            format(float(r["count_error"]), ".10g") for r in result["counts"]
        ],
    }


def examples() -> dict:
    centers = [F(1), F(1, 2), F(1, 4)]
    radii = [F(1, 20), F(1, 40), F(1, 80)]
    threshold = F(1, 8)
    expected_counts = [1, 2, 1]
    scans = []
    first = None
    for K in range(1, 81):
        moments = model_enclosures(K, len(centers))
        result = certify(centers, radii, K, threshold, moments)
        if K in (1, 4, 8, 12, 16, 20, 24, 25, 28, 32):
            scans.append(brief(result))
        if result["success"]:
            first = (K, moments, result)
            if K not in (1, 4, 8, 12, 16, 20, 24, 25, 28, 32):
                scans.append(brief(result))
            break
    if first is None:
        raise AssertionError("The exact infinite-tail example failed to certify")
    K, exact_moments, exact_result = first
    if [row["certified_count"] for row in exact_result["counts"]] != expected_counts:
        raise AssertionError("Exact certificate disagrees with the known model")

    precision_scan = []
    rounded = None
    for digits in (12, 16, 20, 24, 28, 32, 36, 40, 48, 64):
        moments = model_enclosures(K, len(centers), digits)
        result = certify(centers, radii, K, threshold, moments)
        precision_scan.append({"decimal_places": digits, **brief(result)})
        if result["success"]:
            rounded = (digits, moments, result)
            break
    if rounded is None:
        raise AssertionError("Rounded moment example failed to certify")
    digits, rounded_moments, rounded_result = rounded
    if [row["certified_count"] for row in rounded_result["counts"]] != expected_counts:
        raise AssertionError("Rounded certificate disagrees with the known model")

    eta = F(1, 10**20)
    perturbed_centers = [centers[0] + eta, centers[1] - eta, centers[2] + eta]
    perturbed_result = certify(perturbed_centers, radii, K, threshold, rounded_moments)
    if not perturbed_result["success"] or [
        row["certified_count"] for row in perturbed_result["counts"]
    ] != expected_counts:
        raise AssertionError("Perturbed-center certificate failed")

    # A genuinely missing cluster must prevent a completeness certificate.
    omitted_centers, omitted_radii = [centers[0], centers[2]], [radii[0], radii[2]]
    omitted_moments = model_enclosures(K, len(omitted_centers))
    omitted_result = certify(omitted_centers, omitted_radii, K, threshold, omitted_moments)
    if omitted_result["success"] or omitted_result["no_missing_atoms"]:
        raise AssertionError("An omitted cluster was incorrectly certified")

    # Deliberately inadequate but valid moment intervals must not pass.
    coarse_moments = model_enclosures(K, len(centers), 16)
    coarse_result = certify(centers, radii, K, threshold, coarse_moments)
    if coarse_result["success"]:
        raise AssertionError("The coarse-precision negative control unexpectedly passed")

    scenarios = []
    for name, a, r, moments, result, detail in (
        (
            "exact_infinite_tail", centers, radii, exact_moments, exact_result,
            "Exact rational moments, including the complete geometric tail.",
        ),
        (
            "rounded_moment_enclosures", centers, radii, rounded_moments, rounded_result,
            f"Moments rounded to {digits} decimal places with exact half-unit bounds.",
        ),
        (
            "perturbed_centers", perturbed_centers, radii, rounded_moments, perturbed_result,
            "Centers shifted by signed 10^-20; the rounded moments are unchanged.",
        ),
        (
            "omitted_cluster_negative_control", omitted_centers, omitted_radii,
            omitted_moments, omitted_result,
            "The center 1/2, which has multiplicity two, is deliberately omitted.",
        ),
        (
            "coarse_precision_negative_control", centers, radii, coarse_moments, coarse_result,
            "Valid moment enclosures rounded to only 16 decimal places.",
        ),
    ):
        scenarios.append(
            {
                "name": name,
                "detail": detail,
                "input": input_record(a, r, K, threshold, moments),
                "result": result,
                "summary": brief(result),
            }
        )

    # Independent algebraic checks of the cardinal properties used by the proof.
    for i, Q in enumerate(hermite_polynomials(centers, K)):
        derivative = poly_derivative(Q)
        for j, center in enumerate(centers):
            if poly_eval(Q, center) != int(i == j) or poly_eval(derivative, center) != 0:
                raise AssertionError("Hermite cardinal polynomial identity failed")

    return {
        "format": "integer-spectrum-moment-certificate-v1",
        "arithmetic": "All certificate decisions are exact rational arithmetic.",
        "model": {
            "spectrum": "1 once; 1/2 twice; 1/4 once; 2^(-n) once for every n>=4",
            "moment_formula": "p_j=1+2*(1/2)^j+(1/4)^j+(1/16)^j/(1-2^(-j)), j>=1",
            "threshold": threshold,
            "true_counts_above_threshold": expected_counts,
            "total_count_above_threshold": sum(expected_counts),
            "tail_first_moment": F(1, 8),
            "tail_maximum": F(1, 16),
        },
        "first_successful_K_in_scan": K,
        "moment_count_for_three_clusters": 7,
        "K_scan": scans,
        "precision_scan": precision_scan,
        "scenarios": scenarios,
        "validation": {
            "Hermite_cardinal_values_and_derivatives": "passed exactly",
            "known_infinite_spectrum_cluster_counts": "passed exactly",
            "rounded_inputs_and_center_perturbations": "passed exactly",
            "omitted_cluster_and_coarse_precision_controls": "correctly rejected",
            "zeta_zeros_used": False,
            "finite_truncation_of_infinite_tail_used": False,
            "proof_assistant_verified": False,
        },
    }


def json_safe(value):
    if isinstance(value, Fraction):
        return str(value)
    if isinstance(value, dict):
        return {str(k): json_safe(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [json_safe(v) for v in value]
    return value


def parse_input(data: dict) -> tuple:
    raw_K = data["K"]
    if type(raw_K) is not int:
        raise ValueError("JSON K must be an integer, not a float or boolean")
    centers = [q(a) for a in data["centers"]]
    radii = [q(r) for r in data["radii"]]
    moments = {
        int(j): (q(row["mid"]), q(row["error"]))
        for j, row in data["moments"].items()
    }
    return centers, radii, raw_K, q(data["threshold"]), moments


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, help="Verify one JSON moment certificate input")
    parser.add_argument("--output", type=Path, help="Destination JSON; default is artifacts/certificate_results.json")
    args = parser.parse_args()
    output = args.output or Path(__file__).resolve().parents[1] / "artifacts" / "certificate_results.json"
    if args.input:
        data = json.loads(args.input.read_text(encoding="utf-8"))
        result = certify(*parse_input(data))
        payload = {"input": data, "result": result, "summary": brief(result)}
        print(json.dumps(brief(result), indent=2))
    else:
        payload = examples()
        print("Exact infinite-tail certificates:")
        for scenario in payload["scenarios"]:
            print(scenario["name"] + ": " + json.dumps(scenario["summary"]))
        print("All exact validation checks passed.")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(json_safe(payload), indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {output}")


if __name__ == "__main__":
    main()
