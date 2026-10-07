#!/usr/bin/env python3
"""Verify the twenty-bit Fourier-codimension witness using exact arithmetic.

Only the Python standard library is used.  All 5**5 tuples of four-bit
block sums are enumerated with their binomial multiplicities, covering all
2**20 sign strings.  The verifier constructs every observation cell and
checks its conditional moments.  Its degree check is exact and complete:
block symmetry reduces Walsh coefficients to the 5**5 profiles of subset
sizes in the five blocks.  All 56 profiles of degree greater than 16 vanish
on every cell, and a degree-16 coefficient is nonzero on every cell.

Run from any directory:
    python code/verify_witness.py
    python code/verify_witness.py --output /path/to/certificate.json
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from fractions import Fraction
from itertools import product
from math import comb, prod
from pathlib import Path


F = Fraction
BLOCK_SIZE = 4
BLOCK_COUNT = 5
BITS = BLOCK_SIZE * BLOCK_COUNT
CUBE_SIZE = 1 << BITS
VALUES = (-4, -2, 0, 2, 4)
MULTIPLICITIES = (1, 4, 6, 4, 1)
LEAF_VALUES = (-2, 0, 2, 4)
# The entries are zero-based leaf indices, in increasing central-sum order.
SELECTOR = (0, 1, 2, 3, 2)
EXPECTED_GAP = F(9, 34816)


def report(sums: tuple[int, ...]) -> tuple:
    """The complete pointwise reporter, including its disjoint tags."""
    center, *leaves = sums
    selected = SELECTOR[VALUES.index(center)]
    passing = tuple(value == target for value, target in zip(leaves, LEAF_VALUES))
    if all(passing):
        return ("B", tuple(leaves))
    if all(passing[i] for i in range(4) if i != selected):
        return ("A",)
    visible = tuple(leaves[i] for i in range(4) if i != selected)
    return ("ordinary", center, selected, visible)


def safe_comb(n: int, k: int) -> int:
    return comb(n, k) if 0 <= k <= n else 0


def layer_character_sum(subset_size: int, plus_count: int) -> int:
    """Sum of one fixed Walsh character on a four-bit sum layer.

    There are plus_count positive signs.  If h of the subset_size selected
    positions are positive, the character is (-1)**(subset_size-h).
    """
    return sum(
        (-1) ** (subset_size - h)
        * comb(subset_size, h)
        * safe_comb(BLOCK_SIZE - subset_size, plus_count - h)
        for h in range(subset_size + 1)
    )


CHARACTER_SUMS = tuple(
    tuple(layer_character_sum(size, plus_count) for plus_count in range(5))
    for size in range(5)
)


def walsh_numerator(states: list[tuple[int, ...]], profile: tuple[int, ...]) -> int:
    """Numerator of the cell's Walsh coefficient, with denominator 2**20."""
    return sum(
        prod(CHARACTER_SUMS[size][plus_count] for size, plus_count in zip(profile, state))
        for state in states
    )


def exact_reporter_objective() -> dict:
    """Independently evaluate the optimized singleton-reporter formula."""
    probabilities = tuple(F(count, 16) for count in MULTIPLICITIES)
    leaf_probabilities = tuple(probabilities[VALUES.index(value)] for value in LEAF_VALUES)
    q = prod(leaf_probabilities)
    r0 = F(0)
    r1 = F(0)
    h2 = F(0)
    for center, probability, selected in zip(VALUES, probabilities, SELECTOR):
        weight = probability / leaf_probabilities[selected]
        displacement = center - LEAF_VALUES[selected]
        r0 += weight
        r1 += weight * displacement
        h2 += weight * displacement * displacement
    kappa = r0 - 1
    predictor = sum(LEAF_VALUES) + r1 / kappa
    gap = q * (r1 * r1 / kappa - h2)
    assert (q, r0, r1, h2) == (F(3, 2048), F(20, 3), F(-37, 3), F(80, 3))
    assert predictor == F(31, 17)
    assert gap == EXPECTED_GAP
    return {
        "Q": str(q),
        "R0": str(r0),
        "K": str(kappa),
        "R1": str(r1),
        "H2": str(h2),
        "optimal_predictor": str(predictor),
        "exact_advantage": str(gap),
    }


def verify() -> dict:
    cells: dict[tuple, dict] = {}
    grouped_states = 0
    for state in product(range(5), repeat=5):
        sums = tuple(VALUES[j] for j in state)
        multiplicity = prod(MULTIPLICITIES[j] for j in state)
        label = report(sums)
        cell = cells.setdefault(label, {"states": [], "histogram": Counter()})
        cell["states"].append(state)
        cell["histogram"][sum(sums)] += multiplicity
        grouped_states += 1
    assert grouped_states == 5**5
    assert len(cells) == 622
    assert Counter(label[0] for label in cells) == {"A": 1, "B": 1, "ordinary": 620}
    assert sum(sum(cell["histogram"].values()) for cell in cells.values()) == CUBE_SIZE

    high_profiles = tuple(profile for profile in product(range(5), repeat=5) if sum(profile) > 16)
    assert len(high_profiles) == 56
    score_counts: Counter[Fraction] = Counter()
    cell_rows = []
    residual_variance = F(0)
    retained_variance = F(0)
    retained_mean = F(0)
    a_certificate = None
    high_profile_checks = 0

    for label, cell in sorted(cells.items()):
        states = cell["states"]
        histogram = cell["histogram"]
        count = sum(histogram.values())
        first = sum(value * mass for value, mass in histogram.items())
        second = sum(value * value * mass for value, mass in histogram.items())
        score = F(first, count)
        conditional_variance = F(second, count) - score * score
        probability = F(count, CUBE_SIZE)
        retained_mean += probability * score
        retained_variance += probability * score * score
        residual_variance += probability * conditional_variance
        score_counts[score] += count

        for profile in high_profiles:
            assert walsh_numerator(states, profile) == 0, (label, profile)
            high_profile_checks += 1
        if label[0] == "ordinary":
            # The selected leaf is the one omitted four-bit block.
            omitted_block = label[2] + 1
            degree_witness = tuple(0 if i == omitted_block else 4 for i in range(5))
        else:
            degree_witness = (0, 4, 4, 4, 4)
        degree_numerator = walsh_numerator(states, degree_witness)
        assert degree_numerator != 0, label
        assert sum(degree_witness) == 16

        if label[0] == "A":
            assert count == 8704
            assert probability == F(17, 2048)
            assert score == F(31, 17)
            assert conditional_variance == F(1147, 289)
            expected_histogram = {-2: 616, 0: 2368, 2: 3336, 4: 1984, 6: 376, 10: 24}
            assert dict(histogram) == expected_histogram
            alternating = [
                sum(
                    (-1) ** ((BITS - value) // 2)
                    * ((BITS - value) // 2) ** order
                    * mass
                    for value, mass in histogram.items()
                )
                for order in range(4)
            ]
            assert alternating == [0, 0, 0, 0]
            a_certificate = {
                "cube_points": count,
                "grouped_states": len(states),
                "probability": str(probability),
                "conditional_mean": str(score),
                "conditional_variance": str(conditional_variance),
                "conditional_law": [
                    {"H": value, "cube_points": mass, "probability": str(F(mass, count))}
                    for value, mass in sorted(histogram.items())
                ],
                "alternating_Y_moment_numerators_orders_0_to_3": alternating,
            }
        else:
            assert conditional_variance == BLOCK_SIZE

        cell_rows.append({
            "label": label,
            "cube_points": count,
            "grouped_states": len(states),
            "sum_H": first,
            "sum_H_squared": second,
            "score": str(score),
            "conditional_variance": str(conditional_variance),
            "exact_degree": 16,
            "degree_witness_profile": degree_witness,
            "degree_witness_coefficient_numerator": degree_numerator,
        })

    assert a_certificate is not None
    assert retained_mean == 0
    assert retained_variance == 16 + EXPECTED_GAP
    assert retained_variance + residual_variance == BITS
    assert high_profile_checks == 622 * 56
    # A second, closed-form description of the complete score law: start
    # with a sixteen-sign sum, then change just four atomic masses.
    expected_score_counts = Counter({F(2 * j - 16): 16 * comb(16, j) for j in range(17)})
    expected_score_counts[F(2)] -= 9856
    expected_score_counts[F(4)] += 1536
    expected_score_counts[F(6)] -= 384
    expected_score_counts[F(31, 17)] += 8704
    assert score_counts == expected_score_counts
    score_moments = {
        str(order): sum(F(count, CUBE_SIZE) * score**order for score, count in score_counts.items())
        for order in range(7)
    }
    assert score_moments["0"] == 1
    assert score_moments["1"] == 0
    assert score_moments["2"] == retained_variance
    assert score_moments["3"] == F(-6045, 591872)
    assert score_moments["4"] == F(7403910529, 10061824)
    assert score_moments["5"] == F(-253337745, 171051008)
    assert score_moments["6"] == F(157038253024705, 2907867136)
    assert score_moments["4"] / retained_variance**2 < 3
    assert sum(score_counts.values()) == CUBE_SIZE
    # The upper degree bound 16 follows because a readout is a linear
    # combination of the cell indicators already checked above.  One
    # nonzero coefficient establishes that the bound is attained.
    readout_profile = (4, 0, 4, 4, 4)
    readout_numerator = 0
    for cell in cells.values():
        histogram = cell["histogram"]
        first = sum(value * mass for value, mass in histogram.items())
        readout_sign = 1 if first >= 0 else -1  # sign(0) = +1
        readout_numerator += readout_sign * walsh_numerator(cell["states"], readout_profile)
    readout_coefficient = F(readout_numerator, CUBE_SIZE)
    assert readout_coefficient == F(165, 16384)
    assert all((score >= 0) == (1 + score > 0) for score in score_counts)
    absolute_first = sum(F(count, CUBE_SIZE) * abs(score) for score, count in score_counts.items())
    shifted_absolute_first = sum(F(count, CUBE_SIZE) * abs(1 + score) for score, count in score_counts.items())
    assert absolute_first == F(6435, 2048)
    assert shifted_absolute_first == F(109395, 32768)
    assert absolute_first**2 < 16
    assert shifted_absolute_first**2 < 17

    return {
        "description": "Exact twenty-bit Fourier-codimension-four observation certificate",
        "arithmetic": "integers and fractions.Fraction only",
        "bits": BITS,
        "block_size": BLOCK_SIZE,
        "blocks": BLOCK_COUNT,
        "cube_points": CUBE_SIZE,
        "grouped_states": grouped_states,
        "cell_count": len(cells),
        "cell_counts_by_tag": {"A": 1, "B": 1, "ordinary": 620},
        "leaf_values": LEAF_VALUES,
        "selector": [
            {"central_sum": value, "selected_leaf_index": index, "selected_leaf_target": LEAF_VALUES[index]}
            for value, index in zip(VALUES, SELECTOR)
        ],
        "degree_verification": {
            "method": "complete block-symmetric Walsh-profile enumeration",
            "profiles_above_degree_16": len(high_profiles),
            "zero_coefficient_checks": high_profile_checks,
            "every_cell_exact_degree": 16,
            "all_Walsh_coefficient_denominators": CUBE_SIZE,
        },
        "A": a_certificate,
        "retained_mean": str(retained_mean),
        "retained_variance": str(retained_variance),
        "residual_variance": str(residual_variance),
        "advantage_over_degree": str(EXPECTED_GAP),
        "reporter_objective": exact_reporter_objective(),
        "score_law": [
            {"score": str(score), "cube_points": count, "probability": str(F(count, CUBE_SIZE))}
            for score, count in sorted(score_counts.items())
        ],
        "score_law_identity": "Law(H_16) + (12 delta_4 - 77 delta_2 - 3 delta_6 + 68 delta_(31/17))/8192",
        "score_moments_orders_0_to_6": {order: str(value) for order, value in score_moments.items()},
        "score_fourth_moment_divided_by_variance_squared": str(score_moments["4"] / retained_variance**2),
        "sign_readouts": {
            "zero_convention": "sign(0)=+1",
            "sign_T_equals_sign_one_plus_T_pointwise": True,
            "original": {
                "definition": "f(x)=sign(T_F(x))",
                "exact_degree": 16,
                "degree_witness_profile_center_then_four_leaves": readout_profile,
                "degree_witness_coefficient": str(readout_coefficient),
                "signed_singleton_sum": str(absolute_first),
                "majority_benchmark": "B_16",
                "singleton_sum_squared_less_than_actual_degree": True,
            },
            "symmetrized": {
                "definition": "g(z,x)=sign(z*(1+T_F(z*x)))=z*f(z*x)",
                "exact_degree": 17,
                "degree_witness_profile_z_then_center_then_four_leaves": (1,) + readout_profile,
                "degree_witness_coefficient": str(readout_coefficient),
                "coefficient_reason": "an even degree-16 monomial of f becomes z times the same monomial",
                "signed_singleton_sum": str(shifted_absolute_first),
                "majority_benchmark": "B_17",
                "singleton_sum_squared_less_than_actual_degree": True,
            },
        },
        "cells": cell_rows,
        "all_assertions_passed": True,
    }


def main() -> None:
    default_output = Path(__file__).resolve().parent.parent / "data" / "witness_certificate.json"
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=default_output, help="JSON certificate destination")
    args = parser.parse_args()
    certificate = verify()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(certificate, indent=2) + "\n", encoding="utf-8")
    print("PASS: 3,125 grouped states represent all 1,048,576 sign strings.")
    print("PASS: 622 cells; every cell has exact Walsh degree 16.")
    print("PASS: 34,832 Walsh coefficients above degree 16 are zero.")
    print("PASS: retained variance = 16 + 9/34816.")
    print(f"Certificate: {args.output}")


if __name__ == "__main__":
    main()
