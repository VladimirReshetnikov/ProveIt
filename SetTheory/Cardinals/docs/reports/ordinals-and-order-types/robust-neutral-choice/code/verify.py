#!/usr/bin/env python3
"""Exact finite checks for self-dual neutral choices and robust majorities.

Python 3.10+; standard library only.  There is no sampling or random input.
Run ``python3 code/verify.py`` from the package directory, or invoke this file
by its absolute path.  Outputs go to the neighboring ``data`` directory.

The exhaustive part covers all self-dual Boolean maps in dimensions 1--5.
It checks the sharp robustness envelope and conditional-bias bounds.
These finite computations support, but do not replace, the mathematical
proofs in the accompanying article.
"""

from __future__ import annotations

import argparse
import csv
import json
from decimal import Decimal, localcontext
from fractions import Fraction
from math import comb
from pathlib import Path


def rational_text(value: Fraction) -> str:
    """Return an exact rational string without an unnecessary denominator 1."""
    return str(value)


def decimal_text(value: Fraction, places: int = 12) -> str:
    """A display value only; never used to accept or reject a check."""
    with localcontext() as context:
        context.prec = max(places + 10, 50)
        number = Decimal(value.numerator) / Decimal(value.denominator)
        return f"{number:.{places}g}"


def optimum(n: int, r: int) -> Fraction:
    """Claimed exact optimum P(R_f > r), for integer r >= 0."""
    if n < 1 or r < 0:
        raise ValueError("Require n >= 1 and r >= 0")
    d = n if n % 2 else n - 1
    top = (d - 1) // 2 - r
    return Fraction(2 * sum(comb(d, j) for j in range(top + 1)), 1 << d)


class Cube:
    """The n-cube, with subsets represented by Python integer bitsets.

    Bit x represents vertex x.  Coordinate j is bit j of the vertex number.
    ``erode(A)`` keeps x exactly when x and every Hamming neighbor lie in A.
    Therefore r successive erosions of each sign class give {R_f > r}.
    """

    def __init__(self, n: int) -> None:
        self.n = n
        self.size = 1 << n
        self.full = (1 << self.size) - 1
        self.swaps: list[tuple[int, int, int]] = []
        for j in range(n):
            shift = 1 << j
            low = sum(1 << x for x in range(self.size) if not x & shift)
            self.swaps.append((shift, low, self.full ^ low))
        self.prefix_masks = [
            [
                sum(1 << x for x in range(prefix, self.size, 1 << m))
                for prefix in range(1 << m)
            ]
            for m in range(n + 1)
        ]

    def erode(self, subset: int) -> int:
        answer = subset
        for shift, low, high in self.swaps:
            neighbor_set = ((subset & low) << shift) | ((subset & high) >> shift)
            answer &= neighbor_set
        return answer

    def survival_counts(self, positive: int) -> list[int]:
        plus = positive
        minus = self.full ^ positive
        counts = [self.size]
        for _ in range(self.n):
            plus = self.erode(plus)
            minus = self.erode(minus)
            counts.append(plus.bit_count() + minus.bit_count())
        return counts

    def max_prefix_sum(self, positive: int, m: int) -> int:
        """max_y |sum_z f(y,z)|; divide by 2^(n-m) for conditional bias."""
        subcube_size = 1 << (self.n - m)
        return max(
            abs(2 * (positive & mask).bit_count() - subcube_size)
            for mask in self.prefix_masks[m]
        )


def self_dual_positive_sets(n: int):
    """Yield every self-dual map exactly once, encoded by its positive set.

    Choose arbitrary signs at vertices whose top coordinate is zero.  Every
    remaining sign is forced by f(complement x) = -f(x).  Reversing the lower
    half of the sign bitset implements complementing all vertex coordinates.
    """
    half = 1 << (n - 1)
    assignments = 1 << half
    lower_full = assignments - 1
    reversed_bits = [0] * assignments
    for value in range(1, assignments):
        reversed_bits[value] = (
            (reversed_bits[value >> 1] >> 1) | ((value & 1) << (half - 1))
        )
    for assignment in range(assignments):
        yield assignment | (reversed_bits[lower_full ^ assignment] << half)


def direct_survival_counts(cube: Cube, positive: int) -> list[int]:
    """Independent slow audit using minimum Hamming distances directly."""
    signs = [bool(positive & (1 << x)) for x in range(cube.size)]
    assert all(signs[x] != signs[(cube.size - 1) ^ x] for x in range(cube.size))
    radii = [
        min((x ^ y).bit_count() for y in range(cube.size) if signs[x] != signs[y])
        for x in range(cube.size)
    ]
    return [sum(radius > r for radius in radii) for r in range(cube.n + 1)]


def verify_dimension(n: int) -> dict:
    cube = Cube(n)
    expected = [optimum(n, r) * cube.size for r in range(n + 1)]
    assert all(count.denominator == 1 for count in expected)
    expected_counts = [count.numerator for count in expected]
    maxima = [-1] * (n + 1)
    maximizer_counts = [0] * (n + 1)
    prefix_equalities = [0] * (n + 1)
    boundary_equalities = {
        (m, r): 0 for m in range(1, n + 1) for r in range(1, m + 1)
    }
    prefix_ball_volumes = {
        (m, r): sum(comb(m, j) for j in range(r + 1))
        for m in range(1, n + 1) for r in range(1, m + 1)
    }
    observed_maps = 0
    for positive in self_dual_positive_sets(n):
        observed_maps += 1
        assert positive.bit_count() == cube.size // 2
        survival = cube.survival_counts(positive)
        if n <= 4:
            assert survival == direct_survival_counts(cube, positive)
        assert all(a >= b for a, b in zip(survival, survival[1:]))
        assert survival[-1] == 0
        for r, count in enumerate(survival):
            if count > maxima[r]:
                maxima[r] = count
                maximizer_counts[r] = 1
            elif count == maxima[r]:
                maximizer_counts[r] += 1

        for m in range(n + 1):
            largest_sum = cube.max_prefix_sum(positive, m)
            boundary_m = cube.size - survival[m]
            # alpha_m <= P(R <= m), with common denominator 2^n.
            left = largest_sum * (1 << m)
            if left > boundary_m:
                raise AssertionError(("prefix robustness", n, positive, m))
            prefix_equalities[m] += int(left == boundary_m)
            for r in range(1, m + 1):
                # alpha_m <= (2^m / V(m,r)) P(R <= r),
                # where V(m,r) = sum_{j=0}^r binomial(m,j).
                # Cancel the common subcube denominator exactly.
                left_sharp = largest_sum * prefix_ball_volumes[m, r]
                boundary_r = cube.size - survival[r]
                if left_sharp > boundary_r:
                    raise AssertionError(("prefix boundary", n, positive, m, r))
                boundary_equalities[m, r] += int(left_sharp == boundary_r)

    assert observed_maps == 1 << (1 << (n - 1))
    assert maxima == expected_counts, (n, maxima, expected_counts)

    # An explicit majority on d coordinates must attain every budget at once.
    d = n if n % 2 else n - 1
    majority_positive = sum(
        1 << x
        for x in range(cube.size)
        if (x & ((1 << d) - 1)).bit_count() > d // 2
    )
    majority_counts = cube.survival_counts(majority_positive)
    assert majority_counts == maxima

    return {
        "dimension": n,
        "vertices": cube.size,
        "self_dual_maps": observed_maps,
        "independent_direct_hamming_audit_maps": observed_maps if n <= 4 else 0,
        "robustness_budgets_checked": list(range(n + 1)),
        "maximum_surviving_vertex_counts": maxima,
        "optimum_fractions": [rational_text(optimum(n, r)) for r in range(n + 1)],
        "number_of_maximizers_by_budget": maximizer_counts,
        "majority_active_coordinates": d,
        "majority_surviving_vertex_counts": majority_counts,
        "prefix_robustness_checks": observed_maps * (n + 1),
        "prefix_boundary_checks": observed_maps * n * (n + 1) // 2,
        "prefix_one_step_boundary_checks_included": observed_maps * n,
        "individual_prefix_assignments_examined": observed_maps * ((1 << (n + 1)) - 1),
        "prefix_robustness_equality_counts_by_m": prefix_equalities,
        "prefix_boundary_equality_counts_by_m_and_r": {
            str(m): {str(r): boundary_equalities[m, r] for r in range(1, m + 1)}
            for m in range(1, n + 1)
        },
        "status": "PASS",
    }


def table_rows() -> list[dict]:
    budgets = {
        3: [0, 1, 2],
        5: [0, 1, 2, 3],
        9: [0, 1, 2, 3, 4, 5],
        25: [0, 1, 2, 3, 5, 8, 12, 13],
        101: [0, 1, 2, 5, 10, 15, 25, 50, 51],
    }
    result = []
    for n, chosen in budgets.items():
        d = n if n % 2 else n - 1
        for r in chosen:
            rho = optimum(n, r)
            surviving = rho * (1 << n)
            assert surviving.denominator == 1
            result.append({
                "n": n,
                "d": d,
                "r": r,
                "surviving_vertices": surviving.numerator,
                "total_vertices": 1 << n,
                "rho_exact": rational_text(rho),
                "rho_decimal": decimal_text(rho),
                "epsilon_exact": rational_text(1 - rho),
                "epsilon_decimal": decimal_text(1 - rho),
            })
    return result


def latex_fraction(value: str) -> str:
    if "/" not in value:
        return value
    numerator, denominator = value.split("/")
    return rf"\frac{{{numerator}}}{{{denominator}}}"


def latex_decimal(value: str) -> str:
    if "e" not in value.lower():
        return value
    mantissa, exponent = value.lower().split("e")
    return rf"{mantissa}\times 10^{{{int(exponent)}}}"


def write_outputs(output_dir: Path, reports: list[dict], rows: list[dict]) -> str:
    output_dir.mkdir(parents=True, exist_ok=True)
    total_maps = sum(report["self_dual_maps"] for report in reports)
    total_robustness_checks = sum(report["prefix_robustness_checks"] for report in reports)
    total_boundary_checks = sum(report["prefix_boundary_checks"] for report in reports)
    report = {
        "title": "Exact finite verification of robust self-dual choices",
        "method": "Exhaustive enumeration; integer bitsets; exact rational comparisons",
        "sampling": False,
        "formal_proof": False,
        "assumptions": {
            "domain": "{0,1}^n with uniform measure",
            "self_duality": "f(complement(x)) = -f(x)",
            "robustness": "R_f(x) is the minimum Hamming distance to a vertex with opposite output",
            "tail_convention": "rho_f(r) = P(R_f > r), for integer r >= 0",
            "prefix": "coordinates 0 through m-1; all 2^m assignments examined",
        },
        "claims_checked": [
            "max_f rho_f(r) = 2^(1-d) sum_{j=0}^{(d-1)/2-r} binomial(d,j), d=n if odd else n-1",
            "majority on d coordinates attains every robustness budget simultaneously",
            "alpha_m = ||E[f | first m coordinates]||_infinity <= P(R_f <= m)",
            "alpha_m <= (2^m/V(m,r)) P(R_f <= r), 1 <= r <= m <= n; V(m,r)=sum_{j=0}^r binomial(m,j)",
        ],
        "total_self_dual_maps_checked": total_maps,
        "total_independent_direct_hamming_audit_maps": sum(
            item["independent_direct_hamming_audit_maps"] for item in reports
        ),
        "total_prefix_robustness_checks": total_robustness_checks,
        "total_prefix_boundary_checks": total_boundary_checks,
        "dimensions": reports,
        "majority_table_note": (
            "Dimensions above the enumeration limit are evaluations of the exact "
            "majority formula, not exhaustive checks of all Boolean maps."
        ),
        "majority_table": rows,
        "status": "PASS",
    }
    (output_dir / "exact_verification.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8"
    )
    with (output_dir / "majority_table.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)

    # Compact table for direct inclusion in LaTeX. Exact values for n=101
    # remain in CSV/JSON so that long numerators do not overflow a page.
    tex_lines = [
        "% Generated by code/verify.py; exact rational arithmetic.",
        r"\begin{tabular}{rrrr}",
        r"\hline",
        r"$n$ & $r$ & $\rho_n^*(r)$ (exact) & Decimal \\",
        r"\hline",
    ]
    for row in rows:
        if row["n"] <= 25:
            exact = latex_fraction(row["rho_exact"])
            approximate = latex_decimal(row["rho_decimal"])
            tex_lines.append(
                f"{row['n']} & {row['r']} & ${exact}$ & ${approximate}$ " + r"\\"
            )
    tex_lines.extend([r"\hline", r"\end{tabular}"])
    (output_dir / "majority_table.tex").write_text("\n".join(tex_lines) + "\n", encoding="utf-8")

    log_lines = [
        "Exact finite verification of robust self-dual choices",
        "Method: complete enumeration, integer bitsets, exact comparisons.",
        "No random sampling. Display decimals are not used for checks.",
        "",
    ]
    for item in reports:
        log_lines.append(
            f"n={item['dimension']}: {item['self_dual_maps']:,} maps; "
            f"max surviving counts {item['maximum_surviving_vertex_counts']}; PASS"
        )
        log_lines.append(
            f"  rho* = {', '.join(item['optimum_fractions'])}; "
            f"majority on {item['majority_active_coordinates']} coordinates attains all budgets"
        )
        log_lines.append(
            f"  prefix robustness checks: {item['prefix_robustness_checks']:,}; "
            f"general prefix boundary checks: {item['prefix_boundary_checks']:,}; PASS"
        )
    log_lines.extend([
        "",
        f"TOTAL: {total_maps:,} self-dual maps checked.",
        "AUDIT: bitset tails agree with direct minimum Hamming distances "
        f"for all maps through dimension {min(4, max(item['dimension'] for item in reports))}.",
        f"TOTAL: {total_robustness_checks:,} prefix robustness inequalities checked.",
        f"TOTAL: {total_boundary_checks:,} general prefix boundary inequalities checked.",
        "",
        "Exact majority formula evaluations (larger n are not exhaustive):",
        "n, r, rho_exact, rho_decimal",
    ])
    log_lines.extend(
        f"{row['n']}, {row['r']}, {row['rho_exact']}, {row['rho_decimal']}"
        for row in rows
    )
    log_lines.extend(["", "OVERALL STATUS: PASS", ""])
    output = "\n".join(log_lines)
    (output_dir / "verification_run.txt").write_text(output, encoding="utf-8")
    return output


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--max-n", type=int, choices=range(1, 6), default=5,
        help="maximum exhaustive dimension (1--5; default: 5)",
    )
    parser.add_argument(
        "--output-dir", type=Path,
        default=Path(__file__).resolve().parent.parent / "data",
        help="directory for JSON, CSV, LaTeX table, and run transcript",
    )
    args = parser.parse_args()
    reports = [verify_dimension(n) for n in range(1, args.max_n + 1)]
    print(write_outputs(args.output_dir, reports, table_rows()), end="")


if __name__ == "__main__":
    main()
