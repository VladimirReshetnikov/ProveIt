#!/usr/bin/env python3
"""Exact arithmetic checks for the ETH-false algorithm improvement audit.

This is NOT a SAT solver or a running-time benchmark. It checks finite
instances and algebraic identities used in the accompanying report. The
infinite sums below are evaluated by exact closed forms, not cut off.

No third-party Python packages are required. From the package root run:

    python3 code/verify_bounds.py

The default outputs are results/bounds_verification.json and
results/exponent_scales.csv. --out-dir selects another output directory.
"""

from __future__ import annotations

import argparse
import csv
import itertools
import json
import math
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path


def ceil_fraction(value: Fraction) -> int:
    return -((-value.numerator) // value.denominator)


def rational(value: int | Fraction) -> str:
    return str(Fraction(value))


def decimal(value: Fraction) -> str:
    with localcontext() as ctx:
        ctx.prec = 30
        return format(Decimal(value.numerator) / Decimal(value.denominator), "f")


def weighted_mass(q: tuple[int | Fraction, ...]) -> Fraction:
    return sum((Fraction(x, 2**i) for i, x in enumerate(q)), Fraction(0))


def infinite_losses(q: tuple[int | Fraction, ...]) -> tuple[Fraction, ...]:
    """A_i = sum_{j>=1} j*2^-j*(q_i-q_(i+j)), with q outside zero.

    The coefficient of q_i is the exact infinite sum sum j/2^j = 2.
    Only the subtracted terms stop at the end of the finite profile.
    """
    u = len(q)
    return tuple(
        2 * Fraction(q[i])
        - sum(
            (Fraction(j, 2**j) * q[i + j] for j in range(1, u - i)),
            Fraction(0),
        )
        for i in range(u)
    )


def finite_losses(q: tuple[int | Fraction, ...], a: int) -> tuple[Fraction, ...]:
    """The source's finite sum, through j=a-i, evaluated directly."""
    u = len(q)
    if a < u:
        raise ValueError("The grid exponent a must be at least u.")
    return tuple(
        sum(
            (
                Fraction(j, 2**j)
                * (q[i] - (q[i + j] if i + j < u else 0))
                for j in range(1, a - i + 1)
            ),
            Fraction(0),
        )
        for i in range(u)
    )


def tail(jmax: int) -> Fraction:
    """Exact sum_{j>jmax} j/2^j."""
    return Fraction(jmax + 2, 2**jmax)


def equal_loss_profile(u: int) -> tuple[Fraction, ...]:
    """Largest profile with every infinite loss <=1; backward recurrence."""
    q = [Fraction(0)] * u
    for i in range(u - 1, -1, -1):
        q[i] = Fraction(1, 2) + sum(
            (Fraction(j, 2 ** (j + 1)) * q[i + j] for j in range(1, u - i)),
            Fraction(0),
        )
    return tuple(q)


def equal_loss_closed_form(u: int) -> tuple[Fraction, ...]:
    return tuple(
        Fraction(u - 1 - i, 6)
        + Fraction(4, 9)
        + Fraction(1, 18 * 4 ** (u - 1 - i))
        for i in range(u)
    )


def equal_loss_mass(u: int) -> Fraction:
    return Fraction(u, 3) + Fraction(2, 9) * (1 - Fraction(1, 4**u))


def all_weighted_partitions(c: int, p: int) -> int:
    """Exact number of c-colored partitions with weight strictly below p.

    This counts the full *abstract budget set*, not actual nonzero tensor
    coefficients. For every weight j there are c independent variables.
    """
    dp = [0] * p
    dp[0] = 1
    for j in range(1, p):
        for _ in range(c):
            for total in range(j, p):
                dp[total] += dp[total - j]
    return sum(dp)


def binary_subset_histogram(weights: list[int]) -> list[int]:
    """Distribution of total weight among ALL binary subsets, exactly."""
    dp = [1]
    for weight in weights:
        old_length = len(dp)
        dp.extend([0] * weight)
        for total in range(old_length - 1, -1, -1):
            dp[total + weight] += dp[total]
    return dp


def verify_partition_witnesses() -> list[dict]:
    records = []
    # u=square_root_u^2, D=J*square_root_u, M=c*D.
    # Then p=MD/u=c*J^2 and c*J=M/sqrt(u).
    for square_root_u, J, c in [(2, 4, 2), (4, 4, 4), (8, 8, 8), (16, 16, 16)]:
        u = square_root_u**2
        D = J * square_root_u
        M = c * D
        p = Fraction(M * D, u)
        assert p.denominator == 1
        p = int(p)
        weights = [j for j in range(1, J + 1) for _ in range(c)]
        dimension = len(weights)
        maximum_weight = c * J * (J + 1) // 2
        assert maximum_weight < p
        assert dimension == M // square_root_u
        assert dimension <= M  # Also respects ordinary degree <= M.
        histogram = binary_subset_histogram(weights)
        assert len(histogram) - 1 == maximum_weight
        assert sum(histogram) == 2**dimension
        assert all(weight < p for weight, count in enumerate(histogram) if count)
        full_count = all_weighted_partitions(c, p) if p <= 256 else None
        if full_count is not None:
            assert full_count >= 2**dimension
        records.append(
            {
                "M": M,
                "D": D,
                "u": u,
                "sqrt_u": square_root_u,
                "colors_per_weight": c,
                "selected_weights": [1, J],
                "strict_budget_p": p,
                "maximum_weight_of_any_binary_subset": maximum_weight,
                "binary_dimensions": dimension,
                "certified_number_of_budget_feasible_tuples": str(2**dimension),
                "log2_certified_number": dimension,
                "also_respects_total_degree_at_most_M": True,
                "full_abstract_budget_count_if_computed": (
                    str(full_count) if full_count is not None else None
                ),
            }
        )
    return records


def verify_tapers() -> dict:
    qmax = 3
    counts = []
    total_profiles = 0
    finite_tail_checks = 0
    optimal_envelope_checks = 0
    for u in range(1, 7):
        r = equal_loss_profile(u)
        assert r == equal_loss_closed_form(u)
        assert weighted_mass(r) == equal_loss_mass(u)
        assert infinite_losses(r) == (Fraction(1),) * u
        count = 0
        least_ratio = None
        least_profile = None
        for raw in itertools.product(range(qmax + 1), repeat=u):
            q = tuple(raw)
            mass = weighted_mass(q)
            losses = infinite_losses(q)
            H = max(losses)
            expected_sum = sum(
                (Fraction(i + 2, 2**i) * q[i] for i in range(u)), Fraction(0)
            )
            assert sum(losses, Fraction(0)) == expected_sum
            assert H >= 2 * mass / u
            # The stronger exact extremal envelope follows by backward
            # induction; these small cases independently check all coordinates.
            assert all(Fraction(q[i]) <= H * r[i] for i in range(u))
            assert mass <= H * equal_loss_mass(u)
            optimal_envelope_checks += u
            if mass:
                ratio = H / mass
                if least_ratio is None or ratio < least_ratio:
                    least_ratio, least_profile = ratio, list(q)
            for a in sorted({u, u + 1, 2 * u}):
                finite = finite_losses(q, a)
                tails = tuple(Fraction(q[i]) * tail(a - i) for i in range(u))
                assert all(losses[i] == finite[i] + tails[i] for i in range(u))
                assert sum(finite, Fraction(0)) == expected_sum - sum(tails, Fraction(0))
                assert max(finite) >= (expected_sum - sum(tails, Fraction(0))) / u
                # A convenient finite-grid consequence with a >= 2u.
                if a >= 2 * u:
                    assert max(finite) >= mass / u
                finite_tail_checks += u
            count += 1
        total_profiles += count
        counts.append(
            {
                "u": u,
                "profiles_checked": count,
                "entries_from": [0, qmax],
                "continuous_optimal_mass_at_H_equal_1": rational(equal_loss_mass(u)),
                "continuous_optimal_H_over_mass": rational(1 / equal_loss_mass(u)),
                "small_integer_grid_minimum_H_over_mass": rational(least_ratio),
                "small_integer_grid_minimizer": least_profile,
            }
        )
    # Longer, fractional profiles check the closed form beyond the tiny grids.
    for u in (8, 16, 32, 64, 128):
        r = equal_loss_profile(u)
        assert r == equal_loss_closed_form(u)
        assert infinite_losses(r) == (Fraction(1),) * u
        assert weighted_mass(r) == equal_loss_mass(u)
    return {
        "exact_arithmetic": "fractions.Fraction; no floating-point comparisons",
        "total_profiles_checked": total_profiles,
        "finite_tail_coordinate_checks": finite_tail_checks,
        "continuous_optimal_envelope_coordinate_checks": optimal_envelope_checks,
        "identities": {
            "infinite_loss": "A_i = sum_{j>=1} j*2^(-j)*(q_i-q_(i+j)); q_i=0 outside 0<=i<u",
            "sum_identity": "sum_i A_i = sum_i (i+2)*2^(-i)*q_i",
            "average_lower_bound": "max_i A_i >= 2*sum_i 2^(-i)*q_i/u",
            "finite_tail": "A_i - A_i^(a) = q_i*(a-i+2)/2^(a-i)",
            "equal_loss_profile": "r_i=(u-1-i)/6+4/9+1/(18*4^(u-1-i))",
            "equal_loss_mass": "R_u=u/3+(2/9)*(1-4^(-u))",
            "linear_taper_loss": "For q_i=h*(u-i), A_i=h*(6-(u-i+3)*2^(1-(u-i)))",
            "optimal_envelope": "If max_i A_i<=H, then q_i<=H*r_i, hence weighted_mass<=H*R_u",
        },
        "exhaustive_grids": counts,
        "additional_equal_loss_profile_lengths_checked": [8, 16, 32, 64, 128],
    }


def profile_statistics(q: tuple[int, ...], M: int, u: int, a: int) -> dict:
    L = 2**a
    degree = M * (2 * L - 1)
    mass = weighted_mass(q)
    jet_count = L * mass
    assert jet_count.denominator == 1
    assert jet_count > degree
    assert all(x > 0 for x in q)
    infinite = infinite_losses(q)
    finite = finite_losses(q, a)
    precision_losses = []
    for i in range(u):
        # E_t(0) loses D_i*A_i^(a) powers of 2; evaluation of the
        # degree-(q_i-1) Taylor jet loses (q_i-1)*(a+1-i) more.
        exact = Fraction(L, 2**i) * finite[i] + (q[i] - 1) * (a + 1 - i)
        assert exact.denominator == 1
        precision_losses.append(int(exact))
    return {
        "q": list(q),
        "weighted_mass": rational(mass),
        "jet_count": str(int(jet_count)),
        "required_minimum_jet_count": str(degree + 1),
        "jet_excess": str(int(jet_count) - degree - 1),
        "max_infinite_normalized_loss": rational(max(infinite)),
        "max_infinite_normalized_loss_divided_by_M": rational(max(infinite) / M),
        "max_finite_normalized_loss": rational(max(finite)),
        "max_exact_recovery_precision_loss": str(max(precision_losses)),
        "completeness_verified": True,
    }


def verify_profile_choices() -> list[dict]:
    records = []
    M = 2**20
    for u in (1, 2, 4, 8, 16, 32, 64):
        a = 2 * u
        L = 2**a
        degree = M * (2 * L - 1)
        linear_mass_per_h = sum(
            (Fraction(u - i, 2**i) for i in range(u)), Fraction(0)
        )
        closed_mass = 2 * u - 2 + Fraction(1, 2 ** (u - 1))
        assert linear_mass_per_h == closed_mass
        h_source = math.ceil(Fraction(3 * M, u))
        h_min = ceil_fraction(Fraction(degree + 1, L) / linear_mass_per_h)
        assert h_min <= h_source
        assert L * h_min * linear_mass_per_h >= degree + 1
        assert L * (h_min - 1) * linear_mass_per_h < degree + 1
        q_source = tuple(h_source * (u - i) for i in range(u))
        q_linear = tuple(h_min * (u - i) for i in range(u))
        assert infinite_losses(q_linear) == tuple(
            h_min * (6 - Fraction(u - i + 3, 2 ** (u - i - 1)))
            for i in range(u)
        )
        assert max(q_linear) <= max(q_source) <= 4 * M
        required_mass = Fraction(degree + 1, L)
        r = equal_loss_profile(u)
        H_star = required_mass / equal_loss_mass(u)
        q_real = tuple(H_star * x for x in r)
        assert weighted_mass(q_real) == required_mass
        assert infinite_losses(q_real) == (H_star,) * u
        q_rounded = tuple(ceil_fraction(x) for x in q_real)
        assert max(infinite_losses(q_rounded)) <= H_star + 2
        assert weighted_mass(q_rounded) >= required_mass
        assert max(q_rounded) <= 2 * M
        flat_scale = ceil_fraction(required_mass / weighted_mass((1,) * u))
        q_flat = (flat_scale,) * u
        quadratic = tuple((u - i) ** 2 for i in range(u))
        quadratic_scale = ceil_fraction(required_mass / weighted_mass(quadratic))
        q_quadratic = tuple(quadratic_scale * x for x in quadratic)
        source_precision = 8 * h_source * L + 8 * M * (a + 1)
        linear_precision = 8 * h_min * L + 8 * M * (a + 1)
        linear_stats = profile_statistics(q_linear, M, u, a)
        exact_linear_precision = int(linear_stats["max_exact_recovery_precision_loss"])
        records.append(
            {
                "M": M,
                "u": u,
                "a": a,
                "L": str(L),
                "degree_R": str(degree),
                "linear_weighted_mass_per_unit_h": rational(linear_mass_per_h),
                "source_h": h_source,
                "minimum_complete_linear_h": h_min,
                "h_ratio_source_over_optimal_linear": rational(Fraction(h_source, h_min)),
                "source_8hD_plus_8M_a1_at_D_equal_L": str(source_precision),
                "optimized_linear_same_precision_formula_at_D_equal_L": str(linear_precision),
                "source_bound_over_max_exact_linear_recovery_loss": rational(
                    Fraction(source_precision, exact_linear_precision)
                ),
                "source_dominant_coefficient_of_M_D_over_u": rational(
                    Fraction(8 * h_source * u, M)
                ),
                "optimized_linear_infinite_loss_coefficient_of_M_D_over_u": rational(
                    max(infinite_losses(q_linear)) * u / M
                ),
                "continuous_optimal_infinite_loss": rational(H_star),
                "continuous_profile_is_not_an_integer_multiplicity_schedule": True,
                "profiles": {
                    "source_linear": profile_statistics(q_source, M, u, a),
                    "minimum_complete_linear": linear_stats,
                    "rounded_equal_loss": profile_statistics(q_rounded, M, u, a),
                    "flat": profile_statistics(q_flat, M, u, a),
                    "quadratic": profile_statistics(q_quadratic, M, u, a),
                },
            }
        )
    return records


def v2_integer(value: int) -> int:
    if value == 0:
        raise ValueError("v2(0) is not a finite integer")
    value = abs(value)
    return (value & -value).bit_length() - 1


def v2_fraction(value: Fraction) -> int:
    return v2_integer(value.numerator) - v2_integer(value.denominator)


def verify_hermite_products() -> list[dict]:
    """Independent rational-product checks of the exact recovery precision.

    This constructs E_t(0) from its product over actual grid points. It does
    not obtain the valuation from the grouped-by-valuation formula being
    tested. Small grids make this direct method feasible.
    """
    cases = []
    for a, u, M in [(2, 1, 4), (4, 2, 8), (6, 3, 16), (8, 4, 32)]:
        L = 2**a
        alpha = 2 * L
        p = M + 1
        degree = M * (2 * L - 1)
        mass_per_h = sum((Fraction(u - i, 2**i) for i in range(u)), Fraction(0))
        h = ceil_fraction(Fraction(degree + 1, L) / mass_per_h)
        h_old = ceil_fraction(Fraction(3 * M, u))
        q = tuple(h * (u - i) for i in range(u))
        q_old = tuple(h_old * (u - i) for i in range(u))
        assert max(q) <= max(q_old) <= 4 * M
        assert L * weighted_mass(q) > degree
        grouped_losses = finite_losses(q, a)
        grid = range(-L, L)
        if a <= 4:
            nodes = [t for t in grid if t and v2_integer(t) < u]
        else:
            nodes = sorted({-2**i for i in range(u)} | {2**i for i in range(u)} | {3, 7})
        rows = []
        for t in nodes:
            i = v2_integer(t)
            if i >= u:
                continue
            E = Fraction(1)
            for point in grid:
                if point in (0, t):
                    continue
                v = v2_integer(point)
                multiplicity = q[v] if v < u else 0
                if multiplicity:
                    E *= Fraction(-point, t - point) ** multiplicity
                    # Each factor of E_t(t+alpha*z) is a power of
                    # 1+alpha*z/(t-point), whose nonconstant coefficient
                    # is two-adically integral. Its reciprocal is integral.
                    assert v2_fraction(Fraction(alpha, t - point)) >= 1
            actual_loss = -v2_fraction(E)
            D = L // 2**i
            formula_loss = D * grouped_losses[i]
            assert formula_loss.denominator == 1
            assert actual_loss == formula_loss
            new_p = p + actual_loss + (q[i] - 1) * (a + 1 - i)
            old_p = p + 8 * h_old * D + 8 * M * (a + 1)
            assert new_p <= old_p
            # Independently calculate each rational Hermite multiplier.
            # Perturbing any quotient coefficient by 2^new_p changes the
            # recovered answer by a multiple of 2^p, exactly at the last jet.
            error_valuations = []
            for j in range(q[i]):
                multiplier = E * Fraction(-t, alpha) ** j
                error_valuation = new_p + v2_fraction(multiplier)
                assert error_valuation >= p
                error_valuations.append(error_valuation)
            assert min(error_valuations) == p
            rows.append(
                {
                    "t": t,
                    "i_v2_t": i,
                    "D": D,
                    "q_i": q[i],
                    "negative_v2_E_t_0_direct_product": actual_loss,
                    "B_t_grouped_formula": int(formula_loss),
                    "new_precision_p_plus_B_plus_evaluation_loss": new_p,
                    "source_precision_p_plus_8h_oldD_plus_8M_a1": old_p,
                    "source_over_new_precision_ratio": rational(Fraction(old_p, new_p)),
                    "minimum_valuation_of_all_recovery_error_terms": min(error_valuations),
                    "E_t_0_numerator_bits": abs(E.numerator).bit_length(),
                    "E_t_0_denominator_bits": E.denominator.bit_length(),
                }
            )
        cases.append(
            {
                "a": a,
                "u": u,
                "M": M,
                "L": L,
                "p_input": p,
                "h_min": h,
                "h_source": h_old,
                "q_max": max(q),
                "q_max_bound_4M": 4 * M,
                "interpolation_degree_R": degree,
                "total_jets": int(L * weighted_mass(q)),
                "nodes_checked": len(rows),
                "all_retained_grid_nodes_checked": a <= 4,
                "checks": rows,
            }
        )
    return cases


def exponent_rows() -> list[dict]:
    rows = []
    for lam in (16, 64, 256, 1024, 4096, 16384):
        sqrt_lam = math.isqrt(lam)
        assert sqrt_lam**2 == lam
        nu = (lam - 1).bit_length()  # ceil(log2(lambda))
        quantities = {
            "manuscript_general_proxy": Fraction(nu, sqrt_lam),
            "manuscript_fixed_density_proxy": Fraction(1, sqrt_lam),
            "formalized_general_proxy": Fraction(nu * nu, sqrt_lam),
            "conditional_target_proxy": Fraction(nu, lam),
        }
        row = {"lambda_log2_n": lam, "nu_ceil_log2_lambda": nu}
        for label, value in quantities.items():
            row[label + "_exponent_divided_by_n_exact"] = rational(value)
            row[label + "_exponent_divided_by_n_decimal"] = decimal(value)
        row["conditional_over_manuscript_general_exact"] = rational(Fraction(1, sqrt_lam))
        row["interpretation"] = "Normalized asymptotic scales only; hidden constants omitted; not a timing benchmark."
        rows.append(row)
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out-dir", type=Path,
        default=Path(__file__).resolve().parents[1] / "results",
        help="Directory for the verification JSON and exponent-scale CSV.",
    )
    args = parser.parse_args()
    partitions = verify_partition_witnesses()
    tapers = verify_tapers()
    profiles = verify_profile_choices()
    hermite_products = verify_hermite_products()
    scales = exponent_rows()
    result = {
        "status": "all exact-arithmetic checks passed",
        "purpose": "Independent finite checks and exact identities, not a SAT implementation or speed benchmark.",
        "source_snapshot": "openai/math@42907c9e999cc00d6abe7a50bfc1023250edd1b9",
        "claims_not_made": [
            "No improved asymptotic SAT exponent has been established by this script.",
            "Budget-set lower bounds do not prove that all enumerated tensor coefficients are nonzero.",
            "The continuous optimal taper is not an integer schedule until rounded; rounding is checked separately.",
            "Finite arithmetic checks supplement proofs and do not replace formal proof checking.",
        ],
        "partition_budget_witnesses": partitions,
        "taper_functional": tapers,
        "complete_integer_taper_profiles": profiles,
        "direct_rational_hermite_product_checks": hermite_products,
        "exponent_scale_notes": {
            "lambda": "log2(n), evaluated symbolically so n need not be constructed",
            "nu": "ceil(log2(lambda))",
            "baseline": "n*nu/sqrt(lambda)",
            "conditional_target": "n*nu/lambda; explicitly conditional, not an achieved algorithm",
            "csv": "exponent_scales.csv",
        },
    }
    args.out_dir.mkdir(parents=True, exist_ok=True)
    json_path = args.out_dir / "bounds_verification.json"
    json_path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    csv_path = args.out_dir / "exponent_scales.csv"
    with csv_path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(scales[0]))
        writer.writeheader()
        writer.writerows(scales)
    print(json.dumps({
        "status": result["status"],
        "exhaustive_taper_profiles": tapers["total_profiles_checked"],
        "partition_witnesses": len(partitions),
        "integer_profile_parameter_sets": len(profiles),
        "outputs": [str(json_path), str(csv_path)],
    }, indent=2))


if __name__ == "__main__":
    main()
