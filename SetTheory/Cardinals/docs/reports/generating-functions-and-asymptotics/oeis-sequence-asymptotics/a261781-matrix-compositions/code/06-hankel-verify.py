#!/usr/bin/env python3
"""Reproduce the exact and numerical diagnostics in the matrix-composition article.

Run: python3 code/verify.py
Dependencies: Python 3.10+, mpmath, SymPy. No network access is used.

Exact integer checks and numerical diagnostics are deliberately separate. The
numerical tables are not proofs. Coupon probability brackets incorporate the
analytic Bonferroni and pole-replacement bounds; their decimal endpoints use
high-precision floating evaluation, not formally certified directed rounding.
"""

from __future__ import annotations

import argparse
import csv
import json
from math import comb, factorial, gcd
from pathlib import Path
import platform
import time

import mpmath as mp
import sympy as sp


OEIS_ROWS = [
    [1],
    [0, 1],
    [0, 2, 3],
    [0, 4, 16, 13],
    [0, 8, 66, 132, 75],
    [0, 16, 248, 924, 1232, 541],
    [0, 32, 892, 5546, 13064, 13060, 4683],
    [0, 64, 3136, 30720, 114032, 195020, 155928, 47293],
    [0, 128, 10888, 162396, 893490, 2327960, 3116220, 2075948, 545835],
]


def unrestricted_by_compositions(nmax: int, kmax: int) -> list[list[int]]:
    """A[k][n]: ordered lists of nonzero columns of height k, total sum n.

    A nonzero column of sum m has binom(k+m-1,m) possibilities. This
    construction is independent of the Stirling-number computation below.
    """
    columns = [[1] + [0] * nmax]
    for k in range(1, kmax + 1):
        column_counts = [0] + [comb(k + m - 1, m) for m in range(1, nmax + 1)]
        column = [1]
        for n in range(1, nmax + 1):
            column.append(sum(column_counts[m] * column[n - m]
                              for m in range(1, n + 1)))
        columns.append(column)
    return columns


def remove_empty_rows(columns: list[list[int]]) -> list[list[int]]:
    """Binomial inversion: T(n,k)=sum_j (-1)^(k-j) binom(k,j) A(n,j)."""
    nmax = len(columns[0]) - 1
    return [[sum((-1) ** (k - j) * comb(k, j) * columns[j][n]
                 for j in range(k + 1))
             for n in range(nmax + 1)]
            for k in range(len(columns))]


class StirlingData:
    """Unsigned first-kind and second-kind Stirling numbers, and Fubini numbers."""

    def __init__(self, nmax: int):
        self.first = [[1]]
        self.second = [[1]]
        self.factorials = [factorial(n) for n in range(nmax + 1)]
        self.fubini = [1]
        for n in range(1, nmax + 1):
            old_first = self.first[-1]
            old_second = self.second[-1]
            first = [0] * (n + 1)
            second = [0] * (n + 1)
            for q in range(1, n + 1):
                first[q] = old_first[q - 1]
                second[q] = old_second[q - 1]
                if q < n:
                    first[q] += (n - 1) * old_first[q]
                    second[q] += q * old_second[q]
            self.first.append(first)
            self.second.append(second)
            self.fubini.append(sum(self.factorials[q] * second[q]
                                   for q in range(n + 1)))

    def unrestricted(self, n: int, k: int) -> int:
        numerator = sum(self.first[n][q] * k ** q * self.fubini[q]
                        for q in range(n + 1))
        result, remainder = divmod(numerator, self.factorials[n])
        assert remainder == 0, ("nonintegral A", n, k)
        return result

    def packed(self, n: int, k: int) -> int:
        if k > n:
            return 0
        numerator = self.factorials[k] * sum(
            self.first[n][q] * self.second[q][k] * self.fubini[q]
            for q in range(k, n + 1))
        result, remainder = divmod(numerator, self.factorials[n])
        assert remainder == 0, ("nonintegral T", n, k)
        return result


def text_number(value, digits: int = 35) -> str:
    return mp.nstr(value, digits)


def write_json(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def check_recurrences(packed: list[list[int]]) -> list[dict]:
    """Integer polynomial identities, gcds, and independent coefficient checks."""
    z = sp.Symbol("z")
    records = []
    for k in range(1, 11):
        factors = [sp.Poly(2 * (1 - z) ** j - 1, z, domain=sp.ZZ)
                   for j in range(1, k + 1)]
        denominator = sp.Poly(1, z, domain=sp.ZZ)
        for factor in factors:
            denominator *= factor
        numerator = (-1) ** k * denominator  # j=0 contributes A_0(z)=1.
        for j, factor in enumerate(factors, start=1):
            quotient, remainder = sp.div(denominator, factor)
            assert remainder.is_zero
            numerator += ((-1) ** (k - j) * comb(k, j)
                          * sp.Poly((1 - z) ** j, z) * quotient)
        degree = k * (k + 1) // 2
        assert denominator.degree() == numerator.degree() == degree
        assert sp.gcd(numerator, denominator).degree() == 0
        coefficients = [int(denominator.nth(i)) for i in range(degree + 1)]
        assert coefficients[0] == 1
        for n in range(len(packed[k])):
            convolution = sum(coefficients[i] * packed[k][n - i]
                              for i in range(min(degree, n) + 1))
            assert convolution == int(numerator.nth(n)), ("recurrence", k, n)
        impulse = int(numerator.nth(degree))
        predicted_impulse = 2 ** (k - 1) * (-1) ** (k + degree)
        assert impulse == predicted_impulse != 0
        records.append({
            "k": k,
            "degree": degree,
            "denominator_coefficients_ascending": coefficients,
            "numerator_coefficients_ascending": [int(numerator.nth(i))
                                                 for i in range(degree + 1)],
            "gcd_degree": 0,
            "first_homogeneous_recurrence_index": degree + 1,
            "last_checked_index": len(packed[k]) - 1,
            "inhomogeneous_impulse_at_degree": impulse,
        })
    return records


def check_hankel(packed: list[list[int]]) -> list[dict]:
    records = []
    for k in range(1, 6):
        degree = k * (k + 1) // 2
        base = 2 ** (2 * comb(k + 1, 3))
        for j in range(1, k + 1):
            base *= comb(k, j) ** j
        for i in range(1, k + 1):
            for j in range(i + 1, k + 1):
                common = gcd(i, j)
                base *= (2 ** ((j - i) // common) - 1) ** (2 * common)
        for shift in (1, 2, 3):
            matrix = sp.Matrix(degree, degree,
                               lambda p, q: packed[k][shift + p + q])
            determinant = int(matrix.det(method="domain-ge"))
            prediction = base * 2 ** (k * (shift - 1))
            assert determinant == prediction, ("Hankel", k, shift)
            records.append({"k": k, "shift": shift, "rank": degree,
                            "determinant": str(determinant)})
        if k <= 4:
            matrix = sp.Matrix(degree + 1, degree + 1,
                               lambda p, q: packed[k][1 + p + q])
            assert matrix.det(method="domain-ge") == 0
    return records


def check_initial_hankel(packed: list[list[int]], tail_records: list[dict]) -> list[dict]:
    """The isolated n=0 impulse raises the full Hankel rank by one."""
    records = []
    for k in range(1, 5):
        degree = k * (k + 1) // 2
        tail = next(int(row["determinant"]) for row in tail_records
                    if row["k"] == k and row["shift"] == 2)
        prediction, remainder = divmod((-1) ** k * tail, 2)
        assert remainder == 0
        matrix = sp.Matrix(degree + 1, degree + 1,
                           lambda p, q: packed[k][p + q])
        determinant = int(matrix.det(method="domain-ge"))
        assert determinant == prediction != 0
        records.append({"k": k, "matrix_size": degree + 1,
                        "determinant": str(determinant),
                        "formula": "(-1)^k H(k,2)/2"})
    return records


def check_weighted_hankel() -> list[dict]:
    """Check the polynomial identity independently with one variable per column."""
    u = sp.Symbol("u")
    nmax = 11
    columns = [[sp.Poly(1, u)] + [sp.Poly(0, u)] * nmax]
    for k in range(1, 4):
        column = [sp.Poly(1, u)]
        for n in range(1, nmax + 1):
            column.append(sp.Poly(u, u) * sum(
                (comb(k + m - 1, m) * column[n - m]
                 for m in range(1, n + 1)), sp.Poly(0, u)))
        columns.append(column)
    packed = [[sum(((-1) ** (k - j) * comb(k, j) * columns[j][n]
                    for j in range(k + 1)), sp.Poly(0, u))
               for n in range(nmax + 1)] for k in range(4)]
    records = []
    for k, shift in ((1, 1), (1, 2), (2, 1), (2, 2), (3, 1)):
        degree = k * (k + 1) // 2
        cubic = comb(k + 1, 3)
        prediction = (u ** (degree + 2 * cubic)
                      * (1 + u) ** (k * (shift - 1) + 2 * cubic))
        for j in range(1, k + 1):
            prediction *= comb(k, j) ** j
        for i in range(1, k + 1):
            for j in range(i + 1, k + 1):
                common = gcd(i, j)
                exponent = (j - i) // common
                prediction *= ((1 + u) ** exponent - u ** exponent) ** (2 * common)
        matrix = sp.Matrix(degree, degree,
                           lambda p, q: packed[k][shift + p + q].as_expr())
        determinant = matrix.det(method="domain-ge")
        assert sp.Poly(determinant - prediction, u).is_zero, ("weighted Hankel", k, shift)
        records.append({"k": k, "shift": shift, "rank": degree,
                        "factored_determinant": str(sp.factor(prediction))})
    return records


def pole_constants(k: int):
    logarithm = mp.log(2)
    root = mp.exp(-logarithm / k)
    radius = -mp.expm1(-logarithm / k)
    residue = root / (2 * k * radius)
    return radius, residue


def pole_error_bound(n: int):
    logarithm = mp.log(2)
    rho = (1 + 8 / logarithm ** 2) ** (-mp.mpf(1) / 2)
    return mp.pi ** 2 * logarithm ** 2 / 24 * rho ** (n - 1)


def check_pole_bounds(columns: list[list[int]]) -> list[dict]:
    records = []
    for k in (1, 2, 3, 5, 10):
        radius, residue = pole_constants(k)
        for n in (1, 2, 5, 10, 20, 40):
            relative_error = mp.mpf(columns[k][n]) * radius ** n / residue - 1
            bound = pole_error_bound(n)
            assert abs(relative_error) <= bound
            records.append({
                "k": k, "n": n,
                "relative_error": text_number(relative_error),
                "analytic_absolute_bound": text_number(bound),
                "observed_error_divided_by_bound": text_number(abs(relative_error) / bound),
            })
    return records


def coupon_probability(n: int, k: int) -> dict:
    """Bonferroni bounds with an explicit uniform dominant-pole error budget.

    For j>=1 let m_j^*=binom(k,j)c_(k-j)/c_k(r_k/r_(k-j))^n.
    If |epsilon_q|<=E, the true binomial moment differs from m_j^*
    by at most 2E/(1-E)*m_j^*. Odd/even partial sums then bound the
    no-empty-row probability. At j=k all remaining moments vanish.
    """
    radius_k, residue_k = pole_constants(k)
    error = pole_error_bound(n)
    assert error < 1
    moment_error_factor = 2 * error / (1 - error)
    partial = mp.mpf(1)
    error_budget = mp.mpf(0)
    lower, upper = mp.mpf(0), mp.mpf(1)
    last_term = mp.mpf(1)
    for j in range(1, k + 1):
        if j == k:
            moment = mp.mpf(0)
        else:
            radius, residue = pole_constants(k - j)
            moment = (comb(k, j) * residue / residue_k
                      * mp.exp(n * mp.log(radius_k / radius)))
        partial += (-1) ** j * moment
        error_budget += moment_error_factor * moment
        if j % 2:
            lower = max(lower, partial - error_budget)
        else:
            upper = min(upper, partial + error_budget)
        if j == k:
            lower = max(lower, partial - error_budget)
            upper = min(upper, partial + error_budget)
        last_term = moment
        if j >= 2 and (j == k or moment < mp.mpf("1e-70")):
            break
    assert 0 <= lower <= upper <= 1, (n, k, lower, upper)
    return {"lower": lower, "upper": upper,
            "midpoint": (lower + upper) / 2,
            "width": upper - lower,
            "moments_used": j,
            "last_moment": last_term,
            "pole_error_budget": error_budget}


def coupon_table(stirling: StirlingData) -> tuple[list[dict], int]:
    records = []
    exact_comparisons = 0
    for k in (20, 50, 100, 500, 1000):
        for requested_s in (-1, 0, 1):
            n = int(mp.nint(k * (mp.log(k) + requested_s)))
            h = mp.mpf(n) / k
            lam = k * mp.exp(-h)
            estimate = coupon_probability(n, k)
            probability = estimate["midpoint"]
            exact_available = n < len(stirling.first)
            if exact_available:
                exact_probability = (mp.mpf(stirling.packed(n, k))
                                     / stirling.unrestricted(n, k))
                assert estimate["lower"] <= exact_probability <= estimate["upper"]
                exact_comparisons += 1
            leading = mp.exp(-lam)
            correction = (h * (1 - mp.log(2)) * lam - (h + 1) * lam ** 2) / 2
            corrected = leading * (1 + correction / k)
            scaled_residual = ((probability / leading - 1 - correction / k)
                               * k ** 2 / h ** 2)
            records.append({
                "k": k, "n": n, "requested_s": requested_s,
                "actual_s": text_number(h - mp.log(k)),
                "eta": text_number(lam),
                "probability": text_number(probability),
                "bonferroni_lower": text_number(estimate["lower"], 100),
                "bonferroni_upper": text_number(estimate["upper"], 100),
                "analytic_bracket_width": text_number(estimate["width"]),
                "moments_used": estimate["moments_used"],
                "last_moment": text_number(estimate["last_moment"]),
                "pole_replacement_error_budget": text_number(estimate["pole_error_budget"]),
                "independently_compared_with_exact_integer_ratio": exact_available,
                "poisson_prediction": text_number(leading),
                "first_correction_prediction": text_number(corrected),
                "corrected_relative_error": text_number(probability / corrected - 1),
                "scaled_second_order_residual": text_number(scaled_residual),
            })
    return records, exact_comparisons


def diagonal_table(stirling: StirlingData) -> tuple[dict, list[dict]]:
    logarithm = mp.log(2)
    saddle = 2 + mp.lambertw(-2 * mp.exp(-2), 0)
    tilt = logarithm * saddle / 2
    variance = 2 * (saddle - 1)
    cumulant3 = 2 * (saddle ** 2 - 3 * saddle + 3)
    cumulant4 = 2 * (saddle ** 3 - 8 * saddle ** 2 + 19 * saddle - 13)
    growth = 4 * mp.expm1(saddle) / (logarithm ** 2 * saddle ** 2)
    constant = mp.exp(tilt) / (4 * mp.pi * logarithm * mp.sqrt(saddle - 1))
    beta = (cumulant4 / (8 * variance ** 2)
            - 5 * cumulant3 ** 2 / (24 * variance ** 3)
            + tilt * cumulant3 / (2 * variance ** 2)
            - (tilt + tilt ** 2) / (2 * variance)
            + (tilt ** 2 / 3 - tilt) / 2 - mp.mpf(1) / 8)

    # The second correction is evaluated from the finite Gaussian-moment
    # expansion, independently of the exact diagonal data. It is not a fit.
    cumulant5 = 2 * (saddle ** 4 - 20 * saddle ** 3 + 85 * saddle ** 2
                     - 135 * saddle + 75)
    cumulant6 = 2 * (saddle ** 5 - 47 * saddle ** 4 + 335 * saddle ** 3
                     - 940 * saddle ** 2 + 1171 * saddle - 541)
    moment2 = tilt ** 2 + tilt
    moment3 = tilt ** 3 + 3 * tilt ** 2 + tilt
    moment4 = tilt ** 4 + 6 * tilt ** 3 + 7 * tilt ** 2 + tilt
    z0 = cumulant4 / (8 * variance ** 2) - 5 * cumulant3 ** 2 / (24 * variance ** 3)
    p = tilt ** 2 / 3 - tilt
    p1 = 2 * tilt ** 2 / 3 - tilt
    p2 = 4 * tilt ** 2 / 3 - tilt
    s2 = (moment4 / (8 * variance ** 2)
          - 5 * cumulant3 * moment3 / (12 * variance ** 3)
          - 5 * cumulant4 * moment2 / (16 * variance ** 3)
          - cumulant5 * tilt / (8 * variance ** 3)
          - cumulant6 / (48 * variance ** 3)
          + 35 * cumulant3 ** 2 * moment2 / (48 * variance ** 4)
          + 35 * cumulant3 * cumulant4 * tilt / (48 * variance ** 4)
          + 7 * cumulant3 * cumulant5 / (48 * variance ** 4)
          + 35 * cumulant4 ** 2 / (384 * variance ** 4)
          - 35 * cumulant3 ** 3 * tilt / (48 * variance ** 5)
          - 35 * cumulant3 ** 2 * cumulant4 / (64 * variance ** 5)
          + 385 * cumulant3 ** 4 / (1152 * variance ** 6))
    s1p = (p * z0 + (tilt * p + p1) * cumulant3 / (2 * variance ** 2)
           - (moment2 * p + 2 * tilt * p1 + p2) / (2 * variance))
    before_binomial = s2 + s1p / 2 + (tilt ** 4 / 18 - tilt ** 2 / 3) / 4
    beta2 = before_binomial - (beta + mp.mpf(1) / 8) / 8 + mp.mpf(1) / 128
    constants = {name: text_number(value, 70) for name, value in {
        "log_2": logarithm, "saddle_r": saddle, "tilt_t": tilt,
        "variance_b": variance, "cumulant_3": cumulant3,
        "cumulant_4": cumulant4, "growth_d": growth,
        "leading_c": constant, "first_correction_beta": beta,
        "second_correction_beta2": beta2}.items()}
    records = []
    for size in (5, 10, 20, 30, 50, 75, 100):
        exact = stirling.packed(2 * size, size)
        leading = constant * growth ** size * mp.mpf(factorial(size)) ** 2 / size
        ratio = exact / leading
        records.append({
            "N": size,
            "exact_T_2N_N": str(exact),
            "ratio_to_leading_asymptotic": text_number(ratio),
            "N_times_leading_relative_error": text_number(size * (ratio - 1)),
            "beta": text_number(beta),
            "N_squared_times_corrected_remainder": text_number(
                size ** 2 * (ratio - 1 - beta / size)),
            "second_correction_beta2": text_number(beta2),
            "N_cubed_times_twice_corrected_remainder": text_number(
                size ** 3 * (ratio - 1 - beta / size - beta2 / size ** 2)),
            "corrected_relative_error": text_number(ratio / (1 + beta / size) - 1),
            "twice_corrected_relative_error": text_number(
                ratio / (1 + beta / size + beta2 / size ** 2) - 1),
        })
    return constants, records


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-root", type=Path,
                        default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    output = args.output_root / "data"
    output.mkdir(parents=True, exist_ok=True)
    started = time.perf_counter()
    mp.mp.dps = 120

    # Degree 55 is the largest tested recurrence order. Thirty further indices
    # suffice for a useful finite diagnostic; the article proves the identities.
    columns = unrestricted_by_compositions(nmax=85, kmax=10)
    packed = remove_empty_rows(columns)
    stirling = StirlingData(nmax=200)

    for n, expected in enumerate(OEIS_ROWS):
        observed = [packed[k][n] for k in range(n + 1)]
        assert observed == expected, ("OEIS row", n, observed, expected)
    formula_checks = 0
    for n in range(31):
        for k in range(11):
            assert stirling.unrestricted(n, k) == columns[k][n]
            assert stirling.packed(n, k) == packed[k][n]
            if k > n:
                assert packed[k][n] == 0
            formula_checks += 1
    for n in range(1, len(columns[1])):
        assert columns[1][n] == 2 ** (n - 1)

    recurrence_records = check_recurrences(packed)
    hankel_records = check_hankel(packed)
    initial_hankel_records = check_initial_hankel(packed, hankel_records)
    weighted_hankel_records = check_weighted_hankel()
    pole_records = check_pole_bounds(columns)
    coupon_records, exact_coupon_comparisons = coupon_table(stirling)
    constants, diagonal_records = diagonal_table(stirling)

    write_json(output / "oeis_rows.json", {
        "sequence": "A261781", "source": "https://oeis.org/A261781",
        "rows_n_0_through_8": OEIS_ROWS})
    write_json(output / "recurrence_checks.json", recurrence_records)
    write_csv(output / "hankel_determinants.csv", hankel_records)
    write_csv(output / "initial_hankel_determinants.csv", initial_hankel_records)
    write_json(output / "weighted_hankel_checks.json", weighted_hankel_records)
    write_csv(output / "pole_bound_checks.csv", pole_records)
    write_csv(output / "coupon_window.csv", coupon_records)
    write_json(output / "diagonal_constants.json", constants)
    write_csv(output / "diagonal_asymptotics.csv", diagonal_records)

    summary = {
        "status": "PASS",
        "scope": "Finite exact checks and numerical diagnostics; not mathematical proofs.",
        "floating_point_note": (
            "Coupon brackets include analytic Bonferroni and pole-replacement bounds. "
            "Decimal endpoint arithmetic is high precision but not formally directed-rounded."),
        "python": platform.python_version(),
        "sympy": sp.__version__, "mpmath": mp.__version__,
        "decimal_precision": mp.mp.dps,
        "unrestricted_composition_range": {"n_max": 85, "k_max": 10},
        "positive_stirling_formula_comparisons": formula_checks,
        "unrestricted_stirling_formula_comparisons": formula_checks,
        "matched_OEIS_rows": len(OEIS_ROWS),
        "recurrence_and_coprimality_checks_k": list(range(1, 11)),
        "full_rank_hankel_determinants_checked": len(hankel_records),
        "initial_hankel_impulse_determinants_checked": len(initial_hankel_records),
        "symbolic_weighted_hankel_determinants_checked": len(weighted_hankel_records),
        "next_rank_zero_hankel_checks_k": list(range(1, 5)),
        "uniform_pole_bound_checks": len(pole_records),
        "coupon_window_cases": len(coupon_records),
        "coupon_cases_compared_with_exact_integer_ratios": exact_coupon_comparisons,
        "dense_diagonal_cases": len(diagonal_records),
        "elapsed_seconds": round(time.perf_counter() - started, 3),
    }
    write_json(output / "verification_summary.json", summary)
    print(json.dumps(summary, indent=2))
    print("\nCoupon window, requested s=0:")
    for row in coupon_records:
        if row["requested_s"] == 0:
            print(f"k={row['k']:4d}, n={row['n']:4d}, "
                  f"P={float(row['probability']):.12f}, "
                  f"corrected={float(row['first_correction_prediction']):.12f}")
    print("\nDense diagonal: N, N*(ratio-1), N^2*(ratio-1-beta/N)")
    for row in diagonal_records:
        print(row["N"], row["N_times_leading_relative_error"],
              row["N_squared_times_corrected_remainder"])
    print(f"\nData written to {output}")


if __name__ == "__main__":
    main()
