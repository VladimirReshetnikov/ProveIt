#!/usr/bin/env python3
"""Reproducible experiments for the Fabius--Rvachev frontier report.

The script verifies four mathematically separate parts of the report.

1. Exact rational checks for confluent Richardson annihilators and for the
   twisted Thue--Morse/Prouhet filters.  No floating-point arithmetic is used
   in these checks: every residual is a ``fractions.Fraction`` and must be zero.
2. Conditioning comparisons between minimal repeated-root filters, digital
   Thue--Morse filters, additive Lambert phase locking, and multiplicative
   rational phase locking.
3. High-precision evaluation of the Gamma--zeta Fourier coefficients of the
   Fabius endpoint fluctuation, including the predicted exponential decay
   constant pi^2/log(2).
4. A controlled radial--angular tomography experiment.  Its leading periodic
   function is the *actual* Gamma--zeta endpoint fluctuation.  The higher
   inverse-Lambert coefficients are an explicitly documented synthetic model,
   because the experiment is intended to test the new sampling/filter algebra,
   not to replace the repository's exact all-orders coefficient generator.

Outputs are written to ``--output-dir`` (the current directory by default):
CSV tables, a human-readable result log, a JSON verification record, and four
PNG plots.  The plotting code deliberately uses Matplotlib defaults.

Requirements: Python 3.10+, mpmath, numpy, matplotlib.  SymPy is not required.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
from functools import lru_cache
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Callable, Iterable, Sequence

import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np


# ---------------------------------------------------------------------------
# Exact polynomial/filter utilities
# ---------------------------------------------------------------------------


def poly_mul(a: Sequence[Fraction], b: Sequence[Fraction]) -> list[Fraction]:
    """Multiply polynomials stored in ascending coefficient order."""

    out = [Fraction(0) for _ in range(len(a) + len(b) - 1)]
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] += ai * bj
    return out


def minimal_confluent_filter(
    roots_and_multiplicities: Sequence[tuple[Fraction, int]],
) -> list[Fraction]:
    r"""Return the unique minimal normalized annihilator.

    The returned coefficients ``w[j]`` form

        W(z) = product_r ((z-q_r)/(1-q_r))**m_r = sum_j w[j] z**j.

    Hence W(1)=1 and q_r is a root of multiplicity m_r.  Applying W(E), where
    E is the forward shift, annihilates n**ell * q_r**n for ell < m_r.
    """

    w = [Fraction(1)]
    for q, multiplicity in roots_and_multiplicities:
        if q == 0:
            raise ValueError("q=0 is excluded: the confluent Euler-root calculus assumes q!=0")
        if q == 1:
            raise ValueError("q=1 is incompatible with normalization W(1)=1")
        if multiplicity <= 0:
            raise ValueError("multiplicities must be positive")
        factor = [(-q) / (1 - q), Fraction(1, 1) / (1 - q)]
        for _ in range(multiplicity):
            w = poly_mul(w, factor)
    return w


def thue_morse_sign(n: int) -> int:
    """The signed Thue--Morse bit (-1)^{s_2(n)}."""

    return -1 if n.bit_count() & 1 else 1


def finite_thue_morse_product(q: Fraction, order: int) -> Fraction:
    """Theta_order(q) = product_{j=0}^{order-1} (1-q^{2^j})."""

    value = Fraction(1)
    for j in range(order):
        value *= 1 - q ** (1 << j)
    return value


def twisted_thue_morse_filter(q: Fraction, order: int) -> list[Fraction]:
    r"""Return the normalized digital filter T_m(z/q)/T_m(1/q).

    Here

        T_m(z) = product_{j=0}^{m-1} (1-z^{2^j})
               = sum_{n=0}^{2^m-1} tau_n z^n.

    A numerically gentler equivalent coefficient formula is

        w_n = (-1)^m tau_n q^{2^m-1-n} / T_m(q).

    The polynomial has a root of order m at z=q, preserves constants, and
    therefore annihilates n**ell q**n for all ell < m.
    """

    if not (Fraction(0) < q < Fraction(1)):
        raise ValueError("the conditioning formulas assume 0<q<1")
    if order <= 0:
        raise ValueError("order must be positive")

    degree = (1 << order) - 1
    theta = finite_thue_morse_product(q, order)
    sign0 = -1 if order & 1 else 1
    return [
        Fraction(sign0 * thue_morse_sign(n), 1) * q ** (degree - n) / theta
        for n in range(degree + 1)
    ]


def filter_value(weights: Sequence[Fraction], z: Fraction) -> Fraction:
    """Evaluate an ascending-order polynomial by Horner's rule."""

    value = Fraction(0)
    for coefficient in reversed(weights):
        value = value * z + coefficient
    return value


def exact_mode_residual(
    weights: Sequence[Fraction], q: Fraction, degree: int, n0: int
) -> Fraction:
    """Apply a filter exactly to n^degree q^n at n=n0."""

    return sum(
        (weight * Fraction((n0 + shift) ** degree, 1) * q ** (n0 + shift)
         for shift, weight in enumerate(weights)),
        Fraction(0),
    )


def l1_fraction(weights: Sequence[Fraction]) -> Fraction:
    return sum((abs(w) for w in weights), Fraction(0))


# ---------------------------------------------------------------------------
# Geometric q-Richardson and Lambert phase-locking utilities
# ---------------------------------------------------------------------------


def geometric_lagrange_weights(q: mp.mpf, order: int) -> list[mp.mpf]:
    r"""Weights for evaluating at t=0 from t_s=q^s, 0<=s<=order.

    The closed formula is

      omega_s = (-1)^{p-s} q^{(p-s)(p-s+1)/2}
                / ((q;q)_s (q;q)_{p-s}).

    Equivalently, sum_s omega_s z^s has roots q,q^2,...,q^p and value 1 at z=1.
    """

    p = order
    qpoch = [mp.mpf(1)]
    for j in range(1, p + 1):
        qpoch.append(qpoch[-1] * (1 - q**j))
    return [
        (-1) ** (p - s)
        * q ** ((p - s) * (p - s + 1) // 2)
        / (qpoch[s] * qpoch[p - s])
        for s in range(p + 1)
    ]


def geometric_condition_number(q: mp.mpf, order: int) -> mp.mpf:
    """Exact l1 norm (-q;q)_p/(q;q)_p."""

    value = mp.mpf(1)
    for r in range(1, order + 1):
        value *= (1 + q**r) / (1 - q**r)
    return value


def additive_phase_weights(lam: mp.mpf, order: int) -> list[mp.mpf]:
    r"""Weights for the existing additive phase lock lambda+j.

    Interpolation uses h_j=(lambda+j)^(-1) and evaluates at h=0.  The exact
    weights are

      a_j = (-1)^{p-j} (lambda+j)^p / (j!(p-j)!).
    """

    p = order
    return [
        (-1) ** (p - j)
        * (lam + j) ** p
        / (mp.factorial(j) * mp.factorial(p - j))
        for j in range(p + 1)
    ]


# ---------------------------------------------------------------------------
# Gamma--zeta endpoint fluctuation
# ---------------------------------------------------------------------------


LOG2 = mp.log(2)
ALPHA = mp.pi**2 / LOG2
STRIP_HALF_WIDTH = mp.pi / (2 * LOG2)


@lru_cache(maxsize=None)
def endpoint_fourier_coefficient(k: int) -> mp.mpc:
    r"""Nonzero Fourier coefficient of the endpoint periodic fluctuation.

    With chi_k=2*pi*i*k/log(2), the audited corpus gives

       c_k = -Gamma(-chi_k) zeta(1-chi_k) / log(2),  k != 0.

    The mean c_0 is irrelevant to the alias and strip experiments, so this
    function intentionally rejects k=0.
    """

    if k == 0:
        raise ValueError("the nonzero-mode formula does not define the mean")
    chi = 2 * mp.pi * 1j * k / LOG2
    return -mp.gamma(-chi) * mp.zeta(1 - chi, method="euler-maclaurin") / LOG2


def endpoint_periodic_value(u: mp.mpf, cutoff: int) -> mp.mpf:
    """Real zero-mean periodic fluctuation truncated at |k|<=cutoff."""

    total = mp.mpc(0)
    for k in range(1, cutoff + 1):
        ck = endpoint_fourier_coefficient(k)
        term = ck * mp.e ** (2j * mp.pi * k * u)
        total += term + mp.conj(term)
    return mp.re(total)


def model_periodic_coefficient(j: int, u: mp.mpf, cutoff: int) -> mp.mpf:
    r"""Periodic coefficient A_j(u) used in the radial experiment.

    A_0 is the actual Gamma--zeta fluctuation.  For j>=1 we retain the same
    Fourier phases and apply the explicit even multiplier

        beta_j(k) = 0.2^j * (1 + k^2/(j+1)^2).

    This creates a smooth, real, uniformly convergent all-orders surrogate while
    keeping every coefficient exactly reproducible from the documented formula.
    It is *not* asserted to equal the repository's actual saddle coefficient A_j.
    """

    if j == 0:
        return endpoint_periodic_value(u, cutoff)
    total = mp.mpc(0)
    scale = mp.mpf("0.2") ** j
    for k in range(1, cutoff + 1):
        beta = scale * (1 + mp.mpf(k * k) / ((j + 1) ** 2))
        ck = endpoint_fourier_coefficient(k) * beta
        term = ck * mp.e ** (2j * mp.pi * k * u)
        total += term + mp.conj(term)
    return mp.re(total)


def endpoint_surrogate(lam: mp.mpf, max_order: int, cutoff: int) -> mp.mpf:
    """Evaluate sum_{j=0}^{max_order} A_j({lambda}) lambda^{-j}."""

    phase = mp.frac(lam)
    return mp.fsum(
        model_periodic_coefficient(j, phase, cutoff) / lam**j
        for j in range(max_order + 1)
    )


# ---------------------------------------------------------------------------
# Experiment orchestration
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ExactFilterRecord:
    order: int
    minimal_span: int
    digital_span: int
    minimal_condition: Fraction
    digital_condition: Fraction
    residuals_zero: bool


def run_exact_filter_experiments(output_dir: Path) -> list[ExactFilterRecord]:
    q = Fraction(1, 2)
    records: list[ExactFilterRecord] = []

    for order in range(1, 11):
        minimal = minimal_confluent_filter([(q, order)])
        digital = twisted_thue_morse_filter(q, order)

        checks: list[bool] = []
        for degree in range(order):
            checks.append(exact_mode_residual(minimal, q, degree, n0=7) == 0)
            checks.append(exact_mode_residual(digital, q, degree, n0=7) == 0)

        records.append(
            ExactFilterRecord(
                order=order,
                minimal_span=len(minimal) - 1,
                digital_span=len(digital) - 1,
                minimal_condition=l1_fraction(minimal),
                digital_condition=l1_fraction(digital),
                residuals_zero=all(checks),
            )
        )

    # A mixed-mode exact test: double root at 1/2 and simple root at 1/4.
    mixed = minimal_confluent_filter([(Fraction(1, 2), 2), (Fraction(1, 4), 1)])
    mixed_expected = [Fraction(-1, 3), Fraction(8, 3), Fraction(-20, 3), Fraction(16, 3)]
    if mixed != mixed_expected:
        raise AssertionError(f"unexpected mixed filter: {mixed!r}")
    for degree in range(2):
        assert exact_mode_residual(mixed, Fraction(1, 2), degree, 5) == 0
    assert exact_mode_residual(mixed, Fraction(1, 4), 0, 5) == 0

    csv_path = output_dir / "filter_conditioning.csv"
    with csv_path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream, lineterminator="\n")
        writer.writerow(
            [
                "order",
                "minimal_span",
                "digital_span",
                "minimal_l1_exact",
                "digital_l1_exact",
                "minimal_l1_float",
                "digital_l1_float",
                "all_exact_residuals_zero",
            ]
        )
        for rec in records:
            writer.writerow(
                [
                    rec.order,
                    rec.minimal_span,
                    rec.digital_span,
                    str(rec.minimal_condition),
                    str(rec.digital_condition),
                    float(rec.minimal_condition),
                    float(rec.digital_condition),
                    rec.residuals_zero,
                ]
            )

    plt.figure(figsize=(7.2, 4.7))
    orders = [r.order for r in records]
    plt.semilogy(orders, [float(r.minimal_condition) for r in records], marker="o", label="minimal repeated-root")
    plt.semilogy(orders, [float(r.digital_condition) for r in records], marker="s", label="twisted Thue--Morse")
    plt.xlabel("cancellation order m")
    plt.ylabel("filter l1 condition number")
    plt.title("Conditioning versus cancellation order (q=1/2)")
    plt.grid(True, which="both", alpha=0.3)
    plt.legend()
    plt.tight_layout()
    plt.savefig(output_dir / "conditioning_tradeoff.png", dpi=180)
    plt.close()

    return records


def run_lambert_conditioning_experiment(output_dir: Path) -> list[dict[str, str]]:
    # The phase 1/8 is preserved multiplicatively by rho=9 because 9 == 1 mod 8.
    denominator = 8
    rho = denominator + 1
    q = mp.mpf(1) / rho
    lam = mp.mpf(30) + mp.mpf(1) / denominator

    rows: list[dict[str, str]] = []
    for order in range(1, 11):
        additive = additive_phase_weights(lam, order)
        additive_condition = mp.fsum(abs(w) for w in additive)
        multiplicative_condition = geometric_condition_number(q, order)
        rows.append(
            {
                "order": str(order),
                "additive_l1": mp.nstr(additive_condition, 30),
                "multiplicative_l1": mp.nstr(multiplicative_condition, 30),
                "rho": str(rho),
                "lambda0": mp.nstr(lam, 20),
            }
        )

        # Directly verify the pure inverse-power moment conditions.
        weights = geometric_lagrange_weights(q, order)
        assert mp.almosteq(mp.fsum(weights), 1)
        for r in range(1, order + 1):
            assert abs(mp.fsum(weights[s] * q ** (s * r) for s in range(order + 1))) < mp.mpf("1e-60")

    with (output_dir / "lambert_conditioning.csv").open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(
            stream, fieldnames=list(rows[0].keys()), lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(rows)

    plt.figure(figsize=(7.2, 4.7))
    order_values = [int(row["order"]) for row in rows]
    plt.semilogy(order_values, [float(mp.mpf(row["additive_l1"])) for row in rows], marker="o", label="additive lambda+j")
    plt.semilogy(order_values, [float(mp.mpf(row["multiplicative_l1"])) for row in rows], marker="s", label="multiplicative rho^j lambda")
    plt.xlabel("extrapolation order p")
    plt.ylabel("weight l1 norm")
    plt.title("Lambert phase-lock conditioning (phase 1/8, lambda=30+1/8)")
    plt.grid(True, which="both", alpha=0.3)
    plt.legend()
    plt.tight_layout()
    plt.savefig(output_dir / "lambert_conditioning.png", dpi=180)
    plt.close()

    return rows


def run_gamma_zeta_experiment(output_dir: Path, max_k: int = 40) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for k in range(1, max_k + 1):
        ck = endpoint_fourier_coefficient(k)
        magnitude = abs(ck)
        rate = -mp.log(magnitude) / k
        rows.append(
            {
                "k": str(k),
                "real": mp.nstr(mp.re(ck), 35),
                "imag": mp.nstr(mp.im(ck), 35),
                "abs": mp.nstr(magnitude, 35),
                "minus_log_abs_over_k": mp.nstr(rate, 35),
            }
        )

    with (output_dir / "gamma_zeta_coefficients.csv").open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(
            stream, fieldnames=list(rows[0].keys()), lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(rows)

    plt.figure(figsize=(7.2, 4.7))
    k_values = np.array([int(row["k"]) for row in rows], dtype=float)
    rates = np.array([float(mp.mpf(row["minus_log_abs_over_k"])) for row in rows])
    plt.plot(k_values, rates, marker="o", markersize=3, label="-log|c_k| / k")
    plt.axhline(float(ALPHA), linestyle="--", label="pi^2/log 2")
    plt.xlabel("Fourier mode k")
    plt.ylabel("exponential decay-rate estimate")
    plt.title("Gamma--zeta endpoint Fourier decay")
    plt.grid(True, alpha=0.3)
    plt.legend()
    plt.tight_layout()
    plt.savefig(output_dir / "gamma_zeta_decay.png", dpi=180)
    plt.close()

    return rows


def run_tomography_experiment(output_dir: Path) -> list[dict[str, str]]:
    cutoff = 32
    radial_order = 3
    model_order = 7
    base_integer = 16
    target_mode = 1

    rows: list[dict[str, str]] = []
    for d in [4, 6, 8, 10, 12, 16]:
        rho = d + 1  # rho == 1 (mod d), so every rational phase r/d is fixed.
        q = mp.mpf(1) / rho
        weights = geometric_lagrange_weights(q, radial_order)

        exact_phase_values: list[mp.mpf] = []
        radial_estimates: list[mp.mpf] = []
        max_phase_drift = mp.mpf(0)

        for r in range(d):
            theta_fraction = Fraction(r, d)
            theta = mp.mpf(theta_fraction.numerator) / theta_fraction.denominator
            exact_phase_values.append(endpoint_periodic_value(theta, cutoff))

            samples: list[mp.mpf] = []
            for s in range(radial_order + 1):
                # Fraction arithmetic proves exact phase preservation before any
                # conversion to high-precision floating point.
                lam_fraction = (rho**s) * (Fraction(base_integer, 1) + theta_fraction)
                fractional_part = lam_fraction - (lam_fraction.numerator // lam_fraction.denominator)
                phase_error = abs(
                    mp.mpf(fractional_part.numerator) / fractional_part.denominator - theta
                )
                max_phase_drift = max(max_phase_drift, phase_error)
                lam = mp.mpf(lam_fraction.numerator) / lam_fraction.denominator
                samples.append(endpoint_surrogate(lam, model_order, cutoff))

            radial_estimates.append(mp.fsum(weights[s] * samples[s] for s in range(radial_order + 1)))

        def dft(values: Sequence[mp.mpf], k: int) -> mp.mpc:
            return mp.fsum(
                values[r] * mp.e ** (-2j * mp.pi * k * r / d) for r in range(d)
            ) / d

        phase_only = dft(exact_phase_values, target_mode)
        combined = dft(radial_estimates, target_mode)
        target = endpoint_fourier_coefficient(target_mode)
        alias_error = abs(phase_only - target)
        combined_error = abs(combined - target)
        radial_error = abs(combined - phase_only)

        rows.append(
            {
                "phase_grid_d": str(d),
                "rho": str(rho),
                "q": mp.nstr(q, 20),
                "radial_order": str(radial_order),
                "base_integer": str(base_integer),
                "alias_error": mp.nstr(alias_error, 35),
                "radial_error": mp.nstr(radial_error, 35),
                "combined_error": mp.nstr(combined_error, 35),
                "max_phase_drift": mp.nstr(max_phase_drift, 10),
            }
        )

    with (output_dir / "tomography_errors.csv").open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(
            stream, fieldnames=list(rows[0].keys()), lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(rows)

    plt.figure(figsize=(7.2, 4.7))
    d_values = [int(row["phase_grid_d"]) for row in rows]
    alias_values = [max(float(mp.mpf(row["alias_error"])), 1e-320) for row in rows]
    radial_values = [max(float(mp.mpf(row["radial_error"])), 1e-320) for row in rows]
    combined_values = [max(float(mp.mpf(row["combined_error"])), 1e-320) for row in rows]
    plt.semilogy(d_values, alias_values, marker="o", label="angular DFT alias")
    plt.semilogy(d_values, radial_values, marker="s", label="radial extrapolation")
    plt.semilogy(d_values, combined_values, marker="^", label="combined")
    plt.xlabel("number d of rational phases")
    plt.ylabel("absolute error in recovered c_1")
    plt.title("Radial--angular Lambert phase tomography")
    plt.grid(True, which="both", alpha=0.3)
    plt.legend()
    plt.tight_layout()
    plt.savefig(output_dir / "tomography_errors.png", dpi=180)
    plt.close()

    return rows


def write_human_log(
    output_dir: Path,
    exact_records: Sequence[ExactFilterRecord],
    lambert_rows: Sequence[dict[str, str]],
    gamma_rows: Sequence[dict[str, str]],
    tomography_rows: Sequence[dict[str, str]],
) -> None:
    q = Fraction(1, 2)
    theta_limit = mp.mpf(1)
    for j in range(20):
        theta_limit *= 1 - mp.mpf('0.5') ** (1 << j)
    digital_limit = 1 / ((1 - mp.mpf('0.5')) * theta_limit)

    mixed = minimal_confluent_filter([(Fraction(1, 2), 2), (Fraction(1, 4), 1)])
    tm2 = twisted_thue_morse_filter(q, 2)

    lines = [
        "FABIUS--RVACHEV FRONTIER NUMERICAL VERIFICATION",
        "=" * 58,
        "",
        f"mpmath precision: {mp.mp.dps} decimal digits",
        f"alpha = pi^2/log(2) = {mp.nstr(ALPHA, 50)}",
        f"maximal strip half-width = pi/(2 log(2)) = {mp.nstr(STRIP_HALF_WIDTH, 50)}",
        "",
        "Exact rational filters",
        "----------------------",
        f"mixed roots (1/2 multiplicity 2, 1/4 multiplicity 1): {[str(x) for x in mixed]}",
        f"twisted Thue--Morse q=1/2, order 2: {[str(x) for x in tm2]}",
        f"all exact annihilation checks through order 10: {all(r.residuals_zero for r in exact_records)}",
        f"limiting digital l1 condition q=1/2: {mp.nstr(digital_limit, 50)}",
        f"order-10 minimal condition: {exact_records[-1].minimal_condition}",
        f"order-10 digital condition (decimal): {float(exact_records[-1].digital_condition):.12f}",
        "",
        "Lambert phase-lock conditioning",
        "---------------------------------",
        f"order 10 additive l1: {lambert_rows[-1]['additive_l1']}",
        f"order 10 multiplicative l1: {lambert_rows[-1]['multiplicative_l1']}",
        "",
        "Gamma--zeta coefficients",
        "------------------------",
        f"|c_1| = {gamma_rows[0]['abs']}",
        f"-log|c_40|/40 = {gamma_rows[-1]['minus_log_abs_over_k']}",
        "",
        "Tomography",
        "----------",
    ]
    for row in tomography_rows:
        lines.append(
            "d={phase_grid_d:>2}, rho={rho:>2}, alias={alias_error}, radial={radial_error}, combined={combined_error}".format(
                **row
            )
        )
    lines.extend(
        [
            "",
            "Interpretation note:",
            "A_0 in the tomography model is the actual Gamma--zeta periodic term.",
            "A_j for j>=1 are the documented smooth surrogate coefficients in the source.",
        ]
    )
    (output_dir / "experiment_results.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")

    verification = {
        "precision_decimal_digits": mp.mp.dps,
        "alpha_pi_squared_over_log2": mp.nstr(ALPHA, 60),
        "strip_half_width": mp.nstr(STRIP_HALF_WIDTH, 60),
        "all_exact_annihilation_checks": all(r.residuals_zero for r in exact_records),
        "mixed_filter": [str(x) for x in mixed],
        "digital_order_2_filter": [str(x) for x in tm2],
        "digital_condition_limit_q_half": mp.nstr(digital_limit, 60),
        "tomography": list(tomography_rows),
    }
    (output_dir / "verification.json").write_text(
        json.dumps(verification, indent=2) + "\n", encoding="utf-8"
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path.cwd(),
        help="directory for CSV, JSON, TXT, and PNG outputs",
    )
    parser.add_argument(
        "--precision",
        type=int,
        default=90,
        help="mpmath decimal precision (default: 90)",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    mp.mp.dps = args.precision

    # mpmath constants created at import time inherit mpmath's default precision.
    # Recompute every precision-sensitive global after honoring --precision.
    global LOG2, ALPHA, STRIP_HALF_WIDTH
    LOG2 = mp.log(2)
    ALPHA = mp.pi**2 / LOG2
    STRIP_HALF_WIDTH = mp.pi / (2 * LOG2)
    endpoint_fourier_coefficient.cache_clear()

    exact_records = run_exact_filter_experiments(args.output_dir)
    lambert_rows = run_lambert_conditioning_experiment(args.output_dir)
    gamma_rows = run_gamma_zeta_experiment(args.output_dir)
    tomography_rows = run_tomography_experiment(args.output_dir)
    write_human_log(args.output_dir, exact_records, lambert_rows, gamma_rows, tomography_rows)

    print(f"Wrote experiment artifacts to {args.output_dir}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
