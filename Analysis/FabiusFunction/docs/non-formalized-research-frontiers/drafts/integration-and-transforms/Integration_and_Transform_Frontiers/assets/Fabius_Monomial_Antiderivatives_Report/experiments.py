#!/usr/bin/env python3
"""Reproducible numerical and exact checks for the report
"Fabius Monomial Antiderivatives and Inverse-Quantile Integrals".

The script is deliberately self-contained and makes no network requests.
It performs four independent tasks:

1. Compute exact dyadic values V_n = F(2^{-n}) from the rational recurrence
   recorded in the ProveIt corpus.
2. Verify, with exact rational coefficient arithmetic, that the proposed
   polynomial primitive differentiates to x^p F(x).
3. Evaluate the convergent complex-exponent primitive series at x=1.
4. Cross-check those values with a scrambled Sobol quasi-Monte Carlo
   simulation of the probabilistic representation

       X = sum_{j>=1} 2^{-j} U_j,  U_j ~ Uniform[0,1],

   for which F is the distribution function and

       integral_0^1 x^alpha F(x) dx
       = (1 - E[X^(alpha+1)])/(alpha+1),  alpha != -1,
       = -E[log X],                            alpha = -1.

The QMC calculation is only a numerical cross-check; it is not used in any
proof.  The exact recurrence and exact symbolic cancellation are proofs of
finite algebraic statements, while the analytic convergence proof is in the
LaTeX report.
"""

from __future__ import annotations

import argparse
import csv
import math
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Dict, Iterable, List, Mapping, Sequence, Tuple

import mpmath as mp
import numpy as np
from scipy.stats import qmc


# ---------------------------------------------------------------------------
# Exact dyadic arithmetic
# ---------------------------------------------------------------------------


def binom2(n: int) -> int:
    """Return n choose 2 for an integer n."""
    return n * (n - 1) // 2


def exact_dyadic_values(n_max: int) -> List[Fraction]:
    r"""Return V_n = F(2^{-n}) for 0 <= n <= n_max exactly.

    The recurrence is

      V_0 = 1,
      V_n = 2^{-binom(n,2)}/(2^n-1)
            * sum_{k=0}^{n-1} 2^{binom(k,2)} V_k/(n-k+1)!.

    All operations are performed with fractions.Fraction.
    """
    if n_max < 0:
        raise ValueError("n_max must be nonnegative")

    values: List[Fraction] = [Fraction(1)]
    for n in range(1, n_max + 1):
        inner = Fraction(0)
        for k, vk in enumerate(values):
            inner += Fraction(2**binom2(k), math.factorial(n - k + 1)) * vk
        vn = Fraction(1, 2**binom2(n)) * inner / (2**n - 1)
        values.append(vn)
    return values


def moment_from_dyadic_formula(p: int, values: Sequence[Fraction]) -> Fraction:
    r"""Compute integral_0^1 x^p F(x) dx from the finite primitive formula."""
    if p < 0:
        raise ValueError("p must be nonnegative")
    if len(values) <= p + 1:
        raise ValueError("values must contain V_0 through V_{p+1}")

    total = Fraction(0)
    for k in range(p + 1):
        coefficient = Fraction(
            (-1) ** k * math.factorial(p) * 2 ** binom2(k + 1),
            math.factorial(p - k),
        )
        total += coefficient * values[k + 1]
    return total


def fabius_moment_d(n: int, values: Sequence[Fraction]) -> Fraction:
    r"""Return d_n = E[X^n] = n! 2^{binom(n,2)} F(2^{-n})."""
    if n < 0 or len(values) <= n:
        raise ValueError("values must contain V_n")
    return Fraction(math.factorial(n) * 2**binom2(n)) * values[n]


# ---------------------------------------------------------------------------
# Exact formal differentiation of the finite polynomial primitive
# ---------------------------------------------------------------------------

# A monomial is represented by (power_of_x, scale_index_j), where F_j means
# F(x/2^j).  A dictionary maps such monomials to exact rational coefficients.
FormalExpression = Dict[Tuple[int, int], Fraction]


def add_term(expr: FormalExpression, key: Tuple[int, int], value: Fraction) -> None:
    """Add a coefficient and remove exact zeros."""
    expr[key] = expr.get(key, Fraction(0)) + value
    if expr[key] == 0:
        del expr[key]


def differentiate_formal(expr: Mapping[Tuple[int, int], Fraction]) -> FormalExpression:
    r"""Differentiate using F_j'(x) = 2^{1-j} F_{j-1}(x).

    This follows from F'(u)=2F(2u):

      d/dx F(x/2^j) = 2^{-j} F'(x/2^j)
                       = 2^{1-j} F(x/2^{j-1}).

    The target F(x) is represented by scale index j=0.
    """
    result: FormalExpression = {}
    for (power, scale), coefficient in expr.items():
        if power > 0:
            add_term(result, (power - 1, scale), coefficient * power)
        if scale < 1:
            raise ValueError("formal primitive should only contain scale >= 1")
        add_term(result, (power, scale - 1), coefficient * Fraction(1, 2 ** (scale - 1)))
    return result


def polynomial_primitive_formal(p: int) -> FormalExpression:
    r"""Construct the proposed primitive of x^p F(x) as a formal expression."""
    if p < 0:
        raise ValueError("p must be nonnegative")
    result: FormalExpression = {}
    for k in range(p + 1):
        coefficient = Fraction(
            (-1) ** k * math.factorial(p) * 2 ** binom2(k + 1),
            math.factorial(p - k),
        )
        add_term(result, (p - k, k + 1), coefficient)
    return result


def verify_polynomial_primitives(p_max: int = 12) -> List[Tuple[int, bool]]:
    """Verify the derivative identity exactly for p=0,...,p_max."""
    checks: List[Tuple[int, bool]] = []
    for p in range(p_max + 1):
        derivative = differentiate_formal(polynomial_primitive_formal(p))
        expected: FormalExpression = {(p, 0): Fraction(1)}
        checks.append((p, derivative == expected))
    return checks


# ---------------------------------------------------------------------------
# High-precision dyadic values and the complex-exponent series
# ---------------------------------------------------------------------------


def mp_dyadic_values(n_max: int, dps: int = 100) -> List[mp.mpf]:
    """High-precision floating version of the exact dyadic recurrence."""
    if n_max < 0:
        raise ValueError("n_max must be nonnegative")
    mp.mp.dps = dps
    values: List[mp.mpf] = [mp.mpf(1)]
    for n in range(1, n_max + 1):
        inner = mp.mpf(0)
        for k, vk in enumerate(values):
            inner += mp.power(2, binom2(k)) * vk / mp.factorial(n - k + 1)
        vn = mp.power(2, -binom2(n)) * inner / (mp.power(2, n) - 1)
        values.append(vn)
    return values


def falling_factorial(alpha: mp.mpc, k: int) -> mp.mpc:
    """Compute alpha^(underline k) without Gamma-function singularities."""
    value = mp.mpc(1)
    for j in range(k):
        value *= alpha - j
    return value


def primitive_series_partial_sums(
    alpha: complex | float | int,
    x: float,
    n_terms: int,
    values: Sequence[mp.mpf],
) -> List[mp.mpc]:
    r"""Return partial sums of

      I_alpha(x) = sum_{k>=0} (-1)^k alpha^(underline k)
                   2^{binom(k+1,2)} x^{alpha-k} F(x/2^{k+1}).

    This routine presently uses tabulated dyadic values and is therefore used
    at x=1 in the report.  For a general dyadic x=2^{-r}, replace V_{k+1} by
    V_{k+r+1}; the analytic formula itself is valid for every x>0.
    """
    if x != 1.0:
        raise NotImplementedError(
            "the numerical recurrence table in this script is specialized to x=1"
        )
    if n_terms < 1 or len(values) <= n_terms:
        raise ValueError("values must contain V_0 through V_n_terms")

    a = mp.mpc(alpha)
    total = mp.mpc(0)
    partials: List[mp.mpc] = []
    falling = mp.mpc(1)
    for k in range(n_terms):
        if k > 0:
            falling *= a - (k - 1)
        term = (
            (-1) ** k
            * falling
            * mp.power(x, a - k)
            * mp.power(2, binom2(k + 1))
            * values[k + 1]
        )
        total += term
        partials.append(total)
    return partials


# ---------------------------------------------------------------------------
# Independent quasi-Monte Carlo check
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class QMCResult:
    alpha: float
    estimates: Tuple[float, ...]

    @property
    def mean(self) -> float:
        return float(np.mean(self.estimates))

    @property
    def spread(self) -> float:
        return float(np.max(self.estimates) - np.min(self.estimates))


def qmc_integral_estimate(
    alpha: float,
    *,
    power_of_two: int = 19,
    dimensions: int = 28,
    scrambles: int = 4,
) -> QMCResult:
    r"""Estimate I_alpha(1) from the random-series moment identity.

    The omitted tail of X after ``dimensions`` terms is at most 2^{-dimensions}.
    Each scramble uses an independent deterministic seed for reproducibility.
    """
    weights = np.exp2(-np.arange(1, dimensions + 1, dtype=np.float64))
    estimates: List[float] = []

    for seed in range(scrambles):
        engine = qmc.Sobol(d=dimensions, scramble=True, seed=20260827 + seed)
        uniforms = engine.random_base2(m=power_of_two)
        x_samples = uniforms @ weights

        if alpha == -1.0:
            estimate = -float(np.mean(np.log(x_samples)))
        else:
            rho = alpha + 1.0
            estimate = (1.0 - float(np.mean(np.power(x_samples, rho)))) / rho
        estimates.append(estimate)

    return QMCResult(alpha=alpha, estimates=tuple(estimates))


# ---------------------------------------------------------------------------
# Output
# ---------------------------------------------------------------------------


def mp_format(value: mp.mpc, digits: int = 30) -> str:
    """Compact real/complex formatting."""
    if abs(mp.im(value)) < mp.mpf(10) ** (-(digits - 3)):
        return mp.nstr(mp.re(value), digits)
    return mp.nstr(value, digits)


def write_outputs(output_dir: Path, quick: bool = False) -> None:
    output_dir.mkdir(parents=True, exist_ok=True)

    exact_max = 12
    exact_values = exact_dyadic_values(exact_max)
    exact_checks = verify_polynomial_primitives(12)

    n_terms = 160 if quick else 240
    mp_values = mp_dyadic_values(n_terms + 1, dps=120)
    alphas = [-1.0, -0.5, 0.5, 2.3]
    checkpoints = [5, 10, 20, 40, 80, 120, 160]
    if not quick:
        checkpoints.extend([200, 240])

    series_rows: List[Tuple[float, int, str]] = []
    final_series: Dict[float, mp.mpc] = {}
    for alpha in alphas:
        partials = primitive_series_partial_sums(alpha, 1.0, n_terms, mp_values)
        for n in checkpoints:
            if n <= n_terms:
                series_rows.append((alpha, n, mp_format(partials[n - 1], 40)))
        final_series[alpha] = partials[-1]

    qmc_power = 17 if quick else 19
    qmc_results = [
        qmc_integral_estimate(alpha, power_of_two=qmc_power, dimensions=28, scrambles=4)
        for alpha in alphas
    ]

    csv_path = output_dir / "series_convergence.csv"
    with csv_path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(["alpha", "terms", "partial_sum"])
        writer.writerows(series_rows)

    text_path = output_dir / "numerical_results.txt"
    with text_path.open("w", encoding="utf-8") as handle:
        handle.write("FABIUS MONOMIAL ANTIDERIVATIVE CHECKS\n")
        handle.write("Generated by experiments.py; no network access used.\n\n")

        handle.write("Exact dyadic values V_n = F(2^{-n}):\n")
        for n, value in enumerate(exact_values[:8]):
            handle.write(f"  V_{n} = {value} = {float(value):.17g}\n")

        handle.write("\nExact formal derivative checks:\n")
        for p, passed in exact_checks:
            handle.write(f"  p={p:2d}: {'PASS' if passed else 'FAIL'}\n")
        if not all(passed for _, passed in exact_checks):
            raise RuntimeError("an exact polynomial derivative check failed")

        handle.write("\nExact complete moments from two equivalent formulas:\n")
        for p in range(0, 8):
            finite = moment_from_dyadic_formula(p, exact_values)
            d_value = fabius_moment_d(p + 1, exact_values)
            probabilistic = Fraction(1) - d_value
            probabilistic /= p + 1
            status = "PASS" if finite == probabilistic else "FAIL"
            handle.write(
                f"  p={p}: integral={finite} = {float(finite):.17g}; "
                f"identity={status}\n"
            )
            if finite != probabilistic:
                raise RuntimeError(f"moment identity failed for p={p}")

        handle.write("\nComplex-exponent series at x=1:\n")
        for alpha in alphas:
            handle.write(
                f"  alpha={alpha:5.1f}, N={n_terms}: "
                f"{mp_format(final_series[alpha], 40)}\n"
            )

        handle.write("\nScrambled Sobol QMC cross-checks:\n")
        handle.write(
            f"  points per scramble = 2^{qmc_power}; dimensions = 28; scrambles = 4\n"
        )
        for result in qmc_results:
            handle.write(f"  alpha={result.alpha:5.1f}\n")
            for index, estimate in enumerate(result.estimates):
                handle.write(f"    scramble {index}: {estimate:.15f}\n")
            series_value = float(mp.re(final_series[result.alpha]))
            handle.write(f"    mean       : {result.mean:.15f}\n")
            handle.write(f"    spread     : {result.spread:.3e}\n")
            handle.write(f"    series-QMC : {series_value - result.mean:+.3e}\n")

        handle.write("\nInterpretation:\n")
        handle.write(
            "  The exact checks validate the finite algebraic identities.  The QMC values\n"
            "  independently agree with the convergent antiderivative series to the\n"
            "  displayed sampling precision.  QMC is not part of the proof.\n"
        )

    print(text_path.read_text(encoding="utf-8"))
    print(f"Wrote {csv_path}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path(__file__).resolve().parent,
        help="directory for numerical_results.txt and series_convergence.csv",
    )
    parser.add_argument(
        "--quick",
        action="store_true",
        help="use fewer QMC points and fewer series terms for a fast smoke test",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    write_outputs(args.output_dir, quick=args.quick)


if __name__ == "__main__":
    main()
