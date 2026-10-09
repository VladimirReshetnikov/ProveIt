#!/usr/bin/env python3
"""Numerical verification of sharp Herglotz truncation formulas.

Requires mpmath.  The mathematical proofs are in the accompanying article.
This program uses high-precision floating-point arithmetic, not interval
arithmetic.  An independent analytic bound controls omitted Dirichlet terms.

Examples (from any working directory):
  python verify_truncation.py
  python verify_truncation.py --quick
  python verify_truncation.py --digits 90 --output ../data/truncation_checks.json

The default output path is resolved relative to this script.  Higher
precision can increase running time.  The included data use 90 digits.
"""

import argparse
import json
import time
from fractions import Fraction
from pathlib import Path

import mpmath as mp


def sigma_minus_one(m):
    return sum((Fraction(1, d) for d in range(1, m + 1) if m % d == 0),
               Fraction(0))


def gamma_expectation(k, c, derivative=False):
    """E[1/(1+(T/c)^2)] for T~Gamma(k,rate=1), and optional derivative.

    E(c)=-c Im(exp(ic)*expint(k,ic)).  Differentiating the recurrence
    for the generalized exponential integral gives
    E'(c)=k E(c)/c-c Re(exp(ic)*expint(k,ic)).
    """
    auxiliary = mp.exp(1j * c) * mp.expint(k, 1j * c)
    expectation = -c * mp.im(auxiliary)
    if derivative:
        return expectation, k * expectation / c - c * mp.re(auxiliary)
    return expectation


def dirichlet_tail_bound(k, m):
    """Upper bound for sum_{j>m}sigma_{-1}(j)j^{-k}, k>1,m>=2."""
    return mp.mpf(m) ** (1 - k) * (
        (1 + mp.log(m)) / (k - 1) + mp.mpf(1) / (k - 1) ** 2
    )


def newton_root(value_and_derivative, initial):
    """Newton iteration; mathematical existence and uniqueness are proved."""
    value = mp.mpf(initial)
    tolerance = mp.power(10, -(mp.mp.dps - 12))
    for iteration in range(16):
        residual, derivative = value_and_derivative(value)
        if derivative <= 0:
            raise ArithmeticError("Expected a positive transition derivative")
        step = residual / derivative
        value -= step
        if abs(step) <= tolerance * max(1, abs(value)):
            return value, iteration + 1
    raise ArithmeticError("Newton iteration did not converge")


def transition(k, m):
    b = mp.mpf(k) - mp.mpf("0.5")

    def pure_equation(a):
        expectation, derivative = gamma_expectation(k, a, derivative=True)
        return expectation - mp.mpf("0.5"), derivative

    initial = b + mp.mpf(3) / (8 * b) - 1 / b ** 2 + mp.mpf(407) / (128 * b ** 3)
    pure, pure_iterations = newton_root(pure_equation, initial)
    weights = []
    for j in range(1, m + 1):
        q = sigma_minus_one(j)
        weights.append(mp.mpf(q.numerator) / q.denominator / mp.mpf(j) ** k)

    def mixture_equation(a):
        values, derivatives = [], []
        precision = mp.mp.dps
        for j, weight in enumerate(weights, start=1):
            # The weight itself supplies many digits of absolute accuracy.
            # Keep ten guard digits when evaluating tiny weighted terms.
            working_digits = max(30, min(precision,
                precision - int(k * mp.log10(j)) + 10))
            with mp.workdps(working_digits):
                expectation, derivative = gamma_expectation(k, a * j,
                                                           derivative=True)
            values.append(weight * (expectation - mp.mpf("0.5")))
            derivatives.append(weight * j * derivative)
        return mp.fsum(values), mp.fsum(derivatives)

    predicted_shift = -mp.mpf("0.9") * k * mp.mpf(2) ** (-k)
    initial_full = pure + predicted_shift * (1 - mp.mpf(7) / (50 * k))
    full, full_iterations = newton_root(mixture_equation, initial_full)
    # On [k-1,k], for k>=8, the transition derivative is >=4/(25k)
    # by Chebyshev's inequality on T in [k/2,3k/2].  Each omitted
    # Dirichlet summand is bounded by half its weight.
    tail_root_bound = mp.mpf(25) * k / 8 * dirichlet_tail_bound(k, m)
    assert k - 1 < full < pure < k
    digits = min(70, mp.mp.dps - 15)
    ratio_digits = max(8, min(25, mp.mp.dps - int(k * mp.log10(2)) - 5))
    return {
        "N": (k - 2) // 2,
        "K": k,
        "Dirichlet_terms": m,
        "a_pure": mp.nstr(pure, digits),
        "a_full_truncated": mp.nstr(full, digits),
        "shift_over_minus_0.9K2_to_minus_K": mp.nstr(
            (full - pure) / predicted_shift, ratio_digits),
        "b_cubed_algebraic_residual": mp.nstr(
            b ** 3 * (pure - b - mp.mpf(3) / (8 * b) + 1 / b ** 2), 25),
        "root_error_from_omitted_Dirichlet_terms_bound": mp.nstr(
            tail_root_bound, 8),
        "Newton_iterations_pure": pure_iterations,
        "Newton_iterations_full": full_iterations,
    }


def coefficient_check(n, delta):
    delta = mp.mpf(delta)
    x = (n - delta) / mp.pi
    a = 2 * mp.pi * x
    k = 2 * n + 2
    c1 = 2 * delta ** 2 + delta - mp.mpf(5) / 12
    c2 = (2 * delta ** 4 + mp.mpf(2) / 3 * delta ** 3
          - mp.mpf(10) / 3 * delta ** 2 - mp.mpf(7) / 12 * delta
          + mp.mpf(205) / 288)
    prefactor = 2 * mp.gamma(k) * mp.exp(a) * mp.sqrt(x) / a ** k
    exact = prefactor * gamma_expectation(k, a)
    # Avoid cancellation in zeta(k)*zeta(k+1)-1 when k is large.
    tail = prefactor * 4 * mp.mpf(2) ** (-k)
    return {
        "N": n,
        "delta": mp.nstr(delta),
        "pure_scaled_remainder": mp.nstr(exact, 35),
        "a_cubed_residual_after_C1_C2": mp.nstr(
            a ** 3 * (exact - 1 - c1 / a - c2 / a ** 2), 25),
        "full_minus_pure_scaled_upper_bound": mp.nstr(tail, 8),
    }


def quadrature_check(k, c):
    """Independent positive-real integral, not an exponential integral."""
    c = mp.mpf(c)
    direct = mp.quad(
        lambda t: t ** (k - 1) * mp.exp(-t) / (1 + (t / c) ** 2),
        [0, k / 2, k, 2 * k, mp.inf],
    ) / mp.gamma(k)
    residual = abs(direct - gamma_expectation(k, c))
    assert residual < mp.power(10, -(mp.mp.dps - 8))
    return {"K": k, "c": str(c),
            "absolute_residual": mp.nstr(residual, 8)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true",
                        help="Run three transitions and a smaller remainder grid")
    parser.add_argument("--digits", type=int, default=None,
                        help="Working precision (default 70; quick default 55)")
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1]
                                / "data" / "truncation_checks.json")
    args = parser.parse_args()
    mp.mp.dps = args.digits or (55 if args.quick else 70)
    if mp.mp.dps < 55:
        parser.error("Use at least 55 digits to resolve the arithmetic shifts")
    if not args.quick and mp.mp.dps < 70:
        parser.error("The full grid needs at least 70 digits; use --quick at 55")
    start = time.monotonic()
    cases = ([(5, 8), (20, 4), (40, 3)] if args.quick else
             [(5, 12), (10, 8), (20, 6), (40, 4), (80, 3)])
    transitions = []
    for n, terms in cases:
        record = transition(2 * n + 2, terms)
        transitions.append(record)
        print(f"N={n}: shift ratio="
              f"{record['shift_over_minus_0.9K2_to_minus_K']}", flush=True)
    deltas = ["-0.75", "0.1"] if args.quick else ["-0.75", "-0.25", "0.1", "0.6"]
    indices = [30, 100] if args.quick else [30, 100, 300]
    quadrature_cases = [(12, "11.5"), (82, "81.5")]
    if not args.quick:
        quadrature_cases.append((202, "201.5"))
    results = {
        "precision_digits": mp.mp.dps,
        "method": "high-precision floating point; analytic Dirichlet-tail bounds",
        "quick_mode": args.quick,
        "transition_checks": transitions,
        "remainder_checks": [coefficient_check(n, d) for d in deltas for n in indices],
        "independent_gamma_quadrature_checks": [
            quadrature_check(k, c) for k, c in quadrature_cases],
        "predicted_limit_b_cubed_residual": "407/128 = 3.1796875",
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results, indent=2) + "\n")
    print(f"Wrote {args.output.name}; elapsed {time.monotonic()-start:.1f}s")


if __name__ == "__main__":
    main()
