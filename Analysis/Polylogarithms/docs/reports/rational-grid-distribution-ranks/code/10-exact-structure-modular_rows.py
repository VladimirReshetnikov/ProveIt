#!/usr/bin/env python3
"""Exact recurrences and numerical checks for modular polygamma rows.

Requires Python 3.10+, SymPy, and mpmath. Run:

    python code/modular_rows.py

The default output is data/modular_rows.json beside the article. Symbolic
recurrences use rational arithmetic. Decimal values use ordinary mpmath
arithmetic, not directed interval arithmetic; their role is independent
numerical verification of the proved identities and tail bounds.

Notation:
    T[w,j](tau) = sum(n**j * (psi[w-1+j](n*tau)
                       + (-1)**j * psi[w-1+j](1-n*tau)), n >= 1),
where w >= 2 is even, j >= 0, and Im(tau) > 0.
"""

from __future__ import annotations

import argparse
import json
from functools import lru_cache
from pathlib import Path

import mpmath as mp
import sympy as sp


T = sp.Symbol("t")
X, Y, Z = sp.symbols("X Y Z")


def nonnegative_integer(value: int, name: str) -> None:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{name} must be a nonnegative integer")


@lru_cache(maxsize=None)
def negative_polylog_expression(order: int) -> sp.Expr:
    """Return the exact rational function Li_{-order}(t)."""
    nonnegative_integer(order, "order")
    if order == 0:
        return T / (1 - T)
    return sp.cancel(T * sp.diff(negative_polylog_expression(order - 1), T))


@lru_cache(maxsize=None)
def negative_polylog_coefficients(order: int) -> tuple[tuple[int, ...], ...]:
    """Integer numerator/denominator coefficients, in descending order."""
    numerator, denominator = negative_polylog_expression(order).as_numer_denom()
    return (
        tuple(int(c) for c in sp.Poly(numerator, T).all_coeffs()),
        tuple(int(c) for c in sp.Poly(denominator, T).all_coeffs()),
    )


def horner(coefficients: tuple[int, ...], value):
    result = mp.mpf(0)
    for coefficient in coefficients:
        result = result * value + coefficient
    return result


def negative_polylog(order: int, value):
    """Evaluate Li_{-order} by its exact rational coefficients."""
    numerator, denominator = negative_polylog_coefficients(order)
    return horner(numerator, value) / horner(denominator, value)


@lru_cache(maxsize=None)
def ramanujan_polynomial(order: int) -> sp.Expr:
    """P_0=X, P_{j+1}=V(P_j), with Ramanujan's rational derivation V."""
    nonnegative_integer(order, "order")
    if order == 0:
        return X
    previous = ramanujan_polynomial(order - 1)
    return sp.expand(
        (X**2 - Y) * sp.diff(previous, X) / 12
        + (X * Y - Z) * sp.diff(previous, Y) / 3
        + (X * Z - Y**2) * sp.diff(previous, Z) / 2
    )


def evaluate_rational_polynomial(expression: sp.Expr, x, y, z):
    """Preserve exact rational coefficients before mpmath evaluation."""
    terms = []
    for powers, coefficient in sp.Poly(expression, X, Y, Z).terms():
        coefficient = sp.Rational(coefficient)
        scalar = mp.mpf(int(coefficient.p)) / int(coefficient.q)
        terms.append(scalar * x**powers[0] * y**powers[1] * z**powers[2])
    return mp.fsum(terms)


def validate_row_parameters(weight: int, derivative: int, tau) -> None:
    nonnegative_integer(weight, "weight")
    nonnegative_integer(derivative, "derivative")
    if weight < 2 or weight % 2:
        raise ValueError("weight must be even and at least two")
    if mp.im(tau) <= 0:
        raise ValueError("tau must be in the upper half-plane")


def row_summand(weight: int, derivative: int, n: int, tau):
    """One paired row, including the factor n**derivative."""
    validate_row_parameters(weight, derivative, tau)
    nonnegative_integer(n, "n")
    if n == 0:
        raise ValueError("n must be positive")
    qn = mp.exp(2 * mp.pi * mp.j * n * tau)
    return (
        (2 * mp.pi * mp.j) ** (weight + derivative)
        * n**derivative
        * negative_polylog(weight + derivative - 1, qn)
    )


def partial_row_sum(weight: int, derivative: int, tau, rows: int):
    nonnegative_integer(rows, "rows")
    validate_row_parameters(weight, derivative, tau)
    return mp.fsum(row_summand(weight, derivative, n, tau)
                   for n in range(1, rows + 1))


def row_tail_bound(weight: int, derivative: int, tau, rows: int):
    """Evaluate the proved bound for the tail after `rows` paired rows.

    (2*pi)^(w+j) (N+1)^j Li_{-j}(r)/r * Li_{1-w-j}(r^(N+1)),
    where r=exp(-2*pi*Im(tau)). The mathematical bound is rigorous;
    this numerical evaluator does not provide outward rounding.
    """
    validate_row_parameters(weight, derivative, tau)
    nonnegative_integer(rows, "rows")
    r = mp.exp(-2 * mp.pi * mp.im(tau))
    return (
        (2 * mp.pi) ** (weight + derivative)
        * (rows + 1) ** derivative
        * negative_polylog(derivative, r) / r
        * negative_polylog(weight + derivative - 1, r ** (rows + 1))
    )


def cm_parameters(name: str):
    """Return tau and exact-special-value evaluations of (E2,E4,E6)."""
    if name == "i":
        tau = mp.j
        values = (
            3 / mp.pi,
            3 * mp.gamma(mp.mpf(1) / 4) ** 8 / (64 * mp.pi**6),
            mp.mpf(0),
        )
    elif name == "rho":
        tau = (1 + mp.j * mp.sqrt(3)) / 2
        values = (
            2 * mp.sqrt(3) / mp.pi,
            mp.mpf(0),
            27 * mp.gamma(mp.mpf(1) / 3) ** 18 / (512 * mp.pi**12),
        )
    else:
        raise ValueError("CM point must be 'i' or 'rho'")
    return tau, values


def cm_trigamma_jet(name: str, derivative: int):
    """Evaluate the exact Ramanujan-polynomial formula for T[2,j]."""
    nonnegative_integer(derivative, "derivative")
    _, (e2, e4, e6) = cm_parameters(name)
    if derivative == 0:
        return mp.pi**2 * (e2 - 1) / 6
    polynomial_value = evaluate_rational_polynomial(
        ramanujan_polynomial(derivative), e2, e4, e6
    )
    return mp.pi**2 / 6 * (2 * mp.pi * mp.j) ** derivative * polynomial_value


def decimal(value, digits: int) -> str:
    return mp.nstr(value, digits, min_fixed=0, max_fixed=0)


def complex_decimal(value, digits: int) -> dict[str, str]:
    return {
        "real": decimal(mp.re(value), digits),
        "imaginary": decimal(mp.im(value), digits),
    }


def require(condition: bool, description: str) -> None:
    if not condition:
        raise AssertionError(description)


def exact_polynomial_records(maximum: int) -> list[dict]:
    records = []
    for j in range(maximum + 1):
        expression = ramanujan_polynomial(j)
        terms = []
        for powers, coefficient in sp.Poly(expression, X, Y, Z).terms():
            require(2 * powers[0] + 4 * powers[1] + 6 * powers[2] == 2 * j + 2,
                    f"P_{j} has an incorrect homogeneous weight")
            coefficient = sp.Rational(coefficient)
            terms.append({
                "powers_of_X_Y_Z": list(powers),
                "numerator": int(coefficient.p),
                "denominator": int(coefficient.q),
            })
        records.append({
            "j": j,
            "expression": str(sp.factor(expression)),
            "weight": 2 * j + 2,
            "terms": terms,
        })
    return records


def build_report(dps: int, rows: int) -> dict:
    """Run small independent checks and produce a JSON-serializable report."""
    with mp.workdps(dps):
        # Leave substantial guard digits in the published decimal strings.
        digits = max(20, dps - 20)
        relative_allowance = mp.power(10, -(dps - 15))

        # These compare two genuinely different numerical representations:
        # rational functions of q versus mpmath's complex polygamma routine.
        row_identity_checks = []
        tau = mp.mpf("0.37") + mp.j * mp.mpf("0.65")
        for weight, derivative, n in ((2, 0, 1), (2, 1, 2), (2, 2, 1), (4, 1, 2)):
            rational_row = row_summand(weight, derivative, n, tau)
            order = weight - 1 + derivative
            polygamma_row = n**derivative * (
                mp.polygamma(order, n * tau)
                + (-1)**derivative * mp.polygamma(order, 1 - n * tau)
            )
            error = abs(rational_row - polygamma_row)
            allowance = relative_allowance * max(1, abs(polygamma_row))
            require(error <= allowance, "single-row polygamma identity failed")
            row_identity_checks.append({
                "weight": weight, "j": derivative, "n": n,
                "tau": complex_decimal(tau, digits),
                "absolute_difference": decimal(error, digits),
                "floating_point_allowance": decimal(allowance, digits),
                "passed": True,
            })

        # CM formulas are checked against independent q-row summation. The
        # analytic tail is included explicitly in the comparison budget.
        cm_checks = []
        for name in ("i", "rho"):
            tau, _ = cm_parameters(name)
            for derivative in range(5):
                finite_sum = partial_row_sum(2, derivative, tau, rows)
                formula = cm_trigamma_jet(name, derivative)
                bound = row_tail_bound(2, derivative, tau, rows)
                difference = abs(finite_sum - formula)
                allowance = relative_allowance * max(1, abs(formula))
                require(difference <= bound + allowance,
                        f"CM identity failed at {name}, j={derivative}")
                cm_checks.append({
                    "CM_point": name,
                    "j": derivative,
                    "rows": rows,
                    "partial_sum": complex_decimal(finite_sum, digits),
                    "Ramanujan_CM_formula": complex_decimal(formula, digits),
                    "absolute_difference": decimal(difference, digits),
                    "analytic_tail_bound": decimal(bound, digits),
                    "floating_point_allowance": decimal(allowance, digits),
                    "passed": True,
                })

        # Evaluate the tail directly, avoiding subtraction of nearly equal
        # large sums. Bound the uncomputed tail after the reference cutoff.
        tail_checks = []
        samples = (
            (2, 0, mp.j, 4),
            (2, 4, cm_parameters("rho")[0], 4),
            (4, 1, mp.mpf("0.37") + mp.j * mp.mpf("0.48"), 5),
            (6, 3, mp.mpf("0.20") + mp.j * mp.mpf("1.20"), 3),
        )
        for weight, derivative, tau, cutoff in samples:
            reference_cutoff = cutoff + 50
            finite_tail = mp.fsum(
                row_summand(weight, derivative, n, tau)
                for n in range(cutoff + 1, reference_cutoff + 1)
            )
            reference_bound = row_tail_bound(weight, derivative, tau, reference_cutoff)
            bound = row_tail_bound(weight, derivative, tau, cutoff)
            upper_estimate = abs(finite_tail) + reference_bound
            ratio = upper_estimate / bound
            require(ratio <= 1 + relative_allowance,
                    f"tail majorant failed for weight={weight}, j={derivative}")
            tail_checks.append({
                "weight": weight, "j": derivative,
                "tau": complex_decimal(tau, digits),
                "cutoff": cutoff, "reference_cutoff": reference_cutoff,
                "finite_tail_magnitude": decimal(abs(finite_tail), digits),
                "reference_tail_bound": decimal(reference_bound, digits),
                "analytic_tail_bound": decimal(bound, digits),
                "upper_estimate_divided_by_bound": decimal(ratio, digits),
                "passed": True,
            })

        return {
            "description": "Regularized modular polygamma rows and their CM derivative jets",
            "precision_decimal_digits": dps,
            "numeric_status": (
                "Ordinary high-precision numerical verification; decimal values are not "
                "outward-rounded intervals. The article proves the exact formulas and bounds."
            ),
            "libraries": {"sympy": sp.__version__, "mpmath": mp.__version__},
            "definition": (
                "T[w,j](tau)=sum(n^j*(psi^(w-1+j)(n*tau)+"
                "(-1)^j*psi^(w-1+j)(1-n*tau)),n>=1), w even >=2"
            ),
            "row_formula": "(2*pi*i)^(w+j)*n^j*Li_(1-w-j)(exp(2*pi*i*n*tau))",
            "tail_bound": (
                "(2*pi)^(w+j)*(N+1)^j*Li_(-j)(r)/r*"
                "Li_(1-w-j)(r^(N+1)), r=exp(-2*pi*Im(tau))"
            ),
            "negative_polylogarithms": [
                {"order": order, "expression": str(sp.factor(negative_polylog_expression(order)))}
                for order in range(9)
            ],
            "Ramanujan_polynomials": exact_polynomial_records(5),
            "single_row_identity_checks": row_identity_checks,
            "CM_checks": cm_checks,
            "tail_checks": tail_checks,
            "summary": {
                "single_row_checks_passed": len(row_identity_checks),
                "CM_checks_passed": len(cm_checks),
                "tail_checks_passed": len(tail_checks),
                "all_checks_passed": True,
            },
        }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dps", type=int, default=90,
                        help="mpmath working precision (default: 90)")
    parser.add_argument("--rows", type=int, default=48,
                        help="paired rows in each CM comparison (default: 48)")
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parent.parent / "data" / "modular_rows.json")
    arguments = parser.parse_args()
    if arguments.dps < 30 or arguments.rows < 1:
        parser.error("--dps must be at least 30 and --rows must be positive")
    report = build_report(arguments.dps, arguments.rows)
    arguments.output.parent.mkdir(parents=True, exist_ok=True)
    arguments.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"output": str(arguments.output), **report["summary"]}, indent=2))


if __name__ == "__main__":
    main()
