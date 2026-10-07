#!/usr/bin/env python3
"""Exact parameter diagnostics for the Section 14--15 composition.

The general statements are proved in the article. This companion checks
independent recurrence evaluations, exponent identities, finite exact
instances of the selection budget, and the governing field-size branches
in the examples. Decimal logarithms are illustrative; branch comparisons
use integers only. No Lean verification is performed or claimed.
"""

from __future__ import annotations

import argparse
from decimal import Decimal, localcontext
from fractions import Fraction
import json
from math import comb
from pathlib import Path


def ceil_fraction(value: Fraction) -> int:
    return -(-value.numerator // value.denominator)


def ceil_nth_root(value: int, degree: int) -> int:
    """Return the least integer x with x**degree >= value, exactly."""
    if value <= 1 or degree == 1:
        return value
    x = 1 << ((value.bit_length() + degree - 1) // degree)
    while True:
        y = ((degree - 1) * x + value // x ** (degree - 1)) // degree
        if y >= x:
            break
        x = y
    return x if x**degree == value else x + 1


def dimensions(k: int) -> tuple[list[int], list[int]]:
    dims = [16 * sum(comb(k, j) for j in range(t + 1)) - comb(k, t)
            for t in range(k + 1)]
    collision = 120 * 3**k
    weights = [1 + int(t == 1) + collision * int(t == k)
               for t in range(k + 1)]
    return dims, weights


def compare_binary_products(a: int, exponent_a: int,
                            b: int, exponent_b: int) -> int:
    """Compare a*2**exponent_a and b*2**exponent_b without huge shifts."""
    bits_a = a.bit_length() + exponent_a
    bits_b = b.bit_length() + exponent_b
    if bits_a != bits_b:
        return (bits_a > bits_b) - (bits_a < bits_b)
    baseline = min(exponent_a, exponent_b)
    left = a << (exponent_a - baseline)
    right = b << (exponent_b - baseline)
    return (left > right) - (left < right)


def branch_compare(k: int, binary_bandwidth_exponent: int,
                   t: int, u: int) -> int:
    """Exact comparison of threshold branches at beta=gamma=1/2.

    The bandwidth is L=(s+1)*2**binary_bandwidth_exponent.
    Branch t is [2(k+1)a_t * 2**15 * L**D_t]**(1/(t+1)).
    We raise branches t and u to the common power (t+1)(u+1).
    """
    dims, weights = dimensions(k)
    s = 16 * 2**k
    power_t = u + 1
    power_u = t + 1
    coeff_t = ((2 * (k + 1) * weights[t])**power_t
               * (s + 1)**(dims[t] * power_t))
    coeff_u = ((2 * (k + 1) * weights[u])**power_u
               * (s + 1)**(dims[u] * power_u))
    exponent_t = (15 + binary_bandwidth_exponent * dims[t]) * power_t
    exponent_u = (15 + binary_bandwidth_exponent * dims[u]) * power_u
    return compare_binary_products(coeff_t, exponent_t,
                                   coeff_u, exponent_u)


def branch_log2(k: int, binary_bandwidth_exponent: int, t: int) -> Decimal:
    dims, weights = dimensions(k)
    s = 16 * 2**k
    with localcontext() as context:
        context.prec = 80
        log_two = Decimal(2).ln()
        log_bandwidth = (Decimal(binary_bandwidth_exponent)
                         + Decimal(s + 1).ln() / log_two)
        log_coefficient = Decimal(2 * (k + 1) * weights[t]).ln() / log_two
        return +(log_coefficient + 15 + dims[t] * log_bandwidth) / (t + 1)


def example(k: int, variant: str) -> dict[str, object]:
    s = 16 * 2**k
    if variant == "new":
        beta_exponent = 22 * 4**k
        gamma_exponent = 88 * 4**k - 32 * 2**k
    elif variant == "source15":
        beta_exponent = 22 * 4**k
        gamma_exponent = 44 * k * 4**k + 56 * 2**k
    elif variant == "gowers_source35_input":
        beta_exponent = 28 * 4**k
        gamma_exponent = 84 * k * 4**k
    else:
        raise ValueError(variant)
    a = beta_exponent - 15
    exponent = 44 + a + gamma_exponent
    best = 0
    for t in range(1, k + 1):
        if branch_compare(k, exponent, t, best) > 0:
            best = t
    assert all(branch_compare(k, exponent, best, t) >= 0
               for t in range(k + 1))
    with localcontext() as context:
        context.prec = 80
        log_l = Decimal(exponent) + Decimal(s + 1).ln() / Decimal(2).ln()
        count_cost = (Decimal(44 * (s - 1) + 1)
                      + s * Decimal(s + 2).ln() / Decimal(2).ln()
                      + s * a + 15 + s * gamma_exponent)
    return {
        "k": k,
        "variant": variant,
        "beta": "1/2",
        "gamma": "1/2",
        "eta": "2^-44",
        "A": a,
        "g": gamma_exponent,
        "s": s,
        "governing_branch_exact": best,
        "bandwidth_binary_exponent_exact": exponent,
        "bandwidth_odd_factor_exact": s + 1,
        "log2_bandwidth_illustrative": f"{log_l:.12f}",
        "log2_field_threshold_illustrative":
            f"{branch_log2(k, exponent, best):.12f}",
        "negative_log2_retention_factor_illustrative": f"{count_cost:.12f}",
        "retained_beta_exponent_exact": s * a + 15,
        "retained_gamma_exponent_exact": s * gamma_exponent,
    }


def exact_budget_case(k: int, alpha: Fraction,
                      beta: Fraction, eta: Fraction) -> None:
    """Check all arithmetic in the explicit prior-selector consequence."""
    s = 16 * 2**k
    dims, weights = dimensions(k)
    bandwidth = ceil_fraction(Fraction(s + 1) / (alpha * eta))
    branch_powers = [Fraction(2 * (k + 1) * weights[t])
                     * beta**(-15) * bandwidth**dims[t]
                     for t in range(k + 1)]
    q = max(ceil_nth_root(ceil_fraction(value), t + 1)
            for t, value in enumerate(branch_powers))
    for t, value in enumerate(branch_powers):
        assert q**(t + 1) >= value
        if q > 1 and q == ceil_nth_root(ceil_fraction(value), t + 1):
            assert (q - 1)**(t + 1) < value
    upper_budget = sum(Fraction(weights[t] * bandwidth**dims[t],
                                q**(t + 1))
                       for t in range(k + 1))
    assert upper_budget <= beta**15 / 2
    signal = Fraction(bandwidth**s
                      + 2 * sum(u**s for u in range(1, bandwidth)),
                      bandwidth**s)
    assert signal >= Fraction(2 * bandwidth, s + 1)
    score_lower = alpha * eta * signal - (1 - alpha) - beta**(-15) * upper_budget
    assert score_lower > Fraction(1, 2)
    assert Fraction(1, 2) / (eta * bandwidth**s) >= (
        alpha**s * eta**(s - 1) / (2 * (s + 2)**s))
    assert Fraction(1, 1 + eta) >= 1 - eta
    assert q > 2 * (bandwidth - 1)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1]
                        / "data" / "parameter_checks.json")
    args = parser.parse_args()

    recurrence_cases = 0
    coupling_cases = 0
    pair_exponent = 0
    config_exponent = 0
    for k in range(1, 21):
        pair_exponent = 4 * pair_exponent + 8 * 2**(k - 1)
        config_exponent = 4 * config_exponent + 8 * 3**(k - 1)
        assert pair_exponent == 4 * (4**k - 2**k)
        assert config_exponent == 8 * (4**k - 3**k)
        assert pair_exponent <= config_exponent <= 2 * k * 4**k
        recurrence_cases += 1
        for d in range(2, 13):
            coupled = (3 * d - 2) * pair_exponent + 8 * (d - 1) * 2**k
            closed = (12 * d - 8) * 4**k - 4 * d * 2**k
            old = (6 * d - 4) * k * 4**k + 8 * (d - 1) * 2**k
            delta = (6 * d - 4) * ((k - 2) * 4**k + 2**(k + 1))
            assert coupled == closed
            assert old - closed == delta
            assert delta == 0 if k == 1 else delta > 0
            coupling_cases += 1
        s = 16 * 2**k
        a = 22 * 4**k - 15
        g = 88 * 4**k - 32 * 2**k
        assert a > 0 and g > 0
        assert s * g == 1408 * 8**k - 512 * 4**k
        assert s * (44 * k * 4**k + 56 * 2**k) == (
            704 * k * 8**k + 896 * 4**k)
        assert 6 * s * 4**k == 96 * 8**k

    budget_cases = 0
    for k in (1, 2, 3):
        for alpha in (Fraction(1, 2), Fraction(1, 3)):
            for beta in (Fraction(1, 2), Fraction(2, 3)):
                for eta in (Fraction(1, 2), Fraction(1, 5)):
                    exact_budget_case(k, alpha, beta, eta)
                    budget_cases += 1

    samples = [example(k, variant)
               for k in (2, 3)
               for variant in ("new", "source15", "gowers_source35_input")]
    dims_two, _ = dimensions(2)
    dims_three, _ = dimensions(3)
    assert dims_two == [15, 46, 63]
    assert dims_three == [15, 61, 109, 127]
    assert max(Fraction(d, t + 1) for t, d in enumerate(dims_two)) == 23
    assert max(Fraction(d, t + 1) for t, d in enumerate(dims_three)) == Fraction(109, 3)
    for record in samples:
        assert record["governing_branch_exact"] == record["k"] - 1

    # At beta=gamma=1/2 the odd bandwidth factor is identical, so
    # these logarithmic differences are exact rational numbers.
    threshold_savings = {}
    for k in (2, 3):
        dims, _ = dimensions(k)
        t = k - 1
        delta_g = 44 * ((k - 2) * 4**k + 2**(k + 1))
        saving = Fraction(dims[t] * delta_g, t + 1)
        threshold_savings[str(k)] = {
            "log2_bandwidth_saving_exact": delta_g,
            "log2_field_threshold_saving_exact": str(saving),
            "log2_monomial_count_gain_exact": 16 * 2**k * delta_g,
        }
    assert threshold_savings["2"] == {
        "log2_bandwidth_saving_exact": 352,
        "log2_field_threshold_saving_exact": "8096",
        "log2_monomial_count_gain_exact": 22528,
    }

    result = {
        "status": "all exact diagnostics passed",
        "scope": "finite diagnostics; general proofs are in the article",
        "recurrence_cases": recurrence_cases,
        "coupling_cases": coupling_cases,
        "exact_selection_budget_cases": budget_cases,
        "examples": samples,
        "source15_comparison": threshold_savings,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
