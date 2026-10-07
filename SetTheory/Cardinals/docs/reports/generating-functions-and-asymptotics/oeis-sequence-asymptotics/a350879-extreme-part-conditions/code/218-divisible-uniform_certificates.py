#!/usr/bin/env python3
"""Exact endpoint certificates for the uniform reciprocal-minimum bound.

Only integer and Fraction arithmetic is used. Analytic identities and
monotonicity extend the finite endpoint comparisons to all n>=90; the
article supplies those proofs. These checks are not numerical sampling.
"""
from fractions import Fraction as F
from math import factorial
import argparse
import json


def _require(condition, message):
    if not condition:
        raise RuntimeError("Certificate failed: " + message)


def _integer(value, name, minimum=1):
    if type(value) is not int:
        raise TypeError(f"{name} must be an integer, excluding bool")
    if value < minimum:
        raise ValueError(f"{name} must be at least {minimum}")


def _rational(value, name):
    if type(value) not in (int, F):
        raise TypeError(f"{name} must be an int or Fraction, excluding bool")
    return F(value)


def arctan_bounds(x, terms):
    """Strict rational lower/upper bounds from successive alternating sums.

    The domain is 0<x<1; terms is the positive number of terms in the
    first partial sum. The next partial sum lies on the opposite side.
    """
    x = _rational(x, "x")
    _integer(terms, "terms")
    if not 0 < x < 1:
        raise ValueError("x must satisfy 0<x<1")
    partial = sum((F((-1) ** j, 2 * j + 1) * x ** (2 * j + 1)
                   for j in range(terms)), F(0))
    following = partial + F((-1) ** terms, 2 * terms + 1) * x ** (2 * terms + 1)
    return min(partial, following), max(partial, following)


def e_bounds(degree=6):
    """Strict rational bounds on e from positive series and a geometric tail.

    The lower bound is the sum through (degree-1)!. The upper bound is
    the sum through degree!, plus the tail starting at 1/(degree+1)!
    with all subsequent ratios bounded by 1/(degree+2).
    """
    _integer(degree, "degree")
    lower = sum((F(1, factorial(j)) for j in range(degree)), F(0))
    upper = lower + F(1, factorial(degree))
    upper += F(1, factorial(degree + 1)) / (1 - F(1, degree + 2))
    return lower, upper


def _validation_checks():
    bad = [(arctan_bounds, (True, 2)), (arctan_bounds, (False, 2)),
           (arctan_bounds, ("1/5", 2)), (arctan_bounds, (None, 2)),
           (arctan_bounds, (0, 2)), (arctan_bounds, (1, 2)),
           (arctan_bounds, (F(-1, 5), 2)), (arctan_bounds, (F(6, 5), 2)),
           (arctan_bounds, (F(1, 5), True)), (arctan_bounds, (F(1, 5), F(2))),
           (arctan_bounds, (F(1, 5), 0)), (arctan_bounds, (F(1, 5), -1)),
           (e_bounds, (True,)), (e_bounds, (False,)), (e_bounds, (F(6),)),
           (e_bounds, ("6",)), (e_bounds, (0,)), (e_bounds, (-1,))]
    for function, args in bad:
        try:
            function(*args)
        except (TypeError, ValueError):
            pass
        else:
            raise RuntimeError("Invalid input accepted by " + function.__name__)
    try:
        _require(False, "negative guard probe")
    except RuntimeError as exc:
        _require(str(exc) == "Certificate failed: negative guard probe", "guard probe message")
    else:
        raise RuntimeError("Certificate guard was disabled")
    return len(bad)


def endpoint_certificates():
    """Regenerate 19 exact endpoint comparisons, with deterministic receipts."""
    invalid_count = _validation_checks()
    a5_lower, a5_upper = arctan_bounds(F(1, 5), 2)
    a239_lower, a239_upper = arctan_bounds(F(1, 239), 1)
    # Machin's exact identity: pi=16 arctan(1/5)-4 arctan(1/239).
    pi_lower = 16 * a5_lower - 4 * a239_upper
    pi_upper = 16 * a5_upper - 4 * a239_lower
    e_lower, e_upper = e_bounds()
    onset = F(22, 7) ** 2 * F(87, 32) ** 4 / 6 + F(1, 24)
    w_lower = F(25, 8) ** 2 * F(163, 60) ** 2 / 3
    p_ratio = 1 - F(1, 24) - 768 * F(3, 8) ** 12
    comparisons = [
        ("pi_lower", F(25, 8), "<", pi_lower),
        ("pi_upper", pi_upper, "<", F(22, 7)),
        ("pi_square_upper", F(22, 7) ** 2, "<", F(10)),
        ("e_lower_value", e_lower, "=", F(163, 60)),
        ("e_lower_coarse", F(8, 3), "<", e_lower),
        ("e_upper", e_upper, "<", F(87, 32)),
        ("onset_rational_value", onset, "=", F(6935272345, 77070336)),
        ("onset_before_90", onset, "<", F(90)),
        ("w_exceeds_24", F(24), "<", w_lower),
        ("partition_ratio_exceeds_half", F(1, 2), "<", p_ratio),
        ("e_cubed_exceeds_ten", F(10), "<", F(8, 3) ** 3),
        ("eta_product_log_upper", F(10, 81), "<", F(1, 2)),
        ("cutoff_x_cube_exceeds_27", F(27), "<", F(3, 4) * 9 * F(8, 3) ** 2),
        ("cutoff_tx_cube_below_one", F(3, 4) * 10 * F(3, 8) ** 4, "<", F(1)),
        ("kappa_cube_over_eight_below_two", F(3, 16) * 10, "<", F(2)),
        ("positive_cosine_Taylor_factor", 4 * F(22, 7) ** 2 / 9, "<", F(12)),
        ("delta_first_cube", F(20, 9) * F(3, 8) ** 4, "<", F(9, 25) ** 3),
        ("delta_second_cube", F(3200, 2187) * F(3, 8) ** 2, "<", F(3, 5) ** 3),
        ("delta_fraction_sum_below_one", F(9, 25) + F(3, 5), "<", F(1)),
    ]
    _require(w_lower == F(664225, 27648), "w lower rational value")
    rows = []
    for name, lhs, relation, rhs in comparisons:
        _require(lhs < rhs if relation == "<" else lhs == rhs, name)
        rows.append({"name": name, "lhs": str(lhs), "relation": relation,
                     "rhs": str(rhs), "status": "passed"})
    _require(len(rows) == 19, "endpoint certificate count")
    return {"schema": "uniform-reciprocal-minimum-endpoints-v1", "status": "passed",
            "onset_n": 90, "endpoint_comparisons": rows, "endpoint_count": len(rows),
            "invalid_input_tests": invalid_count, "negative_guard_probe": "passed",
            "pi_strict_enclosure": [str(pi_lower), str(pi_upper)],
            "e_strict_enclosure": [str(e_lower), str(e_upper)],
            "onset_upper": str(onset), "w_lower": str(w_lower),
            "partition_ratio_lower": str(p_ratio),
            "scope": "Exact endpoint inequalities; all-parameter extension uses the article's analytic identities and monotonicity proofs"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--negative-probe", action="store_true",
                        help="deliberately fail the certificate guard before running any certificates")
    args = parser.parse_args()
    if args.negative_probe:
        _require(False, "deliberate false-check negative probe")
    print(json.dumps(endpoint_certificates(), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
