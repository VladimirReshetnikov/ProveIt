"""Report155: exact arithmetic for A192561 and its Fock certificate.

Python standard library only. No computation, file writes, or global interpreter
configuration occur on import. Validation remains active under python -O.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
from math import comb, factorial
import sys

from safe_io import InputError, read_json, require, write_new_json

MAX_N = 20
MAX_K = 96
MAX_BISECTIONS = 64
MAX_EXP_TERMS = 192
MAX_ORDER = 10
MAX_ENUMERATION_N = 1000
DEFAULT_SPEC = {"n": 10, "K": 80, "bisections": 48, "exp_terms": 140}


def bounded_int(value, low, high, label):
    require(type(value) is int and low <= value <= high,
            f"{label} must be an integer in [{low}, {high}]")
    return value


def validate_spec(spec):
    require(type(spec) is dict, "Certificate input must be a JSON object")
    require(set(spec) == set(DEFAULT_SPEC),
            "Certificate fields must be exactly n, K, bisections, exp_terms")
    return {"n": bounded_int(spec["n"], 0, MAX_N, "n"),
            "K": bounded_int(spec["K"], 2, MAX_K, "K"),
            "bisections": bounded_int(spec["bisections"], 8, MAX_BISECTIONS,
                                       "bisections"),
            "exp_terms": bounded_int(spec["exp_terms"], 16, MAX_EXP_TERMS,
                                      "exp_terms")}


def decimal_integer(value):
    """Convert an integer without changing Python's integer-string limit."""
    require(type(value) is int, "Expected an integer")
    if value == 0:
        return "0"
    sign = "-" if value < 0 else ""
    value = abs(value)
    chunks = []
    while value:
        value, chunk = divmod(value, 1000000000)
        chunks.append(chunk)
    return sign + str(chunks[-1]) + "".join(f"{x:09d}" for x in reversed(chunks[:-1]))


def rational_json(value):
    value = Q(value)
    return {"numerator": decimal_integer(value.numerator),
            "denominator": decimal_integer(value.denominator)}



def decode_rational(payload):
    """Decode a stored rational without disabling Python's string safety limit.

    JSON endpoints use decimal strings. This bounded chunk parser handles their
    long exact numerator/denominator values without a process-wide setting.
    """
    require(type(payload) is dict and set(payload) == {"numerator", "denominator"},
            "Expected numerator/denominator object")
    def parse(text):
        require(type(text) is str and 1 <= len(text) <= 500000,
                "Rational integer text length is invalid")
        negative = text.startswith("-")
        digits = text[1:] if negative else text
        require(bool(digits) and digits.isascii() and digits.isdecimal(),
                "Rational integer text must be ASCII decimal")
        require(digits == "0" or not digits.startswith("0"),
                "Rational integer text must be canonical")
        require(not (negative and digits == "0"), "Negative zero is refused")
        value = 0
        for start in range(0, len(digits), 9):
            part = digits[start:start + 9]
            value = value * (10 ** len(part)) + int(part)
        return -value if negative else value
    numerator = parse(payload["numerator"])
    denominator = parse(payload["denominator"])
    require(denominator > 0, "Rational denominator must be positive")
    value = Q(numerator, denominator)
    require(value.numerator == numerator and value.denominator == denominator,
            "Rational payload must be in lowest terms")
    return value


def short_rational(value):
    value = Q(value)
    return (decimal_integer(value.numerator) if value.denominator == 1 else
            decimal_integer(value.numerator) + "/" + decimal_integer(value.denominator))


def floor_q(value):
    return value.numerator // value.denominator


def ceil_q(value):
    return -((-value.numerator) // value.denominator)


def decimal_bound(value, places=30, upper=False):
    """A fixed-place outward decimal, computed with integer division only."""
    bounded_int(places, 0, 100, "decimal places")
    scale = 10 ** places
    rounded = ceil_q(value * scale) if upper else floor_q(value * scale)
    sign = "-" if rounded < 0 else ""
    digits = decimal_integer(abs(rounded)).rjust(places + 1, "0")
    return sign + (digits[:-places] + "." + digits[-places:] if places else digits)


def stirling_count(n):
    """b_n = sum_k [n+1,k+1]^2 k!, by unsigned Stirling recurrence."""
    bounded_int(n, 0, MAX_ENUMERATION_N, "enumeration n")
    row = [1]
    for size in range(1, n + 2):
        old = row
        row = [0] * (size + 1)
        for k in range(1, size + 1):
            row[k] = old[k - 1] + ((size - 1) * old[k] if k < len(old) else 0)
    return sum(row[k + 1] ** 2 * factorial(k) for k in range(n + 1))


def saddle_residual(n, center):
    return sum((Q(1, 1) / (j + center) for j in range(1, n + 1)), Q(0)) - center


def upper_saddle_center(n, bisections):
    bounded_int(n, 1, MAX_N, "center n")
    bounded_int(bisections, 8, MAX_BISECTIONS, "bisections")
    lower, upper = Q(0), Q(n)
    # g is strictly decreasing; g(0)>0 and g(n)<0.
    for _ in range(bisections):
        midpoint = (lower + upper) / 2
        if saddle_residual(n, midpoint) > 0:
            lower = midpoint
        else:
            upper = midpoint
    require(saddle_residual(n, lower) >= 0 and saddle_residual(n, upper) <= 0,
            "Root bracket sign invariant failed")
    return lower, upper


def exp_bounds(x, terms):
    """Rational lower/upper bounds on exp(x), no binary floating point.

    For x>=0, truncate at m=terms and bound the remaining positive series by
    t_(m+1)/(1-x/(m+2)). For x<0 invert the positive-x interval.
    """
    require(type(x) in (int, Q), "Exponential input must be exact rational")
    x = Q(x)
    bounded_int(terms, 16, MAX_EXP_TERMS, "exp_terms")
    require(abs(x) <= 64 and abs(x) < terms + 2,
            "Exponential argument exceeds the bounded Taylor domain")
    if x < 0:
        lower, upper = exp_bounds(-x, terms)
        return 1 / upper, 1 / lower
    term = total = Q(1)
    for j in range(1, terms + 1):
        term *= x / j
        total += term
    next_term = term * x / (terms + 1)
    upper = total + next_term / (1 - x / (terms + 2))
    return total, upper


def compare_threshold(lower, upper, threshold, exact_value=None):
    """Strict interval decisions; equality is resolved only by an exact integer."""
    require(type(lower) in (int, Q) and type(upper) in (int, Q),
            "Threshold interval endpoints must be exact")
    require(lower <= upper and type(threshold) is int,
            "Invalid threshold interval or noninteger threshold")
    if exact_value is not None:
        require(type(exact_value) is int and lower <= exact_value <= upper,
                "Exact value is not an integer inside the interval")
        return "equal" if exact_value == threshold else (
            "strictly_below" if exact_value < threshold else "strictly_above")
    if upper < threshold:
        return "strictly_below"
    if lower > threshold:
        return "strictly_above"
    return "undecided"


def certificate_bounds(spec):
    """Return exact Fraction endpoints and exact finite auxiliary quantities."""
    spec = validate_spec(spec)
    n, K = spec["n"], spec["K"]
    if n == 0:
        return {"lower": Q(1), "upper": Q(1), "exact": 1, "n_zero": True}
    bracket_lower, b = upper_saddle_center(n, spec["bisections"])
    reciprocals = [Q(1) / (j + b) for j in range(1, n + 1)]
    moments = [Q(n)] + [sum((x ** r for x in reciprocals), Q(0))
                         for r in range(1, K)]
    # K=2 still needs S_2 for the tail bound, though not for c_0,c_1.
    s = sum((x * x for x in reciprocals), Q(0))
    d = moments[1] - b
    q = Q(K, K + 1)
    require(d <= 0, "Center must be an upper endpoint")
    require(0 < s < q < 1, "Fock-tail scaling condition failed")
    coefficients = [Q(1), d]
    for k in range(2, K):
        coefficients.append((d * coefficients[k - 1] + sum(
            ((-1) ** (r - 1) * moments[r] * coefficients[k - r]
             for r in range(2, k + 1)), Q(0))) / k)
    C = sum((factorial(k) * c * c for k, c in enumerate(coefficients)), Q(0))
    P = Q(1)
    for j in range(1, n + 1):
        P *= 1 + b / j
    tail_factor = (s / q) ** K / (1 - q)
    tail_exponent = q * d * d / (s * (1 - q))
    exp_lower, exp_upper = exp_bounds(-b * b, spec["exp_terms"])
    _, tail_exp_upper = exp_bounds(tail_exponent - b * b, spec["exp_terms"])
    scale = factorial(n) ** 2 * P * P
    lower = scale * C * exp_lower
    upper = scale * (C * exp_upper + tail_factor * tail_exp_upper)
    exact = stirling_count(n)
    require(0 < lower <= exact <= upper, "Exact enumeration is outside certificate")
    return {"lower": lower, "upper": upper, "exact": exact, "n_zero": False,
            "root_lower": bracket_lower, "root_upper": b, "center": b,
            "S2": s, "d": d, "q": q, "partial_fock_norm": C,
            "tail_factor": tail_factor, "tail_exponent": tail_exponent,
            "scale": scale}


def certificate_document(spec):
    spec = validate_spec(spec)
    result = certificate_bounds(spec)
    lower, upper, exact = result["lower"], result["upper"], result["exact"]
    candidate_low, candidate_high = ceil_q(lower), floor_q(upper)
    unique = candidate_low == candidate_high
    if unique:
        require(candidate_low == exact, "Unique integer disagrees with enumeration")
    doc = {"schema": "report155.exact-fock-certificate.v1", "inputs": spec,
           "arithmetic": "Python integers and fractions.Fraction; no floating-point decisions",
           "interval": {"lower": rational_json(lower), "upper": rational_json(upper),
                        "width": rational_json(upper - lower),
                        "decimal_places": 30,
                        "lower_decimal_outward": decimal_bound(lower),
                        "upper_decimal_outward": decimal_bound(upper, upper=True),
                        "width_decimal_upper": decimal_bound(upper - lower, upper=True)},
           "integer_decision": {"ceil_lower": decimal_integer(candidate_low),
                                "floor_upper": decimal_integer(candidate_high),
                                "unique_integer_certified": unique,
                                "unique_integer": decimal_integer(candidate_low) if unique else None},
           "independent_enumeration": {"b_n": decimal_integer(exact),
                                      "inside_interval": True},
           "n_zero_special_case": result["n_zero"]}
    if not result["n_zero"]:
        # Store the finite ingredients as well as the endpoints for exact replay.
        keys = ("root_lower", "root_upper", "center", "S2", "d", "q",
                "partial_fock_norm", "tail_factor", "tail_exponent", "scale")
        doc["rational_ingredients"] = {key: rational_json(result[key]) for key in keys}
        doc["q_scope"] = ("q=K/(K+1) is universally admissible for K>=2 with the "
                          "upper-root-endpoint center; it need not minimize the tail bound when d!=0")
    return doc


# Ascending-coefficient polynomial arithmetic, all coefficients exact Fractions.
def poly_add(left, right):
    out = [Q(0)] * max(len(left), len(right))
    for k, value in enumerate(left):
        out[k] += value
    for k, value in enumerate(right):
        out[k] += value
    return poly_trim(out)


def poly_trim(poly):
    while len(poly) > 1 and poly[-1] == 0:
        poly.pop()
    return poly


def poly_scale(poly, scalar):
    return poly_trim([x * scalar for x in poly])


def poly_mul(left, right):
    out = [Q(0)] * (len(left) + len(right) - 1)
    for i, x in enumerate(left):
        for j, y in enumerate(right):
            out[i + j] += x * y
    return poly_trim(out)


def fock_inner(left, right):
    return sum((factorial(k) * left[k] * right[k]
                for k in range(min(len(left), len(right)))), Q(0))


def bernoulli_numbers(order):
    """B_0=1 and sum_{k=0}^{m} binom(m+1,k) B_k=0; hence B_1=-1/2."""
    bounded_int(order, 0, MAX_ORDER + 1, "Bernoulli order")
    values = [Q(1)]
    for m in range(1, order + 1):
        values.append(-sum((comb(m + 1, k) * values[k] for k in range(m)), Q(0))
                      / (m + 1))
    return values


def coefficient_data(order=10):
    bounded_int(order, 0, MAX_ORDER, "coefficient order")
    bernoulli = bernoulli_numbers(order + 1)
    g = [[Q(0)]]
    for m in range(1, order + 1):
        polynomial = [Q(0)] + [comb(m + 1, k) * bernoulli[m + 1 - k]
                                for k in range(1, m + 2)]
        g.append(poly_scale(polynomial, Q((-1) ** m, m * (m + 1))))
    p = [[Q(1)]]
    for r in range(1, order + 1):
        poly = [Q(0)]
        for m in range(1, r + 1):
            poly = poly_add(poly, poly_scale(poly_mul(g[m], p[r - m]), Q(m, r)))
        p.append(poly)
    H = [sum((fock_inner(p[j], p[r - j]) for j in range(r + 1)), Q(0))
         for r in range(order + 1)]
    log_E = [Q(0)] * (order + 1)
    for r in range(1, order + 1, 2):
        log_E[r] = -2 * bernoulli[r + 1] / ((r + 1) * r)
    E = [Q(1)]
    for r in range(1, order + 1):
        E.append(sum((m * log_E[m] * E[r - m] for m in range(1, r + 1)), Q(0)) / r)
    A = [sum((E[j] * H[r - j] for j in range(r + 1)), Q(0))
         for r in range(order + 1)]
    return {"g": g, "p": p, "H": H, "log_E": log_E, "E": E, "A": A}


def coefficient_document(order=10):
    data = coefficient_data(order)
    return {"schema": "report155.fock-asymptotic-coefficients.v1", "order": order,
            "bernoulli_convention": "B1=-1/2; B1(t)=t-1/2",
            "polynomial_encoding": "ascending powers of t; canonical rational strings",
            "gamma_ratio_log_polynomials": [[short_rational(x) for x in p] for p in data["g"]],
            "gamma_ratio_polynomials": [[short_rational(x) for x in p] for p in data["p"]],
            "fock_norm_coefficients": [short_rational(x) for x in data["H"]],
            "stirling_log_coefficients": [short_rational(x) for x in data["log_E"]],
            "stirling_factor_coefficients": [short_rational(x) for x in data["E"]],
            "normalized_coefficients": [short_rational(x) for x in data["A"]]}


def cli_int(text):
    require(len(text) <= 8 and text.isascii() and text.isdecimal(),
            "CLI integer must contain 1 to 8 ASCII decimal digits")
    return int(text)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    cert = sub.add_parser("certificate", help="exact rational Fock interval")
    cert.add_argument("--input", required=True, help="strict certificate JSON")
    cert.add_argument("--output", required=True, help="fresh .json destination")
    coeff = sub.add_parser("coefficients", help="generate exact A_0 through A_order")
    coeff.add_argument("--order", default="10")
    coeff.add_argument("--output", required=True)
    enum = sub.add_parser("enumerate", help="unsigned Stirling exact enumeration")
    enum.add_argument("--n", required=True)
    enum.add_argument("--output", required=True)
    args = parser.parse_args(argv)
    try:
        if args.command == "certificate":
            result = certificate_document(read_json(args.input))
        elif args.command == "coefficients":
            result = coefficient_document(cli_int(args.order))
        else:
            n = bounded_int(cli_int(args.n), 0, MAX_ENUMERATION_N, "enumeration n")
            result = {"schema": "report155.stirling-enumeration.v1", "n": n,
                      "b_n": decimal_integer(stirling_count(n))}
        write_new_json(args.output, result)
    except (InputError, OSError, ValueError, OverflowError, RecursionError) as exc:
        parser.exit(2, "error: " + str(exc) + "\n")
    print("Wrote " + args.output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
