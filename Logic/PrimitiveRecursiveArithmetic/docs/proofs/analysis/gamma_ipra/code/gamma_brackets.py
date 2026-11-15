#!/usr/bin/env python3
"""Exact rational enclosures of Gamma at positive rational arguments.

Mathematical dependency
----------------------
For 0 < r <= 1 and n >= 1, the Bohr--Mollerup/Euler bracket theorem proves

  A_n(r) = n! n**r / (r (r+1) ... (r+n))
       <= Gamma(r) <=
  B_n(r) = (n-1)! n**r / (r (r+1) ... (r+n-1)),

and 0 <= B_n(r)-A_n(r) <= 1/n.  Gamma(x+1)=x Gamma(x)
then transfers these brackets to every positive rational x.

This module implements those finite expressions using integers and
fractions only.  The only nonrational factor, n**r, is enclosed by bounded
integer-root bisection.  The returned root certificate is the exact pair
of inequalities k**q <= n**p * 2**(q*precision) < (k+1)**q.

All loops have explicit finite lengths.  No floating-point, mpmath,
unbounded search, numerical integration, or numerical Gamma oracle is
used.  The certificate checks validate the arithmetic implementation;
they do not replace the mathematical bracket theorem, constitute a
formal iPRA proof, or supply a universal proof checker.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path


def ceil_fraction(value: Fraction) -> int:
    """Ceiling using one exact integer division, including negative values."""
    return -((-value.numerator) // value.denominator)


def integer_root_floor(radicand: int, degree: int) -> tuple[int, int]:
    """Return floor(radicand**(1/degree)) and the fixed iteration budget."""
    if radicand < 0 or degree < 1:
        raise ValueError("Require a nonnegative radicand and positive degree")
    # This upper endpoint has upper**degree > radicand, including radicand=0.
    endpoint_bits = max(1, (radicand.bit_length() + degree - 1) // degree)
    lower, upper = 0, 1 << endpoint_bits
    budget = endpoint_bits + 1
    for _ in range(budget):
        if upper - lower > 1:
            middle = (lower + upper) // 2
            if middle**degree <= radicand:
                lower = middle
            else:
                upper = middle
    assert upper == lower + 1
    assert lower**degree <= radicand < upper**degree
    return lower, budget


def positive_rational_power_bracket(
    base: int, exponent: Fraction, precision: int
) -> tuple[Fraction, Fraction, dict[str, int | str]]:
    """Enclose base**exponent within a dyadic interval of width 2**-precision."""
    if base < 1 or exponent <= 0 or precision < 0:
        raise ValueError("Invalid positive rational power parameters")
    numerator, denominator = exponent.numerator, exponent.denominator
    radicand = base**numerator << (denominator * precision)
    root, iterations = integer_root_floor(radicand, denominator)
    lower = Fraction(root, 1 << precision)
    upper = Fraction(root + 1, 1 << precision)
    certificate: dict[str, int | str] = {
        "base": base,
        "exponent_numerator": numerator,
        "exponent_denominator": denominator,
        "dyadic_precision": precision,
        "radicand": str(radicand),
        "root_floor": str(root),
        "root_lower_power": str(root**denominator),
        "root_upper_power": str((root + 1)**denominator),
        "bisection_iteration_budget": iterations,
    }
    return lower, upper, certificate


def rational_json(value: Fraction) -> dict[str, str]:
    return {"numerator": str(value.numerator), "denominator": str(value.denominator)}


def rational_from_json(value: dict[str, str]) -> Fraction:
    return Fraction(int(value["numerator"]), int(value["denominator"]))


def directed_decimal(value: Fraction, digits: int, *, upward: bool) -> str:
    """Exact directed decimal rounding, returning digits after the point."""
    if digits < 0:
        raise ValueError("Decimal digits must be nonnegative")
    denominator = 10**digits
    scaled = value * denominator
    integer = ceil_fraction(scaled) if upward else scaled.numerator // scaled.denominator
    sign = "-" if integer < 0 else ""
    whole, fractional = divmod(abs(integer), denominator)
    return f"{sign}{whole}.{fractional:0{digits}d}" if digits else f"{sign}{whole}"


def gamma_bracket(x: Fraction, bits: int = 8, digits: int = 10) -> dict:
    """Produce and verify a Gamma(x) bracket of width at most 2**-bits."""
    if x <= 0 or bits < 0:
        raise ValueError("Require x > 0 and bits >= 0")

    # This is integer division on a rational input, never a real-floor test.
    shift = (x.numerator - 1) // x.denominator
    strip = x - shift
    assert 0 < strip <= 1
    scale = Fraction(1)
    for j in range(shift):
        scale *= strip + j
    assert scale > 0

    n = (1 << (bits + 2)) * max(1, ceil_fraction(scale))
    assert scale / n <= Fraction(1, 1 << (bits + 2))

    # coefficient_b = (n-1)! / (r (r+1) ... (r+n-1)).
    coefficient_b = 1 / strip
    for j in range(1, n):
        coefficient_b *= Fraction(j) / (strip + j)
    coefficient_a = coefficient_b * n / (strip + n)

    amplification = scale * coefficient_b
    # A coarse bit-length bound suffices; no logarithm or search is used.
    coefficient_ceiling = max(1, ceil_fraction(amplification))
    root_precision = bits + 3 + coefficient_ceiling.bit_length()
    assert amplification / (1 << root_precision) <= Fraction(1, 1 << (bits + 3))
    root_lower, root_upper, root_certificate = positive_rational_power_bracket(
        n, strip, root_precision
    )

    lower = scale * coefficient_a * root_lower
    upper = scale * coefficient_b * root_upper
    width = upper - lower
    target = Fraction(1, 1 << bits)
    assert 0 < lower <= upper
    # An additional exact check on the finite output; no Gamma values used.
    assert width <= target

    lower_decimal = directed_decimal(lower, digits, upward=False)
    upper_decimal = directed_decimal(upper, digits, upward=True)
    assert Fraction(lower_decimal) <= lower
    assert Fraction(upper_decimal) >= upper

    result = {
        "x": rational_json(x),
        "x_display": str(x),
        "bits": bits,
        "strip_argument": rational_json(strip),
        "integer_shift": shift,
        "recurrence_scale": rational_json(scale),
        "euler_index": n,
        "coefficient_a": rational_json(coefficient_a),
        "coefficient_b": rational_json(coefficient_b),
        "root_certificate": root_certificate,
        "lower": rational_json(lower),
        "upper": rational_json(upper),
        "width": rational_json(width),
        "target_width": rational_json(target),
        "display_lower": lower_decimal,
        "display_upper": upper_decimal,
        "display_decimal_digits": digits,
        "exact_root_certificate_passed": True,
        "exact_width_check_passed": True,
    }
    verify_record(result)
    return result


def verify_record(record: dict) -> None:
    """Recheck the stored finite certificate, independent of displayed decimals."""
    x = rational_from_json(record["x"])
    r = rational_from_json(record["strip_argument"])
    shift = int(record["integer_shift"])
    assert x == r + shift and 0 < r <= 1
    scale = Fraction(1)
    for j in range(shift):
        scale *= r + j
    assert scale == rational_from_json(record["recurrence_scale"])
    n = int(record["euler_index"])
    coefficient_b = 1 / r
    for j in range(1, n):
        coefficient_b *= Fraction(j) / (r + j)
    coefficient_a = coefficient_b * n / (r + n)
    assert coefficient_a == rational_from_json(record["coefficient_a"])
    assert coefficient_b == rational_from_json(record["coefficient_b"])

    certificate = record["root_certificate"]
    assert int(certificate["base"]) == n
    assert int(certificate["exponent_numerator"]) == r.numerator
    assert int(certificate["exponent_denominator"]) == r.denominator
    precision = int(certificate["dyadic_precision"])
    radicand = n**r.numerator << (r.denominator * precision)
    root = int(certificate["root_floor"])
    assert radicand == int(certificate["radicand"])
    assert root**r.denominator == int(certificate["root_lower_power"])
    assert (root + 1)**r.denominator == int(certificate["root_upper_power"])
    assert root**r.denominator <= radicand < (root + 1)**r.denominator

    lower = scale * coefficient_a * Fraction(root, 1 << precision)
    upper = scale * coefficient_b * Fraction(root + 1, 1 << precision)
    assert lower == rational_from_json(record["lower"])
    assert upper == rational_from_json(record["upper"])
    assert upper - lower == rational_from_json(record["width"])
    assert upper - lower <= Fraction(1, 1 << int(record["bits"]))
    assert Fraction(record["display_lower"]) <= lower
    assert Fraction(record["display_upper"]) >= upper


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bits", type=int, default=8)
    parser.add_argument("--digits", type=int, default=10)
    parser.add_argument("--output", type=Path, default=Path("gamma_brackets.json"))
    parser.add_argument("--validation", type=Path, default=Path("validation.txt"))
    args = parser.parse_args()
    sample_arguments = [Fraction(t) for t in ("1/3", "1/2", "2/3", "1", "3/2", "2", "5/2", "3")]
    records = [gamma_bracket(x, args.bits, args.digits) for x in sample_arguments]
    document = {
        "format": "gamma-ipra-exact-brackets-v1",
        "arithmetic": "Python integers and fractions.Fraction; no floating point",
        "dependency": "Proved Euler/Bohr-Mollerup strip brackets and gamma recurrence",
        "scope": "Finite exact arithmetic certificates; not a formal iPRA proof checker",
        "samples": records,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(document, indent=2) + "\n", encoding="utf-8")
    # Parse the serialized artifact and verify every exact certificate again.
    reread = json.loads(args.output.read_text(encoding="utf-8"))
    for record in reread["samples"]:
        verify_record(record)

    lines = [
        "EXACT RATIONAL GAMMA ENCLOSURES",
        "",
        f"Requested exact bracket width: <= 2^(-{args.bits})",
        "All root certificates and output-width inequalities checked with integers.",
        "Displayed decimal endpoints are rounded outward from the exact fractions.",
        "No floating point or external numerical gamma values were used.",
        "",
    ]
    for record in records:
        lines.append(
            f"Gamma({record['x_display']}) in "
            f"[{record['display_lower']}, {record['display_upper']}] "
            f"(n={record['euler_index']}; exact certificates PASS)"
        )
    lines += [
        "",
        "The interval-enclosure interpretation uses the proved Euler strip-bracket",
        "theorem and recurrence. Finite samples do not prove any universal gamma",
        "identity and are not a completed Lean or iPRA formalization.",
    ]
    args.validation.parent.mkdir(parents=True, exist_ok=True)
    args.validation.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
