#!/usr/bin/env python3
"""Exact rational certificates for the constructive Bohr--Mollerup brackets.

This is a reference artifact, not the Lean formalization.  It implements the
finite arithmetic used by the paper.  For a positive rational x, it returns a
rational interval known (by the proved Euler squeeze) to contain the
constructive Gamma value.

The implementation intentionally uses only integer arithmetic, Fraction,
finite products, and bounded bisection of an integer root.  No floating-point
number is used in certificate verification.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass, asdict
from fractions import Fraction
from math import factorial
from pathlib import Path
from typing import Any


def parse_fraction(text: str) -> Fraction:
    text = text.strip()
    if "/" in text:
        p, q = text.split("/", 1)
        return Fraction(int(p), int(q))
    return Fraction(int(text), 1)


def frac_text(x: Fraction) -> str:
    return f"{x.numerator}/{x.denominator}"


def frac_from_text(text: str) -> Fraction:
    return parse_fraction(text)


def ceil_fraction(x: Fraction) -> int:
    return -((-x.numerator) // x.denominator)


def ceil_log2_fraction(x: Fraction) -> int:
    """Least j >= 0 with 2**j >= x, for x > 0.

    The search has an explicit bit-length bound, so this reference routine
    mirrors a primitive-recursive bounded search rather than an unbounded
    convergence loop.
    """
    if x <= 0:
        raise ValueError("x must be positive")
    if x <= 1:
        return 0
    bound = x.numerator.bit_length() + x.denominator.bit_length() + 2
    p = Fraction(1)
    for j in range(bound + 1):
        if p >= x:
            return j
        p *= 2
    raise AssertionError("bit-length bound for ceil_log2 failed")


def strip_decompose(x: Fraction) -> tuple[int, Fraction]:
    """Return x = m + r with m >= 0 and 0 < r <= 1."""
    if x <= 0:
        raise ValueError("x must be positive")
    m = (x.numerator - 1) // x.denominator  # ceil(x) - 1
    r = x - m
    assert m >= 0 and 0 < r <= 1 and x == m + r
    return m, r


def finite_product(values: list[Fraction]) -> Fraction:
    out = Fraction(1)
    for value in values:
        out *= value
    return out


def rising(x: Fraction, count: int) -> Fraction:
    """x (x+1) ... (x+count-1), with the empty product equal to 1."""
    if count < 0:
        raise ValueError("count must be nonnegative")
    out = Fraction(1)
    for j in range(count):
        out *= x + j
    return out


def pow_le_int_target(q: Fraction, degree: int, target: int) -> bool:
    """Decide q**degree <= target exactly, with q >= 0."""
    if q < 0 or degree < 1 or target < 0:
        raise ValueError("invalid power comparison")
    return q.numerator**degree <= target * q.denominator**degree


def root_bounds_integer(target: int, degree: int, upper: int, steps: int) -> tuple[Fraction, Fraction]:
    """Bound target**(1/degree) by dyadic bisection.

    Preconditions: degree >= 1, target >= 1, upper**degree >= target.
    The loop count is explicit, so the algorithm is primitive-recursive.
    """
    if degree < 1 or target < 1 or upper < 1 or steps < 0:
        raise ValueError("invalid root-bisection arguments")
    lo = Fraction(1)
    hi = Fraction(upper)
    if not pow_le_int_target(lo, degree, target):
        raise AssertionError("lower root invariant failed")
    if pow_le_int_target(hi, degree, target) and hi**degree != target:
        raise AssertionError("upper root invariant failed")
    if hi**degree == target:
        return hi, hi
    for _ in range(steps):
        mid = (lo + hi) / 2
        if pow_le_int_target(mid, degree, target):
            lo = mid
        else:
            hi = mid
    assert pow_le_int_target(lo, degree, target)
    assert hi.numerator**degree >= target * hi.denominator**degree
    return lo, hi


def exact_coefficients(r: Fraction, n: int) -> tuple[Fraction, Fraction]:
    """Coefficients c_A, c_B with A_n=c_A*n^r and B_n=c_B*n^r."""
    if not (0 < r <= 1) or n < 1:
        raise ValueError("requires 0 < r <= 1 and n >= 1")
    p_n = rising(r, n)  # r ... (r+n-1)
    c_b = Fraction(factorial(n - 1), 1) / p_n
    c_a = Fraction(factorial(n), 1) / (p_n * (r + n))
    assert c_b == c_a * Fraction(n + r, n)
    return c_a, c_b


def monotonicity_checks(r: Fraction, n: int) -> dict[str, bool]:
    """Check the two exact rational inequalities behind nesting.

    For r=a/b, powers remove all radicals.
    """
    if not (0 < r <= 1) or n < 1:
        raise ValueError("requires 0 < r <= 1 and n >= 1")
    a, b = r.numerator, r.denominator
    # (A_{n+1}/A_n)^b >= 1.
    lhs_a = Fraction((n + 1) ** (a + b), n**a)
    rhs_a = (Fraction(n + 1, 1) + r) ** b
    a_increasing = lhs_a >= rhs_a
    # (B_{n+1}/B_n)^b <= 1.
    lhs_b = Fraction(n**b * (n + 1) ** a, n**a)
    rhs_b = (Fraction(n, 1) + r) ** b
    b_decreasing = lhs_b <= rhs_b
    return {"A_increasing": a_increasing, "B_decreasing": b_decreasing}


@dataclass(frozen=True)
class Certificate:
    x: str
    m: int
    r: str
    requested_bits: int
    internal_bits: int
    n: int
    root_steps: int
    root_degree: int
    root_target: str
    root_lo: str
    root_hi: str
    strip_lower: str
    strip_upper: str
    shift_product: str
    lower: str
    upper: str
    target_width: str
    actual_width: str
    theoretical_raw_width_bound: str
    A_increasing_at_n: bool
    B_decreasing_at_n: bool


def raw_strip_certificate(r: Fraction, bits: int, n: int | None = None) -> dict[str, Any]:
    if not (0 < r <= 1):
        raise ValueError("r must lie in (0,1]")
    if bits < 0:
        raise ValueError("bits must be nonnegative")
    if n is None:
        n = 1 << (bits + 2)
    if n < 1:
        raise ValueError("n must be positive")

    a, b = r.numerator, r.denominator
    target = n**a
    # Exact bracket gap is <= 1/n.  Root error is chosen so that the two
    # propagated endpoint errors total at most 2^(-bits-2).
    delta = r * Fraction(1, 1 << (bits + 3))
    steps = ceil_log2_fraction(Fraction(n, 1) / delta)
    root_lo, root_hi = root_bounds_integer(target, b, n, steps)
    c_a, c_b = exact_coefficients(r, n)
    lower = c_a * root_lo
    upper = c_b * root_hi
    theoretical = Fraction(1, n) + Fraction(2, 1) * delta / r
    checks = monotonicity_checks(r, n)

    assert root_hi - root_lo <= delta
    assert upper >= lower
    assert upper - lower <= theoretical
    return {
        "n": n,
        "root_steps": steps,
        "root_degree": b,
        "root_target": target,
        "root_lo": root_lo,
        "root_hi": root_hi,
        "strip_lower": lower,
        "strip_upper": upper,
        "theoretical_raw_width_bound": theoretical,
        **checks,
    }


def gamma_certificate(x: Fraction, bits: int) -> Certificate:
    if x <= 0:
        raise ValueError("x must be positive")
    if bits < 0:
        raise ValueError("bits must be nonnegative")
    m, r = strip_decompose(x)
    shift = rising(r, m)
    extra = ceil_log2_fraction(max(Fraction(1), shift)) + 2
    internal = bits + extra

    # One explicit precision choice suffices: the strip interval has width at
    # most 2^(-internal-1), while shift <= 2^(extra-2).
    raw = raw_strip_certificate(r, internal)
    lower = shift * raw["strip_lower"]
    upper = shift * raw["strip_upper"]
    assert upper - lower <= Fraction(1, 1 << bits)

    return Certificate(
        x=frac_text(x),
        m=m,
        r=frac_text(r),
        requested_bits=bits,
        internal_bits=internal,
        n=raw["n"],
        root_steps=raw["root_steps"],
        root_degree=raw["root_degree"],
        root_target=str(raw["root_target"]),
        root_lo=frac_text(raw["root_lo"]),
        root_hi=frac_text(raw["root_hi"]),
        strip_lower=frac_text(raw["strip_lower"]),
        strip_upper=frac_text(raw["strip_upper"]),
        shift_product=frac_text(shift),
        lower=frac_text(lower),
        upper=frac_text(upper),
        target_width=frac_text(Fraction(1, 1 << bits)),
        actual_width=frac_text(upper - lower),
        theoretical_raw_width_bound=frac_text(raw["theoretical_raw_width_bound"]),
        A_increasing_at_n=raw["A_increasing"],
        B_decreasing_at_n=raw["B_decreasing"],
    )


def verify_certificate(data: dict[str, Any]) -> None:
    x = frac_from_text(data["x"])
    m, r = strip_decompose(x)
    assert m == int(data["m"])
    assert r == frac_from_text(data["r"])
    bits = int(data["requested_bits"])
    n = int(data["n"])
    degree = int(data["root_degree"])
    target = int(data["root_target"])
    lo = frac_from_text(data["root_lo"])
    hi = frac_from_text(data["root_hi"])
    assert degree == r.denominator
    assert target == n**r.numerator
    assert pow_le_int_target(lo, degree, target)
    assert hi.numerator**degree >= target * hi.denominator**degree

    c_a, c_b = exact_coefficients(r, n)
    strip_lower = frac_from_text(data["strip_lower"])
    strip_upper = frac_from_text(data["strip_upper"])
    assert strip_lower == c_a * lo
    assert strip_upper == c_b * hi

    shift = rising(r, m)
    assert shift == frac_from_text(data["shift_product"])
    lower = frac_from_text(data["lower"])
    upper = frac_from_text(data["upper"])
    assert lower == shift * strip_lower
    assert upper == shift * strip_upper
    assert upper - lower == frac_from_text(data["actual_width"])
    assert upper - lower <= Fraction(1, 1 << bits)
    target_width = frac_from_text(data["target_width"])
    raw_bound = frac_from_text(data["theoretical_raw_width_bound"])
    assert target_width == Fraction(1, 1 << bits)
    assert raw_bound == Fraction(1, n) + Fraction(1, 1 << (int(data["internal_bits"]) + 2))
    assert strip_upper - strip_lower <= raw_bound
    checks = monotonicity_checks(r, n)
    assert checks["A_increasing"] == bool(data["A_increasing_at_n"])
    assert checks["B_decreasing"] == bool(data["B_decreasing_at_n"])
    assert checks["A_increasing"] and checks["B_decreasing"]


def decimal_interval(lo: Fraction, hi: Fraction, digits: int = 16) -> tuple[str, str]:
    # Decimal rendering is display-only; verification never uses it.
    scale = 10**digits
    lo_i = (lo.numerator * scale) // lo.denominator
    hi_i = -((-hi.numerator * scale) // hi.denominator)
    return f"{lo_i / scale:.{digits}f}", f"{hi_i / scale:.{digits}f}"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("x", nargs="?", default="1/2", help="positive rational, e.g. 1/2")
    parser.add_argument("--bits", type=int, default=6, help="requested interval width <= 2^-bits")
    parser.add_argument("--json", type=Path, help="write certificate JSON")
    parser.add_argument("--verify", type=Path, help="verify an existing certificate JSON")
    args = parser.parse_args()

    if args.verify:
        data = json.loads(args.verify.read_text(encoding="utf-8"))
        verify_certificate(data)
        print(f"verified: {args.verify}")
        return

    cert = gamma_certificate(parse_fraction(args.x), args.bits)
    data = asdict(cert)
    verify_certificate(data)
    lo, hi = frac_from_text(cert.lower), frac_from_text(cert.upper)
    dlo, dhi = decimal_interval(lo, hi)
    print(json.dumps(data, indent=2, sort_keys=True))
    print(f"decimal enclosure: [{dlo}, {dhi}]")
    if args.json:
        args.json.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(f"wrote: {args.json}")


if __name__ == "__main__":
    main()
