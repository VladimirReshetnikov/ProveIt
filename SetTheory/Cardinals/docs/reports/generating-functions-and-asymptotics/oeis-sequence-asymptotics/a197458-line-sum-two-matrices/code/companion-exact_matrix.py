#!/usr/bin/env python3
"""Exact, bounded, no-network checks for A197458 (Report168).

Only the Python standard library is required. The five counting routes are
algorithmically distinct: ODE recurrence, compressed column-degree states,
labeled degree tuples, literal bitmasks, and rational GF truncation.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from fractions import Fraction
import json
from math import comb, factorial, prod
from pathlib import Path
import re
from typing import Sequence

MAX_ODE_N = 2000
MAX_DP_N = 60
MAX_GF_N = 50
MAX_TUPLE_N = 8
MAX_LITERAL_N = 4
FIXTURE_COUNT = 17
DATA = Path(__file__).resolve().parent.parent / "data"
# Coefficients in increasing powers of t, for p_0 G + p_1 G' + p_2 G''.
ODE_POLYNOMIALS = (
    (32, 0, -36, 20, -3, -2, 1),
    (-16, 96, -92, 28, 8, -12, 4),
    (0, -16, 48, -60, 44, -20, 4),
)


def bounded_int(value: int, name: str, maximum: int, minimum: int = 0) -> int:
    """Reject bool and non-built-in integers, including integral floats."""
    if type(value) is not int:
        raise TypeError(f"{name} must be an integer (booleans are not accepted)")
    if not minimum <= value <= maximum:
        raise ValueError(f"{name} must be in [{minimum}, {maximum}]")
    return value


def exact_divide(numerator: int, denominator: int, context: str = "division") -> int:
    if type(numerator) is not int or type(denominator) is not int:
        raise TypeError("exact_divide requires integer arguments, not booleans")
    if denominator == 0:
        raise ZeroDivisionError("exact division by zero")
    quotient, remainder = divmod(numerator, denominator)
    if remainder:
        raise ArithmeticError(f"{context}: nonzero remainder {remainder}")
    return quotient


def ode_sequence(max_n: int) -> list[int]:
    """Return a_0,...,a_max_n by the ODE; exact division is always checked.

    [t^n] has leading coefficient -16(n+1)^2 on b_(n+1).
    After multiplying by (n!)^2 and using a_m=(m!)^2 b_m,
    the left side is -16 a_(n+1). This explains the divisor 16.
    """
    bounded_int(max_n, "max_n", MAX_ODE_N)
    values = [1]
    for n in range(max_n):
        total = 0
        for derivative, polynomial in enumerate(ODE_POLYNOMIALS):
            for power, coefficient in enumerate(polynomial):
                m = n - power + derivative
                if coefficient and derivative <= m <= n:
                    ratio = prod(range(m + 1, n + 1))
                    falling = prod(range(m - derivative + 1, m + 1))
                    total += coefficient * ratio * ratio * falling * values[m]
        values.append(exact_divide(total, 16, f"ODE step n={n}"))
    return values


def compressed_dp(n: int) -> int:
    """Independent row DP; k zero columns, l one columns, others full."""
    bounded_int(n, "n", MAX_DP_N)
    states = {(n, 0): 1}
    for _ in range(n):
        nxt = defaultdict(int)
        for (k, ell), ways in states.items():
            nxt[k, ell] += ways
            if k:
                nxt[k - 1, ell + 1] += k * ways
            if ell:
                nxt[k, ell - 1] += ell * ways
            if k >= 2:
                nxt[k - 2, ell + 2] += comb(k, 2) * ways
            if k and ell:
                nxt[k - 1, ell] += k * ell * ways
            if ell >= 2:
                nxt[k, ell - 2] += comb(ell, 2) * ways
        states = nxt
    return sum(states.values())


def tuple_dp(n: int) -> int:
    """Keep the entire labeled column-degree tuple, with no multiplicities."""
    bounded_int(n, "n", MAX_TUPLE_N)
    rows = [()] + [(i,) for i in range(n)]
    rows += [(i, j) for i in range(n) for j in range(i + 1, n)]
    states = {(0,) * n: 1}
    for _ in range(n):
        nxt = defaultdict(int)
        for state, ways in states.items():
            for row in rows:
                if any(state[i] == 2 for i in row):
                    continue
                changed = list(state)
                for i in row:
                    changed[i] += 1
                nxt[tuple(changed)] += ways
        states = nxt
    return sum(states.values())


def literal_bitmask(n: int) -> int:
    """Visit every one of 2^(n*n) bitmasks. Hard cap n<=4 is intentional."""
    bounded_int(n, "n", MAX_LITERAL_N)
    masks = [sum(1 << (i * n + j) for j in range(n)) for i in range(n)]
    masks += [sum(1 << (i * n + j) for i in range(n)) for j in range(n)]
    return sum(all((bits & mask).bit_count() <= 2 for mask in masks)
               for bits in range(1 << (n * n)))


def _convolve(a: Sequence[Fraction], b: Sequence[Fraction], degree: int) -> list[Fraction]:
    out = [Fraction(0)] * (degree + 1)
    for i, x in enumerate(a[:degree + 1]):
        if x:
            for j, y in enumerate(b[:degree + 1 - i]):
                if y:
                    out[i + j] += x * y
    return out


def gf_sequence(max_n: int) -> list[int]:
    """Independent finite rational series for P(t)*I_0(sqrt(R(t))).

    This does not call the ODE or either DP. P is exponentiated from log P;
    I_0 is summed from powers of R/4 and exact factorial denominators.
    """
    bounded_int(max_n, "max_n", MAX_GF_N)
    log_p = [Fraction(0)] + [Fraction(1) + Fraction(1, 2 * k)
              - (Fraction(1, 2) if k == 1 else 0) for k in range(1, max_n + 1)]
    p = [Fraction(1)]
    for n in range(1, max_n + 1):
        p.append(sum(k * log_p[k] * p[n - k] for k in range(1, n + 1)) / n)
    # R/4 = t(2-t)^2 / (4(1-t)^2).
    r4 = [Fraction(0)] * (max_n + 1)
    for n in range(1, max_n + 1):
        r4[n] = Fraction(n) - (n - 1 if n >= 2 else 0)
        if n >= 3:
            r4[n] += Fraction(n - 2, 4)
    bessel = [Fraction(0)] * (max_n + 1)
    power = [Fraction(1)] + [Fraction(0)] * max_n
    for k in range(max_n + 1):
        divisor = factorial(k) ** 2
        for n in range(max_n + 1):
            bessel[n] += power[n] / divisor
        if k < max_n:
            power = _convolve(power, r4, max_n)
    normalized = _convolve(p, bessel, max_n)
    return [exact_divide(value.numerator * factorial(n) ** 2, value.denominator,
                         f"GF integrality n={n}") for n, value in enumerate(normalized)]


def ode_residuals(values: Sequence[int]) -> list[Fraction]:
    """Substitute an independently supplied integer prefix into the ODE."""
    if not isinstance(values, (list, tuple)) or not values:
        raise TypeError("values must be a nonempty list or tuple of integers")
    bounded_int(len(values) - 1, "maximum sequence index", MAX_ODE_N)
    if any(type(value) is not int or value < 0 for value in values):
        raise ValueError("sequence values must be nonnegative integers, not booleans")
    b = [Fraction(a, factorial(n) ** 2) for n, a in enumerate(values)]
    residuals = []
    for n in range(len(values) - 1):
        total = Fraction(0)
        for derivative, polynomial in enumerate(ODE_POLYNOMIALS):
            for power, coefficient in enumerate(polynomial):
                m = n - power + derivative
                if coefficient and derivative <= m < len(values):
                    total += coefficient * prod(range(m - derivative + 1, m + 1)) * b[m]
        residuals.append(total)
    return residuals


def decimal_integer(value: int) -> str:
    """Bounded CLI output can exceed Python's default integer-string limit.

    Use base-10^9 chunks rather than disabling the interpreter's safeguard.
    """
    if type(value) is not int:
        raise TypeError("value must be an integer")
    if value < 0:
        return "-" + decimal_integer(-value)
    chunks = []
    while value >= 10**9:
        value, chunk = divmod(value, 10**9)
        chunks.append(chunk)
    return str(value) + "".join(f"{chunk:09d}" for chunk in reversed(chunks))


def _unique_json_object(pairs):
    out = {}
    for key, value in pairs:
        if key in out:
            raise ValueError(f"duplicate JSON key {key!r}")
        out[key] = value
    return out


def _read_bounded(path: str | Path, limit: int, label: str) -> bytes:
    with Path(path).open("rb") as source:
        raw = source.read(limit + 1)
    if len(raw) > limit:
        raise ValueError(f"{label} exceeds {limit} bytes")
    return raw


def load_fixtures(path: str | Path = DATA / "oeis_fixtures.json") -> list[int]:
    """Strict local fixture loader; rejects malformed, missing, or extra data."""
    raw = _read_bounded(path, 16384, "fixture")
    try:
        obj = json.loads(raw, object_pairs_hook=_unique_json_object)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError(f"invalid fixture JSON: {exc}") from exc
    if type(obj) is not dict or set(obj) != {"sequence", "offset", "terms"}:
        raise ValueError("fixture must have exactly sequence, offset, and terms")
    if obj["sequence"] != "A197458" or type(obj["offset"]) is not int or obj["offset"] != 0:
        raise ValueError("fixture must be A197458 with integer offset 0")
    terms = obj["terms"]
    if type(terms) is not list or len(terms) != FIXTURE_COUNT:
        raise ValueError("fixture must contain exactly 17 terms")
    if any(type(t) is not str or len(t) > 128 or not re.fullmatch(r"0|[1-9][0-9]*", t)
           for t in terms):
        raise ValueError("fixture terms must be canonical unsigned decimal strings")
    values = [int(t) for t in terms]
    if values[0] != 1 or any(b <= a for a, b in zip(values, values[1:])):
        raise ValueError("fixture must start at 1 and strictly increase")
    return values


def load_oeis_source(path: str | Path = DATA / "oeis_term_records.txt") -> list[int]:
    raw = _read_bounded(path, 32768, "OEIS source fixture")
    records = {}
    for line in raw.decode("utf-8").splitlines():
        if line.startswith(("%S ", "%T ", "%U ")):
            fields = line.split(" ", 2)
            if len(fields) != 3 or fields[1] != "A197458" or fields[0] in records:
                raise ValueError("malformed or repeated OEIS sequence record")
            records[fields[0]] = fields[2]
    if set(records) != {"%S", "%T", "%U"}:
        raise ValueError("missing OEIS %S/%T/%U records")
    text = "".join(records[key] for key in ("%S", "%T", "%U"))
    if not re.fullmatch(r"(?:0|[1-9][0-9]*)(?:,(?:0|[1-9][0-9]*)){16}", text):
        raise ValueError("OEIS source must contain exactly 17 canonical terms")
    return [int(t) for t in text.split(",")]


def require_equal(actual, expected, context: str) -> None:
    if actual != expected:
        raise ArithmeticError(f"{context}: exact comparison failed")


def verify(max_n: int = 200, dp_max_n: int = 40, gf_max_n: int = 30,
           tuple_max_n: int = 8, literal_max_n: int = 4,
           fixture: str | Path = DATA / "oeis_fixtures.json") -> dict:
    bounded_int(max_n, "max_n", MAX_ODE_N, 16)
    for value, name, limit in ((dp_max_n, "dp_max_n", MAX_DP_N),
                              (gf_max_n, "gf_max_n", MAX_GF_N),
                              (tuple_max_n, "tuple_max_n", MAX_TUPLE_N),
                              (literal_max_n, "literal_max_n", MAX_LITERAL_N)):
        bounded_int(value, name, limit)
        if value > max_n:
            raise ValueError(f"{name} cannot exceed max_n")
    values = ode_sequence(max_n)
    fixtures = load_fixtures(fixture)
    require_equal(values[:FIXTURE_COUNT], fixtures, "all 17 OEIS fixtures")
    require_equal(load_oeis_source(), fixtures, "frozen OEIS source vs JSON")
    for name, bound, method in (("compressed DP", dp_max_n, compressed_dp),
                                ("tuple DP", tuple_max_n, tuple_dp),
                                ("literal masks", literal_max_n, literal_bitmask)):
        require_equal([method(n) for n in range(bound + 1)], values[:bound + 1], name)
    independent = gf_sequence(gf_max_n)
    require_equal(independent, values[:gf_max_n + 1], "rational GF")
    require_equal(ode_residuals(independent), [Fraction(0)] * gf_max_n, "GF ODE residuals")
    return {"status": "PASS", "sequence": "A197458", "fixture_terms": FIXTURE_COUNT,
            "ode_max_n": max_n, "compressed_dp_max_n": dp_max_n,
            "rational_gf_max_n": gf_max_n, "tuple_dp_max_n": tuple_max_n,
            "literal_max_n": literal_max_n, "independent_ode_residual_count": gf_max_n,
            "a_max_n": decimal_integer(values[-1]), "network_used": False}


def cli_integer(maximum: int, minimum: int = 0):
    def parse(text: str) -> int:
        if not re.fullmatch(r"0|[1-9][0-9]*", text):
            raise argparse.ArgumentTypeError("expected a canonical nonnegative integer")
        if len(text) > len(str(maximum)):
            raise argparse.ArgumentTypeError(f"must be in [{minimum}, {maximum}]")
        value = int(text)
        if not minimum <= value <= maximum:
            raise argparse.ArgumentTypeError(f"must be in [{minimum}, {maximum}]")
        return value
    return parse


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    check = sub.add_parser("verify", help="cross-check all exact routes and all 17 fixtures")
    check.add_argument("--max-n", type=cli_integer(MAX_ODE_N, 16), default=200)
    check.add_argument("--dp-max-n", type=cli_integer(MAX_DP_N), default=40)
    check.add_argument("--gf-max-n", type=cli_integer(MAX_GF_N), default=30)
    check.add_argument("--tuple-max-n", type=cli_integer(MAX_TUPLE_N), default=8)
    check.add_argument("--literal-max-n", type=cli_integer(MAX_LITERAL_N), default=4)
    check.add_argument("--fixture", type=Path, default=DATA / "oeis_fixtures.json")
    sequence = sub.add_parser("sequence", help="emit exact decimal integer strings")
    sequence.add_argument("--max-n", type=cli_integer(MAX_ODE_N), default=16)
    args = parser.parse_args(argv)
    try:
        if args.command == "verify":
            result = verify(args.max_n, args.dp_max_n, args.gf_max_n,
                            args.tuple_max_n, args.literal_max_n, args.fixture)
        else:
            result = {"sequence": "A197458", "offset": 0,
                      "terms": [decimal_integer(a) for a in ode_sequence(args.max_n)]}
    except (OSError, ValueError, TypeError, ArithmeticError) as exc:
        parser.error(str(exc))
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
