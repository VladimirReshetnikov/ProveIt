#!/usr/bin/env python3
"""Exact Lengyel chain counts and length statistics (OEIS A005121).

Python 3.11+; standard library only.  A chain runs from the discrete partition
to the one-block partition, with arbitrary strict transitions, not necessarily
cover relations.  H is its number of strict transitions; H_1 = 0.

Z_1(q) = 1 and Z_n(q) = q sum_{1 <= j < n} S(n,j) Z_j(q).
Polynomial tuples list coefficients in increasing powers of q.  Raw moments
include order zero (one); cumulant tuples include a zero at index zero.

Examples:
    python lengyel_exact.py value 200
    python lengyel_exact.py sequence 6
    python lengyel_exact.py polynomial 6
    python lengyel_exact.py moments 6 4
    python lengyel_exact.py inverse 9013 --max-n 20

The bounds below are deliberate resource limits, not mathematical limitations.
There are no changes to process-wide integer-conversion, recursion, or numeric
precision settings.  Decimal conversion splits trusted integers into at most
600-digit pieces, including the numerator and denominator of every Fraction.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from math import comb
import sys
from typing import Iterator, Sequence


MAX_N = 1000
MAX_POLYNOMIAL_N = 150
MAX_MOMENT_N = 600
MAX_MOMENT_ORDER = 12
MAX_TARGET_DIGITS = 6000
DECIMAL_CHUNK_DIGITS = 600
MAX_CLI_CHARS = MAX_TARGET_DIGITS + 256
_DECIMAL_BASE = 10 ** DECIMAL_CHUNK_DIGITS
_MAX_TARGET_EXCLUSIVE = 10 ** MAX_TARGET_DIGITS


class InputError(ValueError):
    """An input is invalid or exceeds a documented resource bound."""


class ThresholdNotReached(ValueError):
    """The bounded exact search did not reach its target.

    last_value is z_max_n, allowing the caller to inspect the exact endpoint.
    This is a bounded-search failure, not a claim that the inverse is absent.
    """

    def __init__(self, max_n: int, last_value: int) -> None:
        self.max_n = max_n
        self.last_value = last_value
        super().__init__("target exceeds z_max_n within the permitted search")


def _bounded_int(value: int, low: int, high: int, name: str) -> int:
    # Do not format rejected values: even repr(huge_int) can hit Python's cap.
    if type(value) is not int or value < low or value > high:
        raise InputError(f"{name} must be an integer in [{low}, {high}]")
    return value


def _stirling_rows_unchecked(n: int) -> Iterator[tuple[int, ...]]:
    row = (1,)
    yield row
    for i in range(1, n + 1):
        row = tuple([0] + [
            (j * row[j] if j < len(row) else 0) + row[j - 1]
            for j in range(1, i + 1)
        ])
        yield row


def stirling_row(n: int) -> tuple[int, ...]:
    """Return (S(n,0), ..., S(n,n)), allowing n=0 and n<=MAX_N."""
    _bounded_int(n, 0, MAX_N, "n")
    row = (1,)
    for row in _stirling_rows_unchecked(n):
        pass
    return row


def _values_unchecked(n: int) -> Iterator[tuple[int, int]]:
    values = [0, 1]  # index zero is unused, not a claim about z_0
    for i, row in enumerate(_stirling_rows_unchecked(n)):
        if i == 0:
            continue
        if i > 1:
            values.append(sum(row[j] * values[j] for j in range(1, i)))
        yield i, values[i]


def chain_numbers(n: int) -> tuple[int, ...]:
    """Return (z_1, ..., z_n), for 1<=n<=MAX_N."""
    _bounded_int(n, 1, MAX_N, "n")
    return tuple(value for _, value in _values_unchecked(n))


def chain_value(n: int) -> int:
    """Return z_n exactly, for 1<=n<=MAX_N."""
    _bounded_int(n, 1, MAX_N, "n")
    result = 1
    for _, result in _values_unchecked(n):
        pass
    return result


def chain_polynomial(n: int) -> tuple[int, ...]:
    """Return the coefficients of Z_n(q), for n<=MAX_POLYNOMIAL_N."""
    _bounded_int(n, 1, MAX_POLYNOMIAL_N, "n")
    polynomials: list[tuple[int, ...]] = [(), (1,)]
    for i, row in enumerate(_stirling_rows_unchecked(n)):
        if i < 2:
            continue
        coefficients = [0] * i
        for j in range(1, i):
            for h, coefficient in enumerate(polynomials[j]):
                coefficients[h + 1] += row[j] * coefficient
        polynomials.append(tuple(coefficients))
    return polynomials[n]


def raw_moment_totals(n: int, order: int) -> tuple[int, ...]:
    """Return (sum_chains H^r) for r=0,...,order, with 0^0=1.

    This uses only order+1 entries per rank, rather than constructing the full
    chain-length polynomial.  It first computes ordinary q-derivatives F_r:
    F_r(n) = sum_j S(n,j) [F_r(j) + r F_{r-1}(j)], then applies the Stirling
    transform D^r = sum_k S(r,k) d^k/dq^k at q=1, where D=q d/dq.
    Bounds: n<=MAX_MOMENT_N and order<=MAX_MOMENT_ORDER.
    """
    _bounded_int(n, 1, MAX_MOMENT_N, "n")
    _bounded_int(order, 0, MAX_MOMENT_ORDER, "order")
    derivatives = [(), tuple([1] + [0] * order)]
    for i, row in enumerate(_stirling_rows_unchecked(n)):
        if i < 2:
            continue
        current = [0] * (order + 1)
        for j in range(1, i):
            scale = row[j]
            previous = derivatives[j]
            current[0] += scale * previous[0]
            for r in range(1, order + 1):
                current[r] += scale * (previous[r] + r * previous[r - 1])
        derivatives.append(tuple(current))
    endpoint = derivatives[n]
    return tuple(
        sum(coefficient * endpoint[k] for k, coefficient in enumerate(row))
        for row in _stirling_rows_unchecked(order)
    )


def raw_moments(n: int, order: int) -> tuple[Fraction, ...]:
    """Return exact E[H^r], r=0,...,order, under the uniform chain law."""
    totals = raw_moment_totals(n, order)
    return tuple(Fraction(total, totals[0]) for total in totals)


def _cumulants_from_moments(moments: Sequence[Fraction]) -> tuple[Fraction, ...]:
    result = [Fraction(0)]
    for r in range(1, len(moments)):
        result.append(moments[r] - sum(
            (comb(r - 1, j - 1) * result[j] * moments[r - j]
             for j in range(1, r)), Fraction(0)
        ))
    return tuple(result)


def cumulants(n: int, order: int) -> tuple[Fraction, ...]:
    """Return exact cumulants kappa_r, r=0,...,order (kappa_0=0)."""
    return _cumulants_from_moments(raw_moments(n, order))


def threshold_inverse(target: int, *, max_n: int = MAX_N) -> int:
    """Return min{n>=2: z_n>=target}, if n<=max_n, using exact arithmetic.

    target must be a positive integer with at most MAX_TARGET_DIGITS digits.
    A target beyond z_max_n raises ThresholdNotReached.  No asymptotic formula,
    floating-point approximation, or unproved rounding rule is used.
    """
    _bounded_int(max_n, 2, MAX_N, "max_n")
    if type(target) is not int or target < 1 or target >= _MAX_TARGET_EXCLUSIVE:
        raise InputError("target must be positive with at most 6000 decimal digits")
    last_value = 1
    for n, last_value in _values_unchecked(max_n):
        if n >= 2 and last_value >= target:
            return n
    raise ThresholdNotReached(max_n, last_value)


def integer_to_decimal(value: int) -> str:
    """Format a trusted computed integer without a >600-digit int conversion."""
    if type(value) is not int:
        raise InputError("decimal formatting requires an integer")
    if value == 0:
        return "0"
    sign = "-" if value < 0 else ""
    value = abs(value)
    pieces = []
    while value:
        value, remainder = divmod(value, _DECIMAL_BASE)
        pieces.append(str(remainder))
    return sign + pieces[-1] + "".join(
        piece.zfill(DECIMAL_CHUNK_DIGITS) for piece in reversed(pieces[:-1])
    )


def rational_to_decimal(value: Fraction) -> str:
    """Format a Fraction exactly as numerator[/denominator], with safe chunks."""
    if not isinstance(value, Fraction):
        raise InputError("rational formatting requires a Fraction")
    numerator = integer_to_decimal(value.numerator)
    if value.denominator == 1:
        return numerator
    return numerator + "/" + integer_to_decimal(value.denominator)


def _check_decimal_token(text: str, *, max_digits: int, name: str) -> None:
    # The length check happens first, before digit scanning or integer parsing.
    if not isinstance(text, str) or not 1 <= len(text) <= max_digits:
        raise InputError(f"{name} has an invalid length")
    if not all("0" <= character <= "9" for character in text):
        raise InputError(f"{name} must use ASCII decimal digits only")
    if len(text) > 1 and text[0] == "0":
        raise InputError(f"{name} must not have leading zeroes")


def _parse_small(text: str, low: int, high: int, name: str) -> int:
    upper = str(high)
    _check_decimal_token(text, max_digits=len(upper), name=name)
    # Reject values outside the resource limit before even small int parsing.
    if len(text) == len(upper) and text > upper:
        raise InputError(f"{name} exceeds its resource bound")
    lower = str(low)
    if len(text) < len(lower) or (len(text) == len(lower) and text < lower):
        raise InputError(f"{name} is below its permitted minimum")
    return _bounded_int(int(text), low, high, name)


def _parse_target(text: str) -> int:
    _check_decimal_token(text, max_digits=MAX_TARGET_DIGITS, name="target")
    if text == "0":
        raise InputError("target must be positive")
    result = 0
    for start in range(0, len(text), DECIMAL_CHUNK_DIGITS):
        piece = text[start:start + DECIMAL_CHUNK_DIGITS]
        result = result * (10 ** len(piece)) + int(piece)
    return result


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    commands = parser.add_subparsers(dest="command", required=True)
    for command, help_text in (
        ("value", "print z_n"),
        ("sequence", "print n, z_n rows through N"),
        ("polynomial", "print exponent, coefficient rows for Z_n(q)"),
    ):
        subparser = commands.add_parser(command, help=help_text)
        subparser.add_argument("n")
    moments = commands.add_parser("moments", help="print raw moments and cumulants")
    moments.add_argument("n")
    moments.add_argument("order")
    inverse = commands.add_parser("inverse", help="bounded exact integer threshold inverse")
    inverse.add_argument("target")
    inverse.add_argument("--max-n", default=str(MAX_N))
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    arguments = list(sys.argv[1:] if argv is None else argv)
    # Guard total supplied text before argparse can echo a huge invalid token.
    if len(arguments) > 8 or sum(map(len, arguments)) > MAX_CLI_CHARS:
        print("error: command line exceeds the input-size limit", file=sys.stderr)
        return 2
    parser = _parser()
    args = parser.parse_args(arguments)
    try:
        if args.command == "inverse":
            # The search budget is validated before parsing a large target.
            max_n = _parse_small(args.max_n, 2, MAX_N, "max_n")
            target = _parse_target(args.target)
            print(threshold_inverse(target, max_n=max_n))
        elif args.command == "polynomial":
            n = _parse_small(args.n, 1, MAX_POLYNOMIAL_N, "n")
            for h, coefficient in enumerate(chain_polynomial(n)):
                print(f"{h}\t{integer_to_decimal(coefficient)}")
        elif args.command == "moments":
            n = _parse_small(args.n, 1, MAX_MOMENT_N, "n")
            order = _parse_small(args.order, 0, MAX_MOMENT_ORDER, "order")
            totals = raw_moment_totals(n, order)
            moments = tuple(Fraction(total, totals[0]) for total in totals)
            kappas = _cumulants_from_moments(moments)
            print(f"n={n} z_n={integer_to_decimal(totals[0])} convention=strict_transitions")
            print("order\traw_moment\tcumulant")
            for r in range(order + 1):
                print(f"{r}\t{rational_to_decimal(moments[r])}\t"
                      f"{rational_to_decimal(kappas[r])}")
        else:
            n = _parse_small(args.n, 1, MAX_N, "n")
            if args.command == "value":
                print(integer_to_decimal(chain_value(n)))
            else:
                for i, value in enumerate(chain_numbers(n), 1):
                    print(f"{i}\t{integer_to_decimal(value)}")
    except (InputError, ThresholdNotReached) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
