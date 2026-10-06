#!/usr/bin/env python3
"""Deterministic, standard-library tests; all checks remain active under -O.

Run with Python 3.11+:
    python test_lengyel_exact.py
    python -O test_lengyel_exact.py
    PYTHONINTMAXSTRDIGITS=640 python -O test_lengyel_exact.py

The reference enumerator visits every set partition, every comparable pair,
and every strict endpoint-to-endpoint chain through n=6.  The larger reference
computations are separate implementations, and decimal output is independently
parsed in nine-digit pieces.  Every real CLI subprocess has the integer string
conversion limit set to 640 by its environment, never a runtime override.
"""

from __future__ import annotations

from contextlib import redirect_stderr
from fractions import Fraction
from io import StringIO
from math import comb, factorial
import os
from pathlib import Path
import subprocess
import sys
from unittest.mock import patch

import lengyel_exact as exact


class TestFailure(RuntimeError):
    pass


def check(condition: bool, label: str) -> None:
    if not condition:
        raise TestFailure(label)


def equal(actual, expected, label: str) -> None:
    # Avoid formatting possibly huge integers on a failed test.
    if actual != expected:
        raise TestFailure(label)


def raises(error_type, function, *args, **kwargs):
    try:
        function(*args, **kwargs)
    except error_type as error:
        return error
    except Exception as error:
        raise TestFailure("unexpected exception type") from error
    raise TestFailure("expected exception was not raised")


def partitions(n: int):
    """All set partitions as canonical restricted-growth words; iterative."""
    words = [()]
    for _ in range(n):
        words = [word + (label,)
                 for word in words
                 for label in range(max(word, default=-1) + 2)]
    return words


def refines(fine, coarse) -> bool:
    return all(fine[i] != fine[j] or coarse[i] == coarse[j]
               for i in range(len(fine)) for j in range(i))


def enumerate_chain_polynomial(n: int):
    words = partitions(n)
    top = words.index((0,) * n)
    bottom = words.index(tuple(range(n)))
    successors = [[j for j, q in enumerate(words)
                   if i != j and refines(p, q)]
                  for i, p in enumerate(words)]
    counts = [0] * n
    stack = [(bottom, 0)]
    while stack:
        current, length = stack.pop()
        if current == top:
            counts[length] += 1
        else:
            stack.extend((following, length + 1)
                         for following in successors[current])
    return len(words), tuple(counts)


def stirling_inclusion(n: int, k: int) -> int:
    """Independent surjection/inclusion-exclusion formula."""
    if k == 0:
        return int(n == 0)
    numerator = sum((-1) ** (k - j) * comb(k, j) * j ** n
                    for j in range(k + 1))
    denominator = factorial(k)
    equal(numerator % denominator, 0, "Stirling integrality")
    return numerator // denominator


def independent_values(n: int):
    """Separate in-place Stirling implementation for the larger CLI checks."""
    s = [1] + [0] * n
    values = [0] * (n + 1)
    for i in range(1, n + 1):
        for j in range(i, 0, -1):
            s[j] = j * s[j] + s[j - 1]
        s[0] = 0
        values[i] = 1 if i == 1 else sum(s[j] * values[j] for j in range(i))
    return values


def independent_raw_totals(n: int, order: int):
    """Euler/binomial recurrence, independent of ordinary derivatives."""
    s = [1] + [0] * n
    totals = [[0] * (order + 1) for _ in range(n + 1)]
    totals[1][0] = 1
    for i in range(1, n + 1):
        for j in range(i, 0, -1):
            s[j] = s[j - 1] + j * s[j]
        s[0] = 0
        if i > 1:
            for r in range(order + 1):
                totals[i][r] = sum(
                    s[j] * sum(comb(r, k) * totals[j][k] for k in range(r + 1))
                    for j in range(1, i)
                )
    return tuple(totals[n])


def independent_cumulants(moments):
    """Set-partition formula, rather than triangular cumulant recurrence."""
    result = [Fraction(0)]
    for r in range(1, len(moments)):
        total = Fraction(0)
        for partition in partitions(r):
            blocks = max(partition) + 1
            product = Fraction((-1) ** (blocks - 1) * factorial(blocks - 1))
            for label in range(blocks):
                product *= moments[partition.count(label)]
            total += product
        result.append(total)
    return tuple(result)


def parse_decimal_independently(text: str) -> int:
    sign = -1 if text.startswith("-") else 1
    text = text[1:] if sign == -1 else text
    check(bool(text) and all("0" <= c <= "9" for c in text), "decimal syntax")
    check(len(text) == 1 or text[0] != "0", "canonical decimal output")
    number = 0
    for start in range(0, len(text), 9):
        part = text[start:start + 9]
        number = number * 10 ** len(part) + int(part)
    return sign * number


def parse_fraction_independently(text: str) -> Fraction:
    parts = text.split("/")
    check(len(parts) in (1, 2), "fraction syntax")
    numerator = parse_decimal_independently(parts[0])
    denominator = parse_decimal_independently(parts[1]) if len(parts) == 2 else 1
    check(denominator > 0, "positive fraction denominator")
    return Fraction(numerator, denominator)


HERE = Path(__file__).resolve().parent


def cli(*arguments: str):
    environment = dict(os.environ, PYTHONINTMAXSTRDIGITS="640")
    optimization = ["-O"] if sys.flags.optimize else []
    return subprocess.run(
        [sys.executable, *optimization, str(HERE / "lengyel_exact.py"), *arguments],
        check=False, capture_output=True, text=True, env=environment, timeout=120,
    )


def test_partitions_and_polynomials() -> None:
    expected = (
        (1,),
        (0, 1),
        (0, 1, 3),
        (0, 1, 13, 18),
        (0, 1, 50, 205, 180),
        (0, 1, 201, 1865, 4245, 2700),
    )
    bells = (1, 2, 5, 15, 52, 203)
    for n in range(1, 7):
        count, polynomial = enumerate_chain_polynomial(n)
        equal(count, bells[n - 1], "full partition-poset size")
        equal(polynomial, expected[n - 1], "enumerated listed polynomial")
        equal(exact.chain_polynomial(n), polynomial, "recurrence versus all chains")
        equal(exact.chain_value(n), sum(polynomial), "polynomial evaluated at one")
    equal(exact.chain_numbers(6), (1, 1, 4, 32, 436, 9012), "listed sequence")
    print("PASS complete partition-poset and chain enumeration n=1..6")


def test_stirling_and_integer_recurrence() -> None:
    z = [0, 1]
    for n in range(26):
        row = tuple(stirling_inclusion(n, k) for k in range(n + 1))
        equal(exact.stirling_row(n), row, "Stirling inclusion-exclusion")
        if n >= 2:
            z.append(sum(row[j] * z[j] for j in range(1, n)))
    equal(exact.chain_numbers(25), tuple(z[1:]), "independent exact recurrence")
    for n in range(1, 36):
        previous, row = exact.stirling_row(n - 1), exact.stirling_row(n)
        for j in range(n + 1):
            expected = (j * previous[j] if j < n else 0)
            expected += previous[j - 1] if j else 0
            equal(row[j], expected, "Stirling recurrence")
    print("PASS Stirling inclusion-exclusion n=0..25 and exact recurrence")


def test_moments_and_cumulants() -> None:
    for n in range(1, 7):
        _, polynomial = enumerate_chain_polynomial(n)
        totals = tuple(sum(coefficient * h ** r
                           for h, coefficient in enumerate(polynomial))
                       for r in range(7))
        moments = tuple(Fraction(value, totals[0]) for value in totals)
        equal(exact.raw_moment_totals(n, 6), totals, "raw totals from all chains")
        equal(exact.raw_moments(n, 6), moments, "raw moments from all chains")
        equal(exact.cumulants(n, 6), independent_cumulants(moments),
              "independent set-partition cumulants")
    equal(exact.raw_moments(3, 4),
          (Fraction(1), Fraction(7, 4), Fraction(13, 4),
           Fraction(25, 4), Fraction(49, 4)), "listed n=3 moments")
    equal(exact.cumulants(3, 4),
          (Fraction(0), Fraction(7, 4), Fraction(3, 16),
           Fraction(-3, 32), Fraction(-3, 128)), "listed n=3 cumulants")
    equal(exact.cumulants(4, 2),
          (Fraction(0), Fraction(81, 32), Fraction(319, 1024)),
          "listed n=4 mean and variance")
    equal(exact.raw_moments(6, 0), (Fraction(1),), "zeroth raw moment")
    equal(exact.cumulants(6, 0), (Fraction(0),), "zeroth cumulant")
    equal(exact.raw_moments(1, 12), (Fraction(1),) + (Fraction(0),) * 12,
          "H_1=0 at maximum permitted order")
    equal(exact.cumulants(2, 12), (Fraction(0), Fraction(1)) + (Fraction(0),) * 11,
          "H_2=1 cumulants at maximum permitted order")
    equal(exact.raw_moment_totals(35, 6), independent_raw_totals(35, 6),
          "Euler versus ordinary derivatives")
    print("PASS exact raw moments and cumulants, strict-transition convention")


def test_factorial_domination() -> None:
    for n in range(1, 101):
        row = exact.stirling_row(n)
        falling = 1
        k_factorial = 1
        for k in range(n):
            if k:
                falling *= n - k + 1
                k_factorial *= k
            check((2 ** k) * k_factorial * row[n - k] <= falling ** 2,
                  "exact factorial domination inequality")
    print("PASS exact factorial domination n=1..100, k=0..n-1")


def test_exact_inverse() -> None:
    values = independent_values(24)
    equal(exact.threshold_inverse(1, max_n=2), 2, "inverse starts at n=2")
    targets = list(range(1, 501))
    for n in range(3, 24):
        targets.extend((values[n] - 1, values[n], values[n] + 1))
    for target in targets:
        n = exact.threshold_inverse(target, max_n=24)
        check(2 <= n <= 24 and values[n] >= target, "inverse upper threshold")
        check(n == 2 or values[n - 1] < target, "inverse minimality")
    failure = raises(exact.ThresholdNotReached, exact.threshold_inverse,
                     values[24] + 1, max_n=24)
    equal(failure.max_n, 24, "bounded inverse maximum")
    equal(failure.last_value, values[24], "bounded inverse exact endpoint")
    print("PASS exact inverse minimality and bounded-search failure")


def test_guards() -> None:
    for invalid in (True, False, "6", 1.0, None, -1, 0, 1001, 10 ** 700):
        raises(exact.InputError, exact.chain_value, invalid)
        raises(exact.InputError, exact.chain_numbers, invalid)
    for invalid in (-1, True, 1001):
        raises(exact.InputError, exact.stirling_row, invalid)
    raises(exact.InputError, exact.chain_polynomial, 151)
    raises(exact.InputError, exact.raw_moments, 601, 1)
    for invalid in (-1, True, 13, 10 ** 700):
        raises(exact.InputError, exact.raw_moments, 1, invalid)
        raises(exact.InputError, exact.cumulants, 1, invalid)
    for invalid in (0, -1, True, 1.0, "1", 10 ** exact.MAX_TARGET_DIGITS):
        raises(exact.InputError, exact.threshold_inverse, invalid)
    for invalid in (1, True, 1001, 10 ** 700):
        raises(exact.InputError, exact.threshold_inverse, 1, max_n=invalid)

    def forbidden_parse(*unused):
        raise TestFailure("invalid input reached integer parsing")

    with patch.object(exact, "int", forbidden_parse, create=True):
        for token in ("", "0", "1001", "9" * 700, "0001", "+1", "-1",
                      " 1", "1 ", "1_0", "1.0", "\u0661", "\uff11"):
            raises(exact.InputError, exact._parse_small, token, 1, 1000, "n")
        for token in ("", "0", "01", "-1", "1_0", "9" * 6001, "\u0661"):
            raises(exact.InputError, exact._parse_target, token)
    with patch.object(exact, "_parse_target", forbidden_parse):
        with redirect_stderr(StringIO()):
            equal(exact.main(["inverse", "9" * 6000, "--max-n", "1001"]), 2,
                  "search budget guarded before target parsing")
    with patch.object(exact, "_parser", forbidden_parse):
        with redirect_stderr(StringIO()):
            equal(exact.main(["value", "9" * 10000]), 2,
                  "overall command-line size guarded before argparse")
    for args in (("value", "1001"), ("polynomial", "151"),
                 ("moments", "601", "1"), ("moments", "2", "13"),
                 ("inverse", "0"), ("inverse", "9" * 6001),
                 ("inverse", "2", "--max-n", "2"),
                 ("value", "9" * 10000)):
        result = cli(*args)
        equal(result.returncode, 2, "CLI guarded nonzero status")
        check(result.stderr.startswith("error:") and not result.stdout,
              "CLI concise error without partial output")
        check("Traceback" not in result.stderr, "CLI guards avoid tracebacks")
    print("PASS API and CLI input/resource guards before integer parsing")


def test_decimal_formatting() -> None:
    examples = ((0, "0"), (1, "1"), (-1, "-1"),
                (10 ** 600, "1" + "0" * 600),
                (10 ** 1200 + 42, "1" + "0" * 1198 + "42"))
    for value, text in examples:
        equal(exact.integer_to_decimal(value), text, "decimal chunk boundary")
        equal(parse_decimal_independently(text), value, "independent decimal parse")
    rational = Fraction(-(10 ** 1200 + 7), 10 ** 900 + 1)
    text = exact.rational_to_decimal(rational)
    equal(parse_fraction_independently(text), rational, "large signed rational")
    raises(exact.InputError, exact.integer_to_decimal, True)
    raises(exact.InputError, exact.rational_to_decimal, 1)
    print("PASS 600-digit formatting chunks and exact rational formatting")


def test_real_cli_under_640_digit_cap() -> None:
    environment = dict(os.environ, PYTHONINTMAXSTRDIGITS="640")
    cap = subprocess.run(
        [sys.executable, "-c", "import sys; print(sys.get_int_max_str_digits())"],
        check=False, capture_output=True, text=True, env=environment, timeout=30,
    )
    equal((cap.returncode, cap.stdout.strip()), (0, "640"),
          "subprocess integer digit cap is genuinely 640")
    reference = independent_values(201)
    result = cli("value", "200")
    equal(result.returncode, 0, "large exact value CLI succeeds")
    equal(result.stderr, "", "successful value CLI stderr")
    digits = result.stdout.strip()
    check(len(digits) > 640, "computed output genuinely exceeds 640 digits")
    equal(parse_decimal_independently(digits), reference[200],
          "large exact value agrees with independent recurrence")
    result_again = cli("value", "200")
    equal(result_again.stdout, result.stdout, "CLI output is deterministic")
    inverse = cli("inverse", digits, "--max-n", "200")
    equal((inverse.returncode, inverse.stdout), (0, "200\n"),
          "large decimal input is safely parsed in real CLI")
    just_above = exact.integer_to_decimal(reference[200] + 1)
    inverse = cli("inverse", just_above, "--max-n", "201")
    equal((inverse.returncode, inverse.stdout), (0, "201\n"),
          "large inverse honors strict minimality")
    bounded = cli("inverse", just_above, "--max-n", "200")
    equal(bounded.returncode, 2, "large inverse bounded failure")

    statistics = cli("moments", "200", "4")
    equal(statistics.returncode, 0, "large rational moments CLI succeeds")
    equal(statistics.stderr, "", "successful moments CLI stderr")
    lines = statistics.stdout.splitlines()
    equal(len(lines), 7, "moments CLI row count")
    equal(lines[0], "n=200 z_n=" + digits + " convention=strict_transitions",
          "moments CLI exact normalizer and convention")
    equal(lines[1], "order\traw_moment\tcumulant", "moments CLI column labels")
    totals = independent_raw_totals(200, 4)
    moments = tuple(Fraction(total, totals[0]) for total in totals)
    kappas = independent_cumulants(moments)
    seen_large_rational_piece = False
    for r, line in enumerate(lines[2:]):
        fields = line.split("\t")
        equal(len(fields), 3, "moments CLI column count")
        equal(fields[0], str(r), "moments CLI order")
        equal(parse_fraction_independently(fields[1]), moments[r],
              "large raw moment independently verified")
        equal(parse_fraction_independently(fields[2]), kappas[r],
              "large cumulant independently verified")
        seen_large_rational_piece |= any(len(part.lstrip("-")) > 640
                                         for field in fields[1:]
                                         for part in field.split("/"))
    check(seen_large_rational_piece, "rational CLI really exceeds the cap")
    equal(cli("sequence", "6").stdout,
          "1\t1\n2\t1\n3\t4\n4\t32\n5\t436\n6\t9012\n",
          "deterministic sequence CLI")
    equal(cli("polynomial", "3").stdout, "0\t0\n1\t1\n2\t3\n",
          "deterministic polynomial CLI")
    print(f"PASS real CLI cap=640, z_200 has {len(digits)} digits, large rationals verified")


def main() -> None:
    test_partitions_and_polynomials()
    test_stirling_and_integer_recurrence()
    test_moments_and_cumulants()
    test_factorial_domination()
    test_exact_inverse()
    test_guards()
    test_decimal_formatting()
    test_real_cli_under_640_digit_cap()
    print("ALL EXACT LENGYEL TESTS PASS")


if __name__ == "__main__":
    main()
