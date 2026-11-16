#!/usr/bin/env python3
"""Reproduce the report's small, exact Bell-number numerical certificates.

All arithmetic is integer arithmetic.  This is a checker for the stated
ground instances, not a generic iPRA proof checker.  It computes only through
B_1000 and tests primality only through index 13.
"""

import hashlib
import json
from math import isqrt


def bell_numbers_through(limit):
    """B_(n+1) = sum_(k=0)^n binom(n,k) B_k, with exact binomial updates."""
    values = [1]
    for n in range(limit):
        total = 0
        choose = 1
        for k in range(n + 1):
            total += choose * values[k]
            if k < n:
                numerator = choose * (n - k)
                assert numerator % (k + 1) == 0
                choose = numerator // (k + 1)
        values.append(total)
    return values


def primality_certificate(value):
    root = isqrt(value)
    assert root * root <= value < (root + 1) * (root + 1)
    divisor = next((d for d in range(2, root + 1) if value % d == 0), None)
    return {
        "value": value,
        "integer_square_root": root,
        "square_root_inequalities_verified": True,
        "prime": value >= 2 and divisor is None,
        "smallest_divisor_if_composite": divisor,
        "less_than_two": value < 2,
        "trial_division_range": [2, root],
    }


def main():
    values = bell_numbers_through(1000)
    expected_initial = [1, 1, 2, 5, 15, 52, 203, 877,
                        4140, 21147, 115975, 678570, 4213597,
                        27644437, 190899322, 1382958545]
    assert values[:16] == expected_initial

    digit_certificates = []
    for index, digits in [(1, 1), (10, 6), (100, 116), (1000, 1928)]:
        value = values[index]
        assert 10 ** (digits - 1) <= value < 10 ** digits
        decimal = str(value)
        assert len(decimal) == digits
        digit_certificates.append({
            "index": index,
            "decimal_digits": digits,
            "lower_bound_power_of_ten": digits - 1,
            "upper_bound_power_of_ten": digits,
            "integer_inequalities_verified": True,
            "first_at_most_32_digits": decimal[:32],
            "last_at_most_32_digits": decimal[-32:],
            "sha256_of_decimal_without_newline": hashlib.sha256(decimal.encode("ascii")).hexdigest(),
        })

    primality = [{"index": n, **primality_certificate(values[n])} for n in range(14)]
    assert [entry["index"] for entry in primality if entry["prime"]] == [2, 3, 7, 13]
    report = {
        "status": "all exact ground checks passed",
        "not_a_formal_proof_checker": True,
        "bell_recurrence_computed_through": 1000,
        "initial_values_index_0_through_15": expected_initial,
        "decimal_digit_certificates": digit_certificates,
        "primality_certificates_index_0_through_13": primality,
        "prime_indices_among_0_through_13": [2, 3, 7, 13],
        "scope": "No Bell number beyond index 13 is subjected to a primality claim or test here.",
    }
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
