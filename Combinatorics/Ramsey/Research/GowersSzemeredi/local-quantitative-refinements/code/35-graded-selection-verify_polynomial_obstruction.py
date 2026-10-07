#!/usr/bin/env python3
"""Exact finite checks for the graded polynomial divisibility construction.

Uses only the Python standard library.  The exhaustive residue checks are
finite certificates for the listed examples, not substitutes for the general
proof.  Run from any directory.  By default, print a short summary; use
--output PATH to write the complete JSON report to an explicitly chosen path.
"""

import argparse
from fractions import Fraction
from math import isqrt, prod
from pathlib import Path
import json


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def is_prime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    return all(n % a for a in range(3, isqrt(n) + 1, 2))


def next_prime(n):
    while not is_prime(n):
        n += 1
    return n


def arc_span(values, modulus):
    values = sorted(values)
    gaps = [b - a for a, b in zip(values, values[1:])]
    gaps.append(modulus + values[0] - values[-1])
    return modulus - max(gaps)


def semigroup_table(lengths, limit):
    reachable = [False] * (limit + 1)
    reachable[0] = True
    for n in range(1, limit + 1):
        reachable[n] = any(n >= u and reachable[n - u] for u in lengths)
    return reachable


def check_case(degree, length, epsilon, primes):
    require(len(primes) == degree, "One denominator per degree is required")
    require(len(set(primes)) == degree, "Denominators must be distinct")
    require(length >= degree + 1, "Too few phase samples")
    require(epsilon < Fraction(1, 2**degree), "Small-arc condition failed")
    margins = []
    for j, p in enumerate(primes, 1):
        h = (length - 1) // j
        require(is_prime(p) and p > j, "Invalid prime denominator")
        margin = h**j - p * 2**(j - 1) * epsilon
        require(margin > 0, "Strict leading-coefficient condition failed")
        margins.append(str(margin))

    period = prod(primes)
    coefficients = [period // p for p in primes]
    values = [
        sum(c * n**j for j, c in enumerate(coefficients, 1)) % period
        for n in range(period)
    ]
    good = 0
    for step in range(period):
        for start in range(period):
            span = arc_span(
                [values[(start + t * step) % period] for t in range(length)],
                period,
            )
            flat = span * epsilon.denominator <= epsilon.numerator * period
            require(flat == (step == 0), "Unexpected flat residue progression")
            good += flat
    require(good == period, "Incorrect number of flat pairs")

    conductor = length * (length - 1)
    limit = conductor + 2 * length
    reachable = semigroup_table((length, length + 1), limit)
    # An independent two-variable enumeration checks the dynamic program.
    direct = {
        a * length + b * (length + 1)
        for a in range(limit // length + 1)
        for b in range(limit // (length + 1) + 1)
        if a * length + b * (length + 1) <= limit
    }
    require(all(reachable[n] == (n in direct) for n in range(limit + 1)),
            "Semigroup calculations disagree")
    require(not reachable[conductor - 1], "The last gap is representable")
    require(all(reachable[conductor:]), "A post-conductor gap was found")
    require(reachable[conductor], "Threshold residue chains cannot be tiled")

    return {
        "degree": degree,
        "minimum_length": length,
        "tolerance": str(epsilon),
        "primes_by_degree": primes,
        "strict_prime_margins": margins,
        "period": period,
        "start_step_pairs_tested": period**2,
        "good_pairs": good,
        "good_steps_mod_period": [0],
        "allowed_lengths": [length, length + 1],
        "semigroup_conductor": conductor,
        "bad_interval_length": period * conductor - 1,
        "exact_partition_threshold": period * conductor,
        "first_interval_length_with_one_good_cell": period * (length - 1) + 1,
    }


def check_prime_embedding():
    # The rational example is rigid at radius 1/16.  Approximate it at
    # radius 1/32 in a prime field, checking every candidate length-3 AP
    # inside the prohibited interval of 1301 integer points.
    interval = 1301
    epsilon = Fraction(1, 32)
    primes = [31, 7]
    period = prod(primes)
    error_numerator = (interval - 1) + (interval - 1)**2
    lower = error_numerator * epsilon.denominator // epsilon.numerator
    modulus = next_prime(max(2 * interval + 1, lower))
    require(modulus > 2 * interval, "Short-interval lifting condition failed")
    coefficients = [(2 * modulus + p) // (2 * p) for p in primes]
    require(all(abs(Fraction(a, modulus) - Fraction(1, p))
                <= Fraction(1, 2 * modulus)
                for a, p in zip(coefficients, primes)),
            "Nearest coefficient estimate failed")
    require(Fraction(error_numerator, 2 * modulus) <= epsilon / 2,
            "Uniform phase approximation bound failed")
    values = [
        sum(c * n**j for j, c in enumerate(coefficients, 1)) % modulus
        for n in range(interval)
    ]
    tested = 0
    good = 0
    good_steps = set()
    for step in range(1, (interval - 1) // 2 + 1):
        for start in range(interval - 2 * step):
            tested += 1
            span = arc_span([values[start + t * step] for t in range(3)], modulus)
            if span * epsilon.denominator <= epsilon.numerator * modulus:
                good += 1
                good_steps.add(step)
                require(step % period == 0,
                        "Prime approximation admitted a prohibited step")
    return {
        "interval_length": interval,
        "prime_modulus": modulus,
        "coefficients_by_degree": coefficients,
        "tolerance": str(epsilon),
        "uniform_phase_error_bound": str(Fraction(error_numerator, 2 * modulus)),
        "candidate_progressions_tested": tested,
        "good_progressions": good,
        "good_steps": sorted(good_steps),
        "all_good_steps_divisible_by": period,
        "claim_scope": "Only the specified integer interval; no global period is claimed",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output", type=Path,
        help="Write the complete exact verification record as JSON",
    )
    arguments = parser.parse_args()
    cases = [
        check_case(2, 3, Fraction(1, 16), [31, 7]),
        check_case(2, 4, Fraction(1, 16), [43, 7]),
        check_case(3, 4, Fraction(1, 64), [5, 7, 11]),
    ]
    report = {
        "status": "passed",
        "arithmetic": "integer residues and exact rational comparisons",
        "cases": cases,
        "total_periodic_pairs_tested": sum(c["start_step_pairs_tested"] for c in cases),
        "prime_embedding": check_prime_embedding(),
        "scope": "Exact finite examples; general theorems are proved in the article",
    }
    if arguments.output is not None:
        arguments.output.parent.mkdir(parents=True, exist_ok=True)
        arguments.output.write_text(
            json.dumps(report, indent=2) + "\n", encoding="utf-8",
        )
    print(
        f"Passed {report['total_periodic_pairs_tested']:,} exact periodic "
        "start/step checks across three examples."
    )
    print(
        f"Passed {report['prime_embedding']['candidate_progressions_tested']:,} "
        "exact prime-modulus progression checks and the semigroup checks."
    )
    if arguments.output is not None:
        print("JSON verification record:", arguments.output)


if __name__ == "__main__":
    main()
