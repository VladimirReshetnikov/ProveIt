#!/usr/bin/env python3
"""Independent finite sanity checks for the new arithmetic lemmas.

Python 3.10+, standard library only. No producer or polynomial compiler is
imported. These checks do not replace the unbounded mathematical proofs,
do not search for a ZFC refutation, and do not decide polynomial solvability.
The script is read-only unless --report is supplied. Explicit exceptions
make the same checks operative under python -O.
"""

from __future__ import annotations

import argparse
from collections import Counter
from itertools import combinations_with_replacement
import json
from math import comb, factorial, lcm, prod
from pathlib import Path


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def factor(n: int) -> Counter[int]:
    require(n >= 1, "factor requires a positive integer")
    answer: Counter[int] = Counter()
    d = 2
    while d * d <= n:
        while n % d == 0:
            answer[d] += 1
            n //= d
        d = 3 if d == 2 else d + 2
    if n > 1:
        answer[n] += 1
    return answer


def coefficient_vector(labels: tuple[int, ...]) -> list[int]:
    coefficients = [1]
    for label in labels:
        following = [0] * (len(coefficients) + 1)
        for k, value in enumerate(coefficients):
            following[k] += value
            following[k + 1] += label * value
        coefficients = following
    return coefficients


def check_lcm() -> dict:
    values = [1]
    for n in range(1, 501):
        values.append(lcm(values[-1], n))
        require(values[n] <= 4 ** (n - 1), f"LCM bound failed at {n}")
        if n >= 2:
            m = (n + 1) // 2
            numerator = values[m] * comb(n, n // 2)
            require(numerator % values[n] == 0,
                    f"LCM/binomial divisibility failed at {n}")
        if n >= 16:
            require(n ** n > values[n] ** 2,
                    f"Linear radius too small at {n}")
    return {"lcm_bound_and_recursive_divisibility_through": 500,
            "linear_radius_t_power_t_checked_from": 16}


def check_binomial_selectors() -> dict:
    cases = 0
    rows_checked = 0
    support_checked = 0
    examples = []
    for t in range(1, 9):
        least_common_multiple = lcm(*range(1, t + 1))
        threshold = least_common_multiple ** 2
        for radius in range(threshold, threshold + 21):
            b = comb(radius + t, t)
            exponents: Counter[int] = Counter()
            for i in range(1, t + 1):
                exponents.update(factor(radius + i))
            for prime, exponent in factor(factorial(t)).items():
                exponents[prime] -= exponent
            require(all(e >= 0 for e in exponents.values()),
                    f"Negative binomial valuation at t={t}, R={radius}")
            exponents = Counter({p: e for p, e in exponents.items() if e})
            require(prod(p ** e for p, e in exponents.items()) == b,
                    f"Factorization mismatch at t={t}, R={radius}")

            for i in range(1, t + 1):
                witnesses = [p ** e for p, e in exponents.items()
                             if p ** e > t and (radius + i) % (p ** e) == 0]
                require(bool(witnesses),
                        f"Missing row selector at t={t}, R={radius}, i={i}")
                rows_checked += 1
            for p, e in exponents.items():
                require(any((radius + i) % (p ** e) == 0
                            for i in range(1, t + 1)),
                        f"Unsupported full prime power at t={t}, R={radius}")
                support_checked += 1
            if t == 3 and radius == 37:
                examples.append({"t": t, "radius": radius, "binomial": b,
                                 "full_prime_powers": sorted(p ** e for p, e
                                                             in exponents.items())})
            cases += 1

    # This is a deliberate missing-hypothesis control, not a valid case.
    # t=2,R=1 has B=3. The factor R+1=2 has no selector from B.
    t, radius, b, power, c = 2, 1, 3, 9, 1
    require(comb(radius + t, t) == b, "Counterexample binomial mismatch")
    require((c + radius + 1) % b == 0, "Counterexample index mismatch")
    require(comb(c, t) % power == 0, "Counterexample range mismatch")
    require((c - 1) ** 2 % power == 0, "Counterexample local congruence mismatch")
    require((0 - 1) ** 2 != 0 and (radius + 1) % b != 0,
            "Missing-hypothesis control was not detected")
    return {"threshold_and_nearby_cases": cases,
            "individual_rows_checked": rows_checked,
            "full_prime_power_support_checks": support_checked,
            "example": examples,
            "missing_size_hypothesis_control_detected": True}


def check_odd_binomials() -> dict:
    checked = []
    for t in (16, 20, 24, 28, 32, 40, 48, 64, 80, 100):
        f = t ** t
        b = comb(f + t, t)
        require(f % 2 == 0, f"F unexpectedly odd at {t}")
        require(b % 2 == 1, f"B unexpectedly even at {t}")
        # Check the exact cofinal multiplier recipe against t!, too.
        odd_part = factorial(t)
        while odd_part % 2 == 0:
            odd_part //= 2
        for odd_multiple in (odd_part, 3 * odd_part, 5 * odd_part):
            y = f * odd_multiple
            require(y % factorial(t) == 0 and y % 2 == 0,
                    f"Affine beta divisibility failed at {t}")
            require(y == f * (2 * ((odd_multiple - 1) // 2) + 1),
                    f"Affine beta parametrization failed at {t}")
        checked.append({"t": t, "F_bits": f.bit_length(),
                        "B_bits": b.bit_length()})
    return {"actual_binomial_parity_checks": checked,
            "affine_beta_completions_per_horizon": 3}


def check_label_coefficients_and_injectivity() -> dict:
    coefficient_counts = []
    for t in range(1, 9):
        f = t ** t
        values: dict[int, tuple[int, ...]] = {}
        count = 0
        for m in range(t + 1):
            for labels in combinations_with_replacement(range(1, t + 1), m):
                coefficients = coefficient_vector(labels)
                require(all(1 <= a <= t ** m for a in coefficients),
                        f"Coefficient bound failed at t={t}, labels={labels}")
                value = prod(1 + label * f for label in labels)
                require(value == sum(a * f ** k for k, a in enumerate(coefficients)),
                        "Direct product and polynomial evaluation disagree")
                require(value not in values or values[value] == labels,
                        f"Label collision at t={t}: {labels} and {values.get(value)}")
                values[value] = labels
                count += 1
        coefficient_counts.append({"t": t, "multisets": count})

    unequal_count_checks = []
    for t in range(1, 6):
        f = t ** t
        small_products: dict[int, tuple[int, ...]] = {}
        for m in range(t + 1):
            for labels in combinations_with_replacement(range(1, t + 1), m):
                small_products[prod(1 + label * f for label in labels)] = labels
        count = 0
        for m in range(t + 1, 2 * t + 2):
            for labels in combinations_with_replacement(range(1, t + 1), m):
                value = prod(1 + label * f for label in labels)
                require(value not in small_products,
                        f"Unequal-factor-count collision at t={t}")
                count += 1
        unequal_count_checks.append({"t": t, "larger_multisets": count})

    return {"coefficient_and_equal_count_injectivity": coefficient_counts,
            "total_small_multisets": sum(x["multisets"] for x in coefficient_counts),
            "unequal_factor_count_checks": unequal_count_checks}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path,
                        help="Optional path for a JSON receipt; otherwise stdout only")
    arguments = parser.parse_args()
    result = {
        "schema": "finite_arithmetic_sanity_v1",
        "scope": "Finite checks only; unbounded proofs are supplied separately.",
        "status": "passed",
        "lcm_and_radius": check_lcm(),
        "binomial_crt": check_binomial_selectors(),
        "parity_and_beta": check_odd_binomials(),
        "label_separation": check_label_coefficients_and_injectivity(),
    }
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if arguments.report is not None:
        arguments.report.parent.mkdir(parents=True, exist_ok=True)
        arguments.report.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()

