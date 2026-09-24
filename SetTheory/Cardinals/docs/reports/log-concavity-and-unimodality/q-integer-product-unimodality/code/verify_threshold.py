#!/usr/bin/env python3
"""Exact checks for the binomial-smoothing article. Python 3.9+; no dependencies.

Run from any directory:
    python code/verify_threshold.py

The unbounded threshold theorem is proved in report.tex. Finite checks here
are regression tests, not a substitute for that proof. Degree <= 9 is a finite,
complete search and does certify the stated minimum-degree counterexample.
"""
from __future__ import annotations

import argparse
import csv
import itertools
import json
import platform
from pathlib import Path
from typing import Iterator, Sequence, Tuple


def require(condition: bool, message: str) -> None:
    """Do not use assert: verification must also run under python -O."""
    if not condition:
        raise RuntimeError(message)


def binomial_row(n: int) -> list[int]:
    if n < 0:
        raise ValueError("n must be nonnegative")
    row = [1]
    for j in range(n):
        value, remainder = divmod(row[-1] * (n - j), j + 1)
        require(remainder == 0, "binomial recurrence was not integral")
        row.append(value)
    return row


def two_spike(n: int, r: int) -> list[int]:
    """Coefficients of (1+q)^n (1+q^r), from the binomial theorem."""
    if r < 1:
        raise ValueError("r must be positive")
    row = binomial_row(n)
    coefficients = [0] * (n + r + 1)
    for j, value in enumerate(row):
        coefficients[j] += value
        coefficients[j + r] += value
    return coefficients


def smooth(coefficients: Sequence[int]) -> list[int]:
    """Multiply by 1+q using only additions."""
    out = [0] * (len(coefficients) + 1)
    for j, value in enumerate(coefficients):
        out[j] += value
        out[j + 1] += value
    return out


def is_unimodal(coefficients: Sequence[int]) -> bool:
    """Definition-based test, independent of symmetry."""
    descending = False
    for left, right in zip(coefficients, coefficients[1:]):
        if right < left:
            descending = True
        elif right > left and descending:
            return False
    return True


def symmetric_test(coefficients: Sequence[int]) -> bool:
    return (
        list(coefficients) == list(reversed(coefficients))
        and all(coefficients[j - 1] <= coefficients[j]
                for j in range(1, (len(coefficients) - 1) // 2 + 1))
    )


def multiply_q_integer(coefficients: Sequence[int], a: int,
                       step: int = 1) -> list[int]:
    """Multiply by [a]_(q^step), via a sliding sum in each residue class.

    (1-q^step) Q = (1-q^(a*step)) P gives the recurrence below.
    """
    if a < 1 or step < 1:
        raise ValueError("a and step must be positive")
    out = [0] * (len(coefficients) + (a - 1) * step)
    for j in range(len(out)):
        value = coefficients[j] if j < len(coefficients) else 0
        if j >= step:
            value += out[j - step]
        old_index = j - a * step
        if 0 <= old_index < len(coefficients):
            value -= coefficients[old_index]
        out[j] = value
    return out


def q_product(a: Sequence[int], b: int, r: int) -> list[int]:
    out = [1]
    for length in a:
        out = multiply_q_integer(out, length)
    return multiply_q_integer(out, b, r)


def q_product_by_tuples(a: Sequence[int], b: int, r: int) -> list[int]:
    """Independent direct counting: no polynomial multiplication."""
    degree = sum(length - 1 for length in a) + r * (b - 1)
    out = [0] * (degree + 1)
    for values in itertools.product(*(range(length) for length in a), range(b)):
        out[sum(values[:-1]) + r * values[-1]] += 1
    return out


def partitions(total: int, least: int = 1) -> Iterator[Tuple[int, ...]]:
    """Every nondecreasing partition of total exactly once."""
    if total == 0:
        yield ()
    else:
        for part in range(least, total + 1):
            for tail in partitions(total - part, part):
                yield (part,) + tail


def normalized_parameters(degree: int) -> Iterator[Tuple[int, int, Tuple[int, ...]]]:
    # b=1 cannot violate necessity. All a_i=1 give a visibly nonunimodal
    # sparse polynomial. Delete trivial factors and sort the other factors.
    for r in range(2, degree):
        for b in range(2, 2 + (degree - 1) // r):
            ordinary_degree = degree - r * (b - 1)
            if ordinary_degree < 1:
                continue
            for partition in partitions(ordinary_degree):
                yield r, b, tuple(part + 1 for part in partition)


def proposed_condition(a: Sequence[int], b: int, r: int) -> bool:
    return any(length % r == 0 for length in a) or b <= 1 + sum(
        length // r for length in a
    )


def plateau(coefficients: Sequence[int]) -> tuple[int, int]:
    maximum = max(coefficients)
    modes = [j for j, value in enumerate(coefficients) if value == maximum]
    require(modes == list(range(modes[0], modes[-1] + 1)), "disconnected modes")
    return modes[0], modes[-1]


def verify(out: Path, max_shift: int, degree_bound: int,
           grid_max_shift: int, grid_max_n: int) -> dict:
    out.mkdir(parents=True, exist_ok=True)
    expected = [1, 6, 15, 21, 21, 21, 21, 15, 6, 1]
    a = (2,) * 6
    witness = two_spike(6, 3)
    require(witness == expected == q_product(a, 2, 3)
            == q_product_by_tuples(a, 2, 3), "witness disagreement")
    require(is_unimodal(witness), "witness not unimodal")
    require(not proposed_condition(a, 2, 3), "witness meets condition")
    witness_record = {
        "r": 3, "b": 2, "a": list(a), "degree": 9,
        "coefficients": witness,
        "first_differences": [witness[j] - witness[j - 1]
                              for j in range(1, len(witness))],
        "claimed_necessary_condition": False,
        "necessity_clause_applies": True,
        "unimodal": True,
        "source": "Connelly et al., arXiv:2605.12822v1, Conjecture 5.4, p. 14"
    }
    (out / "counterexample.json").write_text(
        json.dumps(witness_record, indent=2) + "\n", encoding="utf-8")

    # Full rectangular grid. Generate rows incrementally and compare against
    # the independent binomial-row expression at every point.
    grid_count = 0
    for r in range(2, grid_max_shift + 1):
        iterative = [1] + [0] * (r - 1) + [1]
        for n in range(grid_max_n + 1):
            c = two_spike(n, r)
            require(c == iterative, f"coefficient disagreement n={n}, r={r}")
            actual = is_unimodal(c)
            require(actual == symmetric_test(c), "unimodality-test disagreement")
            require(actual == (n >= r * r - 3),
                    f"threshold mismatch n={n}, r={r}")
            grid_count += 1
            iterative = smooth(iterative)

    # Threshold and adjacent rows, well beyond the rectangular grid.
    threshold_rows = []
    boundary_count = 0
    central_identities = 0
    ratio_checks = 0
    for r in range(2, max_shift + 1):
        critical = r * r - 3
        current = two_spike(critical - 1, r)
        require(not is_unimodal(current), f"lower boundary passed r={r}")
        boundary_count += 1
        below = critical - 1
        m = (below + r) // 2
        central_drop = current[m] - current[m - 1]
        if r >= 3:
            row = binomial_row(below)
            require(central_drop * (m + 1) * (below - m + 1)
                    == row[m] * (below + 2 - r * r), "central identity failed")
            require(central_drop < 0, "central obstruction missing")
            central_identities += 1
        modes_at_threshold = None
        for offset, width in enumerate((4, 3, 2, 1, 2)):
            n = critical + offset
            current = smooth(current)
            require(current == two_spike(n, r), "boundary recurrence disagreement")
            require(is_unimodal(current) and symmetric_test(current),
                    f"upper boundary failed n={n}, r={r}")
            modes = plateau(current)
            require(modes[1] - modes[0] + 1 == width, "plateau width mismatch")
            if offset == 0:
                modes_at_threshold = modes
                for j in range(1, modes[0] + 1):
                    require(current[j] > current[j - 1], "non-strict left flank")
            boundary_count += 1
        if r >= 3:
            n = critical
            row = binomial_row(n)
            d = [row[j] - (row[j - 1] if j else 0) for j in range(n + 1)]
            T = (n + 1 - r) // 2
            # Compare R_t >= R_(t+1) using integer cross-multiplication.
            first_j = (n + 1) // 2 + 1
            for t in range(first_j - r, T):
                y = 2 * T - t
                require(min(d[t], d[y], d[t + 1], d[y - 1]) > 0,
                        "ratio denominator not positive")
                require(d[t] * d[y - 1] >= d[t + 1] * d[y],
                        "ratio monotonicity failed")
                ratio_checks += 1
        threshold_rows.append({
            "r": r, "critical_n": critical, "below_n": below,
            "below_central_difference": central_drop,
            "critical_degree": critical + r,
            "plateau_start": modes_at_threshold[0],
            "plateau_end": modes_at_threshold[1]
        })
    with (out / "thresholds.csv").open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=list(threshold_rows[0]))
        writer.writeheader()
        writer.writerows(threshold_rows)

    # Exhaustive degree-bounded test. Independent tuple counting at degree <= 9.
    all_cases = []
    degree_summary = []
    failures = []
    tuple_cases = 0
    tuple_objects = 0
    for degree in range(1, degree_bound + 1):
        case_count = necessity_failures = sufficiency_failures = 0
        for r, b, factors in normalized_parameters(degree):
            c = q_product(factors, b, r)
            require(len(c) == degree + 1, "wrong product degree")
            require(all(value >= 0 for value in c), "negative counting coefficient")
            if degree <= 9:
                direct = q_product_by_tuples(factors, b, r)
                require(c == direct, "tuple-counting disagreement")
                tuple_cases += 1
                tuple_objects += sum(direct)
            actual = is_unimodal(c)
            require(actual == symmetric_test(c), "unimodality-test disagreement")
            condition = proposed_condition(factors, b, r)
            necessity_applies = len(factors) <= 3 or r <= 3
            bad_n = necessity_applies and actual and not condition
            bad_s = condition and not actual
            case_count += 1
            necessity_failures += int(bad_n)
            sufficiency_failures += int(bad_s)
            record = {
                "degree": degree, "r": r, "b": b,
                "a": json.dumps(factors), "k": len(factors),
                "condition": int(condition), "necessity_applies": int(necessity_applies),
                "unimodal": int(actual), "necessity_counterexample": int(bad_n),
                "sufficiency_counterexample": int(bad_s),
                "coefficients": json.dumps(c)
            }
            all_cases.append(record)
            if bad_n:
                failures.append(record)
        degree_summary.append({
            "degree": degree, "normalized_cases": case_count,
            "necessity_counterexamples": necessity_failures,
            "sufficiency_counterexamples": sufficiency_failures
        })
    if degree_bound >= 9:
        first = [record for record in failures if record["degree"] <= 9]
        require(len(first) == 1 and first[0]["degree"] == 9
                and first[0]["r"] == 3 and first[0]["b"] == 2
                and json.loads(first[0]["a"]) == [2] * 6,
                "minimum-degree certificate disagreed")
    for name, rows in (("degree_search.csv", all_cases),
                       ("degree_summary.csv", degree_summary)):
        with (out / name).open("w", newline="", encoding="utf-8") as f:
            writer = csv.DictWriter(f, fieldnames=list(rows[0]))
            writer.writeheader()
            writer.writerows(rows)

    report = {
        "status": "PASS",
        "arithmetic": "arbitrary-precision integers only",
        "python": platform.python_version(),
        "grid": {"r_min": 2, "r_max": grid_max_shift,
                 "n_min": 0, "n_max": grid_max_n, "cases": grid_count},
        "boundary": {"r_min": 2, "r_max": max_shift,
                     "offsets_from_r_squared_minus_3": [-1, 0, 1, 2, 3, 4],
                     "cases": boundary_count},
        "central_identity_checks": central_identities,
        "ratio_cross_multiplication_checks": ratio_checks,
        "degree_search": {
            "degree_max": degree_bound, "normalized_cases": len(all_cases),
            "direct_tuple_cross_checks": tuple_cases,
            "directly_enumerated_objects": tuple_objects,
            "necessity_counterexamples": len(failures),
            "minimum_counterexample_degree": min((r["degree"] for r in failures), default=None),
            "sufficiency_counterexamples": sum(r["sufficiency_counterexample"] for r in all_cases)
        },
        "scope": "Finite regression tests plus a complete degree-bounded search; the infinite theorem has a written proof."
    }
    (out / "verification_report.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8")
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data")
    parser.add_argument("--max-shift", type=int, default=100)
    parser.add_argument("--degree-bound", type=int, default=9)
    parser.add_argument("--grid-max-shift", type=int, default=14)
    parser.add_argument("--grid-max-n", type=int, default=250)
    args = parser.parse_args()
    if args.max_shift < 3 or args.degree_bound < 3 or args.grid_max_shift < 2 or args.grid_max_n < 0:
        parser.error("Require max-shift >= 3, degree-bound >= 3, grid-max-shift >= 2, grid-max-n >= 0")
    report = verify(args.out, args.max_shift, args.degree_bound,
                    args.grid_max_shift, args.grid_max_n)
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
