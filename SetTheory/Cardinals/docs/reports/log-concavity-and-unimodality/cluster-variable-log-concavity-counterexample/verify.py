#!/usr/bin/env python3
"""Exact certificates for the annular single-lamination counterexample.

Python 3.10+, standard library only. All polynomial calculations use integers.
Run: python verify.py --write-data
Polynomial tuples store coefficients in increasing degree. This program checks
algebraic certificates; the geometric realization is proved in the article.
"""
from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path
from typing import Iterable

Poly = tuple[int, ...]
Matrix = tuple[tuple[int, ...], ...]
ONE: Poly = (1,)
ZERO: Poly = (0,)
B0: Matrix = ((0, 2), (-2, 0), (1, 0))


def trim(values: Iterable[int]) -> Poly:
    out = list(values)
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return tuple(out) if out else ZERO


def add(a: Poly, b: Poly) -> Poly:
    out = [0] * max(len(a), len(b))
    for i, v in enumerate(a):
        out[i] += v
    for i, v in enumerate(b):
        out[i] += v
    return trim(out)


def sub(a: Poly, b: Poly) -> Poly:
    return add(a, tuple(-v for v in b))


def scale(a: Poly, c: int) -> Poly:
    return trim(c * v for v in a)


def shift(a: Poly, k: int) -> Poly:
    if k < 0:
        raise ValueError("A polynomial shift must be nonnegative")
    return ZERO if a == ZERO else (0,) * k + a


def mul(a: Poly, b: Poly) -> Poly:
    if a == ZERO or b == ZERO:
        return ZERO
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    out[i + j] += x * y
    return trim(out)


def power(a: Poly, n: int) -> Poly:
    if n < 0:
        raise ValueError("Exponent must be nonnegative")
    result = ONE
    while n:
        if n & 1:
            result = mul(result, a)
        n >>= 1
        if n:
            a = mul(a, a)
    return result


def exact_div(a: Poly, b: Poly) -> Poly:
    """Divide in Z[q], raising on nonintegral quotient or nonzero remainder."""
    if b == ZERO:
        raise ZeroDivisionError("Zero polynomial divisor")
    if a == ZERO:
        return ZERO
    if len(a) < len(b):
        raise ArithmeticError("Polynomial division is not exact")
    work = list(a)
    out = [0] * (len(a) - len(b) + 1)
    while work and len(work) >= len(b):
        value, remainder = divmod(work[-1], b[-1])
        if remainder:
            raise ArithmeticError("Nonintegral polynomial quotient")
        offset = len(work) - len(b)
        out[offset] = value
        for j, coefficient in enumerate(b):
            work[offset + j] -= value * coefficient
        while work and work[-1] == 0:
            work.pop()
    if any(work):
        raise ArithmeticError("Nonzero polynomial remainder")
    return trim(out)


def coefficient(p: Poly, k: int) -> int:
    return p[k] if 0 <= k < len(p) else 0


def mutate_matrix(b: Matrix, k: int) -> Matrix:
    """Standard extended exchange-matrix mutation (zero-based k)."""
    rows, columns = len(b), len(b[0])
    if not 0 <= k < columns or any(len(row) != columns for row in b):
        raise ValueError("Invalid matrix or mutation direction")
    return tuple(tuple(
        -b[i][j] if i == k or j == k else
        b[i][j] + max(b[i][k], 0) * max(b[k][j], 0)
        - max(-b[i][k], 0) * max(-b[k][j], 0)
        for j in range(columns)) for i in range(rows))


def exchange_step(b: Matrix, x: tuple[Poly, ...], k: int
                  ) -> tuple[Matrix, tuple[Poly, ...]]:
    """Mutate a specialized geometric seed with one frozen variable q."""
    if len(b) != len(x) + 1 or len(b[0]) != len(x):
        raise ValueError("Expected exactly one frozen coefficient")
    positive, negative = ONE, ONE
    for i, row in enumerate(b):
        exponent = row[k]
        if not exponent:
            continue
        factor = (shift(ONE, abs(exponent)) if i == len(x)
                  else power(x[i], abs(exponent)))
        if exponent > 0:
            positive = mul(positive, factor)
        else:
            negative = mul(negative, factor)
    new_x = list(x)
    new_x[k] = exact_div(add(positive, negative), x[k])
    return mutate_matrix(b, k), tuple(new_x)


def seed_after(r: int) -> Matrix:
    b = B0
    for step in range(r):
        b = mutate_matrix(b, step % 2)
    return b


def sequence_linear(d: int, maximum_n: int) -> list[Poly]:
    if d < 1 or maximum_n < 0:
        raise ValueError("Require d >= 1 and maximum_n >= 0")
    out = [ONE, ONE]
    for n in range(1, maximum_n):
        out.append(sub(add(add(out[n], shift(out[n], 1)),
                           shift(out[n], d)), shift(out[n - 1], 1)))
    return out[:maximum_n + 1]


def sequence_nonlinear(d: int, maximum_n: int) -> list[Poly]:
    out = [ONE, ONE]
    for n in range(1, maximum_n):
        out.append(exact_div(add(mul(out[n], out[n]),
                                 shift(ONE, d + n - 1)), out[n - 1]))
    return out[:maximum_n + 1]


def sequence_mutations(d: int, maximum_n: int) -> list[Poly]:
    """Choose T_{d-1} as initial seed, THEN specialize its variables to 1."""
    b = seed_after(d - 1)
    x = (ONE, ONE)
    out = [ONE, ONE]
    for step in range(maximum_n - 1):
        k = (d - 1 + step) % 2
        b, x = exchange_step(b, x, k)
        out.append(x[k])
    return out[:maximum_n + 1]


def sequence_walks(d: int, maximum_n: int) -> list[Poly]:
    # Row vector (a,b) counts weighted paths from A to states A and B.
    a, b = ONE, ZERO
    out = [ONE, ONE]
    for _ in range(maximum_n - 1):
        a, b = (add(add(a, shift(a, d)), shift(b, 1)),
                add(shift(a, d), shift(b, 1)))
        out.append(a)
    return out[:maximum_n + 1]


def positive_formula(d: int, n: int) -> Poly:
    if n == 0:
        return ONE
    length = n - 1
    atom = add(ONE, shift(ONE, d))
    out = power(atom, length)
    for excursions in range(1, length // 2 + 1):
        for b_loops in range(length - 2 * excursions + 1):
            a_loops = length - 2 * excursions - b_loops
            multiplicity = (math.comb(a_loops + excursions, excursions)
                            * math.comb(b_loops + excursions - 1,
                                        excursions - 1))
            term = shift(power(atom, a_loops),
                         excursions * (d + 1) + b_loops)
            out = add(out, scale(term, multiplicity))
    return out


def fibonacci(n: int) -> int:
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def violations(p: Poly) -> list[int]:
    return [i for i in range(1, len(p) - 1)
            if p[i] ** 2 < p[i - 1] * p[i + 1]]


def require(condition: bool, description: str) -> None:
    if not condition:
        raise AssertionError(description)


def verify() -> dict[str, int | str]:
    counts: dict[str, int | str] = {}
    for r in range(201):
        b = seed_after(r)
        expected_row = ((r + 1, -r) if r % 2 == 0 else (-r, r + 1))
        require(b[2] == expected_row, f"Shear row at r={r}")
        require(b[:2] == tuple(tuple((-1) ** r * v for v in row)
                              for row in B0[:2]), f"Principal matrix at r={r}")
        for k in (0, 1):
            require(mutate_matrix(mutate_matrix(b, k), k) == b,
                    f"Matrix involution at r={r}, k={k}")
    counts["shear_rows_and_matrix_involutions"] = 201
    require(seed_after(1) == ((0, -2), (2, 0), (-1, 2)), "Initial certificate")
    b, x = seed_after(1), (ONE, ONE)
    for k in (1, 0, 1):
        previous_b, previous_x = b, x
        b, x = exchange_step(b, x, k)
        restored_b, restored_x = exchange_step(b, x, k)
        require((restored_b, restored_x) == (previous_b, previous_x),
                "Seed mutation is involutive")
    require(x[1] == (1, 0, 3, 2, 4, 2, 1), "P_4 exact coefficients")
    require(3 in violations(x[1]), "Positive-triple log-concavity failure")
    linear_cases = 0
    nonlinear_cases = 0
    formula_cases = 0
    for d in range(1, 13):
        linear = sequence_linear(d, 80)
        require(linear == sequence_walks(d, 80), f"Walk recurrence at d={d}")
        for n, p in enumerate(linear):
            require(all(v >= 0 for v in p), f"Positivity d={d}, n={n}")
            require(p[0] == 1, f"Constant coefficient d={d}, n={n}")
            expected_sum = 1 if n == 0 else fibonacci(2 * n - 1)
            require(sum(p) == expected_sum, f"Fibonacci specialization d={d}, n={n}")
            if d >= 2 and n >= 2:
                require(len(p) - 1 == d * (n - 1) and p[-1] == 1,
                        f"Monic degree d={d}, n={n}")
                require(all(coefficient(p, k) == 0 for k in range(1, d)),
                        f"Initial zero gap d={d}, n={n}")
                require(coefficient(p, d) == n - 1, "First coefficient")
                for s in range(1, d):
                    require(coefficient(p, d + s) == max(n - 1 - s, 0),
                            f"Low coefficient d={d}, n={n}, s={s}")
                require(coefficient(p, 2 * d) == math.comb(n - 1, 2)
                        + max(n - d - 1, 0), f"Coefficient at 2d, d={d}, n={n}")
            linear_cases += 1
        nonlinear = sequence_nonlinear(d, 32)
        mutated = sequence_mutations(d, 32)
        require(nonlinear == linear[:33] == mutated,
                f"Independent nonlinear and matrix verification d={d}")
        nonlinear_cases += len(nonlinear)
        for n in range(13):
            require(positive_formula(d, n) == linear[n],
                    f"Positive finite formula d={d}, n={n}")
            formula_cases += 1
        if d >= 2:
            p = linear[d + 1]
            triple = tuple(coefficient(p, k) for k in (2*d-2, 2*d-1, 2*d))
            require(triple == (2, 1, math.comb(d, 2)), "General positive triple")
            require(triple[1] ** 2 < triple[0] * triple[2], "General failure")
    for n, p in enumerate(sequence_linear(2, 160)):
        if n >= 3:
            require(3 in violations(p), f"Fixed-seed log-concavity failure n={n}")
        if n >= 4:
            require(p[2] > p[3] < p[4], f"Fixed-seed strict valley n={n}")
    counts["linear_walk_positivity_fibonacci_cases"] = linear_cases
    counts["nonlinear_and_actual_matrix_mutation_cases"] = nonlinear_cases
    counts["positive_finite_formula_cases"] = formula_cases
    counts["fixed_seed_log_concavity_failures_n_3_to_160"] = 158
    counts["fixed_seed_strict_valleys_n_4_to_160"] = 157
    counts["arithmetic"] = "exact integers; no floating-point calculations"
    counts["result"] = "PASS"
    return counts


def write_data(directory: Path, report: dict[str, int | str]) -> None:
    directory.mkdir(parents=True, exist_ok=True)
    seq = sequence_linear(2, 40)
    with (directory / "coefficients_d2.csv").open("w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["n", "degree", "coefficient"])
        for n, p in enumerate(seq):
            writer.writerows((n, i, v) for i, v in enumerate(p))
    with (directory / "row_sums_A001519.txt").open("w", encoding="utf-8") as f:
        f.write("# n P_n^(2)(1); same indexing as OEIS A001519\n")
        for n, p in enumerate(sequence_linear(2, 100)):
            f.write(f"{n} {sum(p)}\n")
    small = []
    b, x = seed_after(1), (ONE, ONE)
    for step, k in enumerate((1, 0, 1), 1):
        before_b = b
        b, x = exchange_step(b, x, k)
        small.append({"step": step, "mutation_label": k + 1,
                      "matrix_before": before_b, "matrix_after": b,
                      "new_coefficients_low_to_high": x[k]})
    data = {
        "reference_matrix": B0,
        "reference_lamination": "One unit-weight elementary curve L_alpha1",
        "reference_flip": 1,
        "chosen_initial_matrix": seed_after(1),
        "initial_mutable_specializations": [1, 1],
        "frozen_variable": "q",
        "mutations": small,
        "positive_triple": {"degrees": [2, 3, 4], "coefficients": [3, 2, 4],
                            "middle_squared": 4, "neighbor_product": 12},
        "general_family": [{"d": d, "n": d+1,
                            "coefficients": sequence_linear(d, d+1)[d+1],
                            "triple_degrees": [2*d-2, 2*d-1, 2*d],
                            "triple": [2, 1, math.comb(d, 2)]}
                           for d in range(2, 13)]
    }
    (directory / "certificates.json").write_text(json.dumps(data, indent=2) + "\n",
                                                encoding="utf-8")
    (directory / "verification.json").write_text(json.dumps(report, indent=2) + "\n",
                                                encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-data", action="store_true",
                        help="Regenerate deterministic JSON/CSV/text artifacts")
    parser.add_argument("--data-dir", type=Path,
                        default=Path(__file__).resolve().parent / "data")
    args = parser.parse_args()
    report = verify()
    if args.write_data:
        write_data(args.data_dir, report)
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
