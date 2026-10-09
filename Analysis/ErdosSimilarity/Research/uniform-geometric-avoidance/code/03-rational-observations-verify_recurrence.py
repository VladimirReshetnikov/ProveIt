#!/usr/bin/env python3
"""Exact checks for norm sampling of oscillatory recurrence sequences.

Run from any directory:
    python verification/verify_recurrence.py

Only the Python standard library is required. All mathematical comparisons use
fractions.Fraction. The checks verify representative algebra, boundary cases,
and the normalization/sign conventions used in the article. They do not prove
the theorem for a continuum of parameters and do not construct routing tables.
"""

from __future__ import annotations

import argparse
import itertools
import json
from dataclasses import dataclass
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
from typing import Callable


Matrix = list[list[F]]
Vector = list[F]


def identity(n: int) -> Matrix:
    return [[F(i == j) for j in range(n)] for i in range(n)]


def transpose(a: Matrix) -> Matrix:
    return [list(row) for row in zip(*a)]


def matmul(a: Matrix, b: Matrix) -> Matrix:
    return [
        [sum((x * y for x, y in zip(row, col)), F(0)) for col in zip(*b)]
        for row in a
    ]


def matvec(a: Matrix, v: Vector) -> Vector:
    return [sum((x * y for x, y in zip(row, v)), F(0)) for row in a]


def add(a: Matrix, b: Matrix, multiplier: F = F(1)) -> Matrix:
    return [
        [x + multiplier * y for x, y in zip(ra, rb)]
        for ra, rb in zip(a, b)
    ]


def scale(a: Matrix, c: F) -> Matrix:
    return [[c * x for x in row] for row in a]


def quadratic(v: Vector, p: Matrix) -> F:
    return sum((x * y for x, y in zip(v, matvec(p, v))), F(0))


def determinant(a: Matrix) -> F:
    b = [row[:] for row in a]
    value = F(1)
    for col in range(len(b)):
        pivot = next((i for i in range(col, len(b)) if b[i][col]), None)
        if pivot is None:
            return F(0)
        if pivot != col:
            b[pivot], b[col] = b[col], b[pivot]
            value = -value
        diagonal = b[col][col]
        value *= diagonal
        for i in range(col + 1, len(b)):
            ratio = b[i][col] / diagonal
            for j in range(col + 1, len(b)):
                b[i][j] -= ratio * b[col][j]
    return value


def is_psd(a: Matrix) -> bool:
    """Exact PSD test using all principal minors (matrices have order <=4)."""
    if a != transpose(a):
        return False
    for size in range(1, len(a) + 1):
        for indices in itertools.combinations(range(len(a)), size):
            if determinant([[a[i][j] for j in indices] for i in indices]) < 0:
                return False
    return True


def solve_linear(a: Matrix, rhs: Vector) -> Vector:
    b = [row[:] + [r] for row, r in zip(a, rhs)]
    n = len(rhs)
    for col in range(n):
        pivot = next(i for i in range(col, n) if b[i][col])
        b[col], b[pivot] = b[pivot], b[col]
        divisor = b[col][col]
        b[col] = [x / divisor for x in b[col]]
        for i in range(n):
            if i != col:
                multiplier = b[i][col]
                b[i] = [x - multiplier * y for x, y in zip(b[i], b[col])]
    return [b[i][-1] for i in range(n)]


def solve_lyapunov(a: Matrix) -> Matrix:
    """Solve P-A^T P A=I in the symmetric matrix entries, exactly."""
    n = len(a)
    positions = [(i, j) for i in range(n) for j in range(i, n)]
    basis = []
    for i, j in positions:
        e = [[F(0) for _ in range(n)] for _ in range(n)]
        e[i][j] = e[j][i] = F(1)
        basis.append(e)
    images = [add(e, matmul(matmul(transpose(a), e), a), F(-1)) for e in basis]
    equations = [[image[i][j] for image in images] for i, j in positions]
    coefficients = solve_linear(equations, [F(i == j) for i, j in positions])
    p = [[F(0) for _ in range(n)] for _ in range(n)]
    for coefficient, e in zip(coefficients, basis):
        p = add(p, e, coefficient)
    return p


def companion(coefficients: list[F]) -> Matrix:
    n = len(coefficients)
    a = [[F(0) for _ in range(n)] for _ in range(n)]
    for i in range(n - 1):
        a[i][i + 1] = F(1)
    a[-1] = coefficients[:]
    return a


def complex_multiply(z: tuple[F, F], w: tuple[F, F]) -> tuple[F, F]:
    return z[0] * w[0] - z[1] * w[1], z[0] * w[1] + z[1] * w[0]


def rational_complex_term(n: int) -> F:
    z = (F(1), F(0))
    for _ in range(n):
        z = complex_multiply(z, (F(3, 10), F(2, 5)))
    return complex_multiply((F(1, 2), F(3, 8)), z)[0]


def quarter_turn_cos(n: int) -> F:
    return F((1, 0, -1, 0)[n % 4])


def ceiling(q: F) -> int:
    return -(-q.numerator // q.denominator)


@dataclass
class Example:
    slug: str
    title: str
    a: Matrix
    p: Matrix
    w: Vector
    alpha: F
    beta: F
    metric_bound: int
    expected: Callable[[int], F]
    description: str

    @property
    def dimension(self) -> int:
        return len(self.w)

    @property
    def c(self) -> F:
        return self.alpha / (3 * self.dimension * self.metric_bound)

    @property
    def q(self) -> F:
        q = F(1, 2)
        threshold = min(self.c / 2, self.alpha ** self.dimension, F(1, 8))
        while q >= threshold:
            q /= 2
        return q

    @property
    def crossing_bound(self) -> int:
        t, value = 0, F(1)
        while value > self.q:
            value *= self.beta
            t += 1
        return t


def examples() -> list[Example]:
    a0 = companion([F(-1, 4), F(0)])
    a1 = companion([F(-1, 4), F(3, 5)])
    a2 = companion([F(-1, 16), F(0), F(-1, 2), F(0)])
    raw_p = solve_lyapunov(a2)
    raw_w = [F(1), F(0), F(-3, 4), F(0)]
    raw_energy = quadratic(raw_w, raw_p)
    divisor = isqrt(ceiling(raw_energy))
    while divisor * divisor < raw_energy:
        divisor += 1
    normalized_p = scale(raw_p, F(divisor * divisor) / raw_energy)
    normalized_w = [x / divisor for x in raw_w]
    propagated_p = matmul(matmul(transpose(a2), normalized_p), a2)
    alpha = F(1, 2)
    while not is_psd(add(propagated_p, normalized_p, -(alpha * alpha))):
        alpha /= 2
    beta = F(1, 2)
    while not is_psd(add(scale(normalized_p, beta * beta), propagated_p, F(-1))):
        beta = (1 + beta) / 2
    return [
        Example(
            "quarter_turn", "Complex roots; exact zeros", a0,
            [[F(1), F(0)], [F(0), F(4)]], [F(1), F(0)],
            F(1, 2), F(3, 4), 4,
            lambda n: F(1, 2) ** n * quarter_turn_cos(n),
            "a_n=2^(-n) cos(n*pi/2); every odd scalar term is zero.",
        ),
        Example(
            "rational_complex", "Roots 3/10 +/- 2i/5", a1,
            [[F(4), F(-24, 5)], [F(-24, 5), F(16)]], [F(1, 2), F(0)],
            F(1, 2), F(3, 4), 20, rational_complex_term,
            "a_n=Re((1/2+3i/8)(3/10+2i/5)^n); phase cancellation is present.",
        ),
        Example(
            "repeated_complex", "Repeated complex roots", a2,
            normalized_p, normalized_w, alpha, beta,
            ceiling(sum(normalized_p[i][i] for i in range(4))),
            lambda n, d=divisor: F(n + 1, d) * F(1, 2) ** n * quarter_turn_cos(n),
            "Normalized (n+1)2^(-n) cos(n*pi/2); characteristic polynomial "
            "(z^2+1/4)^2 and exact Lyapunov equation P-A^T P A=I before scaling.",
        ),
    ]


def denominator_error(n: int) -> F:
    return F(1, 4) * F(-1, 2) ** n


def quotient(term: F, n: int) -> F:
    return term / (2 * (1 + denominator_error(n)))


def choose_coordinate(v: Vector) -> int:
    """Least index attaining the largest absolute coordinate, including ties."""
    return max(range(len(v)), key=lambda i: (abs(v[i]), -i))


def states_until(example: Example, last: int) -> list[Vector]:
    states = [example.w[:]]
    for _ in range(last):
        states.append(matvec(example.a, states[-1]))
    return states


def sample(example: Example, count: int = 8) -> tuple[list[dict], list[Vector]]:
    states = [example.w[:]]
    selected = []
    n = 1
    for j in range(1, count + 1):
        target = example.q ** (2 * j)
        while True:
            while len(states) <= n:
                states.append(matvec(example.a, states[-1]))
            if quadratic(states[n], example.p) <= target:
                break
            n += 1
        k = choose_coordinate(states[n])
        index = n + k
        while len(states) <= index + example.dimension:
            states.append(matvec(example.a, states[-1]))
        term = states[index][0]
        selected.append({
            "j": j, "crossing": n, "coordinate": k, "index": index,
            "term": term, "quotient": quotient(term, index),
            "energy": quadratic(states[n], example.p),
            "previous_energy": quadratic(states[n - 1], example.p),
            "threshold": target,
        })
    return selected, states


def sign(x: F) -> int:
    return (x > 0) - (x < 0)


def serialize(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, list):
        return [serialize(x) for x in value]
    if isinstance(value, dict):
        return {k: serialize(v) for k, v in value.items()}
    return value


def run_checks() -> dict:
    counts: dict[str, int] = {}

    def check(condition: bool, category: str) -> None:
        counts[category] = counts.get(category, 0) + 1
        if not condition:
            raise AssertionError(category)

    check(choose_coordinate([F(1), F(-1), F(0)]) == 0, "coordinate_ties")
    check(choose_coordinate([F(0), F(-2), F(2)]) == 1, "coordinate_ties")
    check(choose_coordinate([F(0), F(0)]) == 0, "coordinate_ties")
    records = []
    selected_signs = set()
    exact_crossing_equalities = 0

    for example in examples():
        d = example.dimension
        p_next = matmul(matmul(transpose(example.a), example.p), example.a)
        check(is_psd(add(example.p, identity(d), F(-1))), "metric_lower_bound")
        check(is_psd(add(scale(identity(d), F(example.metric_bound)), example.p, F(-1))),
              "metric_upper_bound")
        check(is_psd(add(p_next, example.p, -(example.alpha ** 2))),
              "norm_contraction_lower")
        check(is_psd(add(scale(example.p, example.beta ** 2), p_next, F(-1))),
              "norm_contraction_upper")
        check(quadratic(example.w, example.p) == 1, "exact_initial_normalization")
        check(determinant(example.a) != 0, "invertible_state_transition")
        if example.slug != "repeated_complex":
            check(p_next == scale(example.p, F(1, 4)), "exact_quarter_energy_identity")
        else:
            raw_p = solve_lyapunov(example.a)
            check(add(raw_p, matmul(matmul(transpose(example.a), raw_p), example.a), F(-1))
                  == identity(d), "exact_lyapunov_equation")

        denominator_matrix = [[F(-1, 2)]]
        denominator_metric = [[F(1)]]
        denominator_state = [F(1, 4)]
        denominator_next_metric = matmul(
            matmul(transpose(denominator_matrix), denominator_metric), denominator_matrix
        )
        check(is_psd(add(denominator_metric, identity(1), F(-1))),
              "denominator_metric_lower_bound")
        check(is_psd(add(scale(identity(1), F(example.metric_bound)), denominator_metric, F(-1))),
              "denominator_metric_upper_bound")
        check(is_psd(add(denominator_next_metric, denominator_metric, -(example.alpha ** 2))),
              "denominator_shared_contraction_lower")
        check(is_psd(add(scale(denominator_metric, example.beta ** 2), denominator_next_metric, F(-1))),
              "denominator_shared_contraction_upper")
        check(quadratic(denominator_state, denominator_metric) <= F(1, 4),
              "denominator_initial_state_bound")

        check(example.q < min(example.c / 2, example.alpha ** d, F(1, 8)),
              "strict_annular_ratio")
        t_bound = example.crossing_bound
        check(example.beta ** t_bound <= example.q, "crossing_index_constant")
        selected, states = sample(example)
        for n, state in enumerate(states):
            check(state[0] == example.expected(n), "independent_scalar_formula")
            for k in range(d):
                check(state[k] == example.expected(n + k), "state_coordinate_is_original_term")
            error = denominator_error(n)
            check(denominator_state[0] == error, "denominator_independent_state_realization")
            check(abs(error) <= F(1, 2), "denominator_uniform_lower_bound")
            check(F(1, 2) <= 1 + error <= F(3, 2), "denominator_uniform_lower_bound")
            denominator_state = matvec(denominator_matrix, denominator_state)
            if n + 1 < len(states):
                energy = quadratic(state, example.p)
                energy_next = quadratic(states[n + 1], example.p)
                check(example.alpha ** 2 * energy <= energy_next <= example.beta ** 2 * energy,
                      "state_energy_contraction")

        for item in selected:
            j, n, k, index = (item[x] for x in ("j", "crossing", "coordinate", "index"))
            a = item["quotient"]
            check(item["previous_energy"] > item["threshold"] >= item["energy"],
                  "first_crossing_including_equality")
            check(example.alpha ** 2 * item["threshold"] < item["energy"],
                  "crossing_energy_lower_bound")
            check(n <= t_bound * j, "original_prefix_cutoff")
            check(index <= t_bound * j + d - 1, "original_prefix_cutoff")
            check(states[n][k] == item["term"] == example.expected(index),
                  "selected_coordinate_is_original_term")
            check(example.c * example.q ** j < abs(a) <= example.q ** j,
                  "signed_quotient_envelope")
            check(item["term"] != 0, "selected_term_is_nonzero")
            check(k == choose_coordinate(states[n]), "coordinate_ties")
            selected_signs.add(sign(a))
            exact_crossing_equalities += item["energy"] == item["threshold"]

            for t in (F(1), F(3, 2), F(2)):
                for x in (F(-7, 5), F(0), F(11, 7)):
                    point = x + t * a
                    for gamma in (point - F(1, 17), point, point + F(1, 17)):
                        cleared = t * item["term"] - 2 * (gamma - x) * (
                            1 + denominator_error(index)
                        )
                        check(sign(point - gamma) == sign(cleared),
                              "quotient_boundary_sign_clearing_including_zero")

        for left, right in itertools.combinations(selected, 2):
            j = left["j"]
            check(left["index"] != right["index"], "selected_indices_are_distinct")
            check(abs(left["quotient"] - right["quotient"])
                  > (example.c - example.q) * example.q ** j,
                  "signed_pairwise_separation")

        for left, right in zip(selected, selected[1:]):
            check(right["crossing"] >= left["crossing"] + d,
                  "successive_crossings_leave_a_full_scalar_block")
            check(left["index"] < right["index"], "selected_indices_strictly_increase")

        records.append({
            "example": example.slug,
            "description": example.description,
            "matrix": example.a, "metric": example.p, "initial_state": example.w,
            "alpha": example.alpha, "beta": example.beta,
            "metric_bound_K": example.metric_bound, "annular_c": example.c,
            "annular_Q": example.q, "crossing_index_T": t_bound,
            "original_prefix_bound_for_B_8": t_bound * 8 + d - 1,
            "computed_state_prefix_length": len(states),
            "denominator_realization": {
                "matrix": denominator_matrix, "metric": denominator_metric,
                "initial_state": [F(1, 4)],
                "formula": "e_n=(1/4)(-1/2)^n",
                "bounds": "Uses the same alpha, beta, and K as the numerator family.",
            },
            "selected_witnesses": selected,
        })

    check(selected_signs == {-1, 1}, "both_displacement_signs_occur")
    check(exact_crossing_equalities > 0, "threshold_equalities_are_tested")
    return serialize({
        "schema_version": 1,
        "arithmetic": "Python fractions.Fraction; all comparisons exact",
        "purpose": "Check normalization, oscillatory cancellations, repeated roots, original-term "
                   "selection, boundary equality, annular separation, and rational sign clearing.",
        "limitation": "These finite checks support the implementation and exposition. "
                      "They do not prove the continuum theorem or instantiate its random routing tree.",
        "status": "PASS",
        "total_assertions": sum(counts.values()),
        "assertions_by_category": counts,
        "exact_threshold_equality_witnesses": exact_crossing_equalities,
        "examples": records,
    })


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("results.json"))
    args = parser.parse_args()
    result = run_checks()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": result["status"],
        "assertions": result["total_assertions"],
        "examples": len(result["examples"]),
        "exact_threshold_equalities": result["exact_threshold_equality_witnesses"],
        "results": str(args.output),
    }, indent=2))


if __name__ == "__main__":
    main()
