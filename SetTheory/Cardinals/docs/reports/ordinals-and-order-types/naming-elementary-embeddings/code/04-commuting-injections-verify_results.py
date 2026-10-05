#!/usr/bin/env python3
"""Exact finite checks accompanying the commuting-injections article.

This program requires Python 3.10 or newer and uses only its standard library.
It performs four separate
checks, using exact integers and fractions throughout:

* compute the positive rank of eight finite commutative presentations by
  enumerating positive circuits of their integer relation matrices;
* enumerate weak compositions modulo cyclic rotation and compare their counts
  with the necklace formula;
* enumerate subgroups of C_k x C_D having order D;
* enumerate pairs of finite permutations satisfying commutativity and f^m=g^n,
  and compare their counts with the proposed generating function.

Run ``python verify_results.py`` to write verification.json next to this file.
Use ``--output PATH`` to write a separate result file for comparison.  The JSON
is deterministic: it contains no clock times or platform-dependent metadata.

These finite checks are evidence for the stated examples and counting formulas;
they do not replace the article's proofs for arbitrary inputs or ordinals.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from functools import reduce
from itertools import combinations, permutations, product
import json
from math import comb, factorial, gcd, lcm
from pathlib import Path


def require(condition: bool, message: str) -> None:
    """Keep mathematical assertions active even if Python is run with -O."""
    if not condition:
        raise AssertionError(message)


def rref(rows: list[list[int | Fraction]], ncols: int):
    """Return rational reduced row echelon form and its pivot columns.

    The explicit column count allows matrices with no rows.  Columns are never
    inferred from a first row, which matters for a free monoid presentation.
    """
    require(ncols >= 0, "A matrix must have a nonnegative column count.")
    require(all(len(row) == ncols for row in rows), "Ragged matrix.")
    matrix = [[Fraction(value) for value in row] for row in rows]
    pivots: list[int] = []
    pivot_row = 0
    for col in range(ncols):
        candidate = next(
            (i for i in range(pivot_row, len(matrix)) if matrix[i][col]),
            None,
        )
        if candidate is None:
            continue
        matrix[pivot_row], matrix[candidate] = matrix[candidate], matrix[pivot_row]
        divisor = matrix[pivot_row][col]
        matrix[pivot_row] = [value / divisor for value in matrix[pivot_row]]
        for i in range(len(matrix)):
            if i == pivot_row or not matrix[i][col]:
                continue
            multiplier = matrix[i][col]
            matrix[i] = [
                value - multiplier * pivot
                for value, pivot in zip(matrix[i], matrix[pivot_row])
            ]
        pivots.append(col)
        pivot_row += 1
        if pivot_row == len(matrix):
            break
    return matrix, pivots


def matrix_rank(rows: list[list[int | Fraction]], ncols: int) -> int:
    return len(rref(rows, ncols)[1])


def nullspace(rows: list[list[int | Fraction]], ncols: int):
    """Give a rational basis of the kernel, using one vector per free column."""
    reduced, pivots = rref(rows, ncols)
    free_columns = [j for j in range(ncols) if j not in pivots]
    basis = []
    for free in free_columns:
        vector = [Fraction(0) for _ in range(ncols)]
        vector[free] = Fraction(1)
        for i, pivot in enumerate(pivots):
            vector[pivot] = -reduced[i][free]
        require(
            all(sum(Fraction(a) * b for a, b in zip(row, vector)) == 0
                for row in rows),
            "Computed kernel vector fails the original equations.",
        )
        basis.append(vector)
    require(
        len(basis) + len(pivots) == ncols,
        "Rank-nullity failed in rational elimination.",
    )
    return basis


def restrict_columns(rows: list[list[int]], support: tuple[int, ...]):
    return [[row[j] for j in support] for row in rows]


def primitive_integer_vector(vector: list[Fraction]) -> list[int]:
    """Scale a nonzero rational vector to primitive integral coordinates."""
    denominator = reduce(lcm, (entry.denominator for entry in vector), 1)
    integral = [int(entry * denominator) for entry in vector]
    common = reduce(gcd, (abs(entry) for entry in integral), 0)
    require(common > 0, "Cannot normalize the zero vector.")
    return [entry // common for entry in integral]


def positive_circuits(rows: list[list[int]], ncols: int):
    """Enumerate the primitive generators of all extreme rays of W.

    Here W={w>=0: A w=0}.  Its positive circuits are precisely supports S for
    which ker(A_S) is one-dimensional and its spanning vector has one strict
    sign.  A circuit has at most rank(A)+1 coordinates.  Singleton supports of
    zero columns are included.  Exhaustive enumeration is finite but can be
    exponential; this is an exact verification routine, not an LP optimizer.
    """
    rank = matrix_rank(rows, ncols)
    circuits = []
    for size in range(1, min(ncols, rank + 1) + 1):
        for support in combinations(range(ncols), size):
            basis = nullspace(restrict_columns(rows, support), size)
            if len(basis) != 1:
                continue
            local = basis[0]
            if all(entry < 0 for entry in local):
                local = [-entry for entry in local]
            if not all(entry > 0 for entry in local):
                continue
            primitive = primitive_integer_vector(local)
            vector = [0] * ncols
            for j, value in zip(support, primitive):
                vector[j] = value
            require(
                all(sum(a * b for a, b in zip(row, vector)) == 0 for row in rows),
                "A positive circuit fails A w=0.",
            )
            require(all(value > 0 for value in primitive), "Nonpositive circuit.")
            circuits.append({
                "support_indices": [j + 1 for j in support],
                "primitive_vector": vector,
            })
    return circuits


def unit_certificate(rows: list[list[int]], ncols: int, index: int):
    """Find integral z,v>=0 in A^T z=e_index+v for a known unit index.

    Only v is required to be nonnegative; z may have either sign.  Rational
    Farkas duality and denominator clearing prove existence when the index is
    absent from all positive circuits.  Enumerating integral coefficient shells
    therefore terminates for these calls.  It is intentionally elementary and
    can be slow on large presentations; the supplied examples use tiny shells.
    """
    require(rows, "A free presentation has no unit generator to certify.")
    radius = 1
    while True:
        for coefficients in product(range(-radius, radius + 1), repeat=len(rows)):
            if max(abs(value) for value in coefficients) != radius:
                continue
            image = [
                sum(coefficient * row[j]
                    for coefficient, row in zip(coefficients, rows))
                for j in range(ncols)
            ]
            if image[index] < 1 or any(value < 0 for value in image):
                continue
            inverse = image.copy()
            inverse[index] -= 1
            require(all(value >= 0 for value in inverse), "Invalid unit inverse.")
            require(
                all(image[j] == inverse[j] + int(j == index) for j in range(ncols)),
                "The integral unit-certificate identity failed.",
            )
            return {
                "generator_index": index + 1,
                "row_coefficients": list(coefficients),
                "inverse_exponents": inverse,
            }
        radius += 1


def analyze_presentation(name, generators, relations, rows):
    """Compute rank(G), J, d, and positive/negative membership certificates."""
    ncols = len(generators)
    rank = matrix_rank(rows, ncols)
    circuits = positive_circuits(rows, ncols)
    witness = [
        sum(circuit["primitive_vector"][j] for circuit in circuits)
        for j in range(ncols)
    ]
    positive = tuple(j for j, value in enumerate(witness) if value > 0)
    units = tuple(j for j in range(ncols) if j not in positive)
    restricted_rank = matrix_rank(restrict_columns(rows, positive), len(positive))
    positive_rank = len(positive) - restricted_rank
    require(
        all(sum(a * b for a, b in zip(row, witness)) == 0 for row in rows),
        f"{name}: the summed positive witness fails the relations.",
    )
    require(
        matrix_rank([c["primitive_vector"] for c in circuits], ncols)
        == positive_rank,
        f"{name}: circuit-span dimension disagrees with |J|-rank(A_J).",
    )
    require(
        all((witness[j] > 0) == (j in positive) for j in range(ncols)),
        f"{name}: the witness support differs from J.",
    )
    certificates = [unit_certificate(rows, ncols, j) for j in units]
    return {
        "name": name,
        "generators": generators,
        "relations": relations,
        "relation_matrix": rows,
        "matrix_rank": rank,
        "group_rank": ncols - rank,
        "positive_generator_indices": [j + 1 for j in positive],
        "positive_generators": [generators[j] for j in positive],
        "unit_generator_indices": [j + 1 for j in units],
        "unit_generators": [generators[j] for j in units],
        "restricted_matrix_rank": restricted_rank,
        "positive_rank": positive_rank,
        "positive_circuits": circuits,
        "positive_witness": witness,
        "unit_certificates": certificates,
    }


def check_rank_examples():
    """The expected data are specified separately from the circuit algorithm."""
    examples = [
        ("free_two_generators", ["f", "g"], [], [],
         ["f", "g"], 2, 2, [1, 1]),
        ("f_squared_equals_g_cubed", ["f", "g"], ["f^2=g^3"], [[2, -3]],
         ["f", "g"], 1, 1, [3, 2]),
        ("fg_equals_identity", ["f", "g"], ["fg=1"], [[1, 1]],
         [], 1, 0, [0, 0]),
        ("idempotent_generator", ["f"], ["f^2=f"], [[1]],
         [], 0, 0, [0]),
        ("fg_equals_h", ["f", "g", "h"], ["fg=h"], [[1, 1, -1]],
         ["f", "g", "h"], 2, 2, [1, 1, 2]),
        ("cancellation_relation", ["f", "g"], ["f^2 g=g^2 f"], [[1, -1]],
         ["f", "g"], 1, 1, [1, 1]),
        ("two_power_relations", ["f", "g", "h"],
         ["f^2=g^3", "h^5=f^7"], [[2, -3, 0], [-7, 0, 5]],
         ["f", "g", "h"], 1, 1, [15, 10, 21]),
        ("torsion_survives_quotient", ["f", "g"], ["f^2=g^2"], [[2, -2]],
         ["f", "g"], 1, 1, [1, 1]),
    ]
    results = []
    for (name, generators, relations, rows, expected_j, expected_group_rank,
         expected_positive_rank, expected_witness) in examples:
        result = analyze_presentation(name, generators, relations, rows)
        require(result["positive_generators"] == expected_j, f"{name}: wrong J.")
        require(result["group_rank"] == expected_group_rank, f"{name}: wrong rank(G).")
        require(result["positive_rank"] == expected_positive_rank, f"{name}: wrong d.")
        require(result["positive_witness"] == expected_witness,
                f"{name}: unexpected primitive-circuit witness.")
        results.append(result)
    return {
        "case_count": len(results),
        "positive_circuit_count": sum(len(r["positive_circuits"]) for r in results),
        "unit_certificate_count": sum(len(r["unit_certificates"]) for r in results),
        "all_passed": True,
        "cases": results,
    }


def divisors(number: int) -> list[int]:
    require(number >= 1, "Divisors are requested only for positive integers.")
    return [d for d in range(1, number + 1) if number % d == 0]


def euler_phi(number: int) -> int:
    result = number
    residual = number
    prime = 2
    while prime * prime <= residual:
        if residual % prime == 0:
            result -= result // prime
            while residual % prime == 0:
                residual //= prime
        prime += 1
    if residual > 1:
        result -= result // residual
    return result


def weak_compositions(total: int, slots: int):
    """Enumerate ordered nonnegative integer tuples with the specified sum."""
    if slots == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for suffix in weak_compositions(total - first, slots - 1):
            yield (first,) + suffix


def necklace_formula(total: int, slots: int) -> int:
    """Burnside count for weak compositions of total into slots modulo rotation."""
    numerator = sum(
        euler_phi(d) * comb(total // d + slots // d - 1, slots // d - 1)
        for d in divisors(gcd(total, slots))
    )
    require(numerator % slots == 0, "The necklace numerator is not divisible by n.")
    return numerator // slots


def check_necklaces():
    cases = []
    for total in range(1, 7):
        for slots in range(1, 7):
            words = list(weak_compositions(total, slots))
            require(len(words) == comb(total + slots - 1, slots - 1),
                    "Weak-composition enumeration has an incorrect size.")
            representatives = {
                min(word[shift:] + word[:shift] for shift in range(slots))
                for word in words
            }
            expected = necklace_formula(total, slots)
            require(len(representatives) == expected,
                    f"Necklace formula failed for m={total}, n={slots}.")
            cases.append({
                "m": total,
                "n": slots,
                "compositions_examined": len(words),
                "rotation_orbits": len(representatives),
                "formula": expected,
            })
    return {
        "case_count": len(cases),
        "compositions_examined": sum(case["compositions_examined"] for case in cases),
        "rotation_orbits": sum(case["rotation_orbits"] for case in cases),
        "all_passed": True,
        "cases": cases,
    }


def check_finite_subgroups():
    """Brute-force order-D subsets containing zero in C_k x C_D.

    A nonempty finite subset closed under addition is a subgroup.  The test
    therefore does not rely on the subgroup classification or the divisor-sum
    formula it is checking.
    """
    cases = []
    for order in range(1, 5):
        for cyclic_size in range(1, 7):
            identity = (0, 0)
            elements = list(product(range(cyclic_size), range(order)))
            nonidentity = [element for element in elements if element != identity]
            candidate_count = 0
            subgroup_count = 0
            for remainder in combinations(nonidentity, order - 1):
                candidate_count += 1
                subset = frozenset((identity,) + remainder)
                if all(
                    ((a[0] + b[0]) % cyclic_size, (a[1] + b[1]) % order) in subset
                    for a in subset for b in subset
                ):
                    subgroup_count += 1
            require(candidate_count == comb(cyclic_size * order - 1, order - 1),
                    "Subgroup candidate enumeration has an incorrect size.")
            expected = sum(divisors(gcd(order, cyclic_size)))
            require(subgroup_count == expected,
                    f"Subgroup formula failed for D={order}, k={cyclic_size}.")
            cases.append({
                "D": order,
                "k": cyclic_size,
                "ambient_group_order": cyclic_size * order,
                "candidate_subsets": candidate_count,
                "subgroups_of_order_D": subgroup_count,
                "sigma_1_of_gcd": expected,
            })
    return {
        "case_count": len(cases),
        "candidate_subsets_examined": sum(case["candidate_subsets"] for case in cases),
        "subgroups_found": sum(case["subgroups_of_order_D"] for case in cases),
        "all_passed": True,
        "cases": cases,
    }


def compose_permutations(left: tuple[int, ...], right: tuple[int, ...]):
    """Composition convention: (left right)(i) = left(right(i))."""
    return tuple(left[right[i]] for i in range(len(left)))


def permutation_power(permutation: tuple[int, ...], exponent: int):
    result = tuple(range(len(permutation)))
    for _ in range(exponent):
        result = compose_permutations(permutation, result)
    return result


def divisor_partition_coefficient(order: int, degree: int) -> int:
    """Coefficient of z^degree in product_(c|order) (1-z^c)^(-1).

    Integer coin-change recurrence counts partitions with allowed part sizes
    dividing order, independently of the permutation enumeration.
    """
    coefficients = [1] + [0] * degree
    for part in divisors(order):
        for target in range(part, degree + 1):
            coefficients[target] += coefficients[target - part]
    return coefficients[degree]


def check_permutation_pairs():
    cases = []
    distinct_pairs_examined = 0
    pair_exponent_checks = 0
    for size in range(5):
        elements = list(permutations(range(size)))
        require(len(elements) == factorial(size), "Permutation enumeration failed.")
        pairs = list(product(elements, repeat=2))
        distinct_pairs_examined += len(pairs)
        commutes = {
            (left, right): compose_permutations(left, right)
            == compose_permutations(right, left)
            for left, right in pairs
        }
        powers = {
            (permutation, exponent): permutation_power(permutation, exponent)
            for permutation in elements for exponent in range(1, 5)
        }
        for m in range(1, 5):
            for n in range(1, 5):
                count = 0
                for left, right in pairs:
                    pair_exponent_checks += 1
                    if commutes[(left, right)] and powers[(left, m)] == powers[(right, n)]:
                        count += 1
                order = gcd(m, n)
                coefficient = divisor_partition_coefficient(order, size)
                expected = factorial(size) * coefficient
                require(count == expected,
                        f"Permutation formula failed for N={size}, m={m}, n={n}.")
                cases.append({
                    "N": size,
                    "m": m,
                    "n": n,
                    "D": order,
                    "permutation_pairs": len(pairs),
                    "commuting_pairs_with_power_relation": count,
                    "generating_function_coefficient": coefficient,
                    "factorial_times_coefficient": expected,
                })
    return {
        "case_count": len(cases),
        "distinct_permutation_pairs_examined": distinct_pairs_examined,
        "pair_exponent_checks": pair_exponent_checks,
        "all_passed": True,
        "cases": cases,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output", type=Path,
        default=Path(__file__).resolve().with_name("verification.json"),
        help="JSON destination; default: verification.json next to this script.",
    )
    arguments = parser.parse_args()
    ranks = check_rank_examples()
    necklaces = check_necklaces()
    subgroups = check_finite_subgroups()
    permutation_pairs = check_permutation_pairs()
    report = {
        "schema_version": 1,
        "arithmetic": "exact integers and fractions; Python standard library only",
        "scope": "finite checks of the specified examples and counting formulas",
        "generator_index_convention": "one-based indices in matrix certificates",
        "rank_examples": ranks,
        "necklaces": necklaces,
        "finite_subgroups": subgroups,
        "permutation_pairs": permutation_pairs,
        "summary": {
            "all_passed": True,
            "case_count": sum(section["case_count"] for section in
                              (ranks, necklaces, subgroups, permutation_pairs)),
            "rank_cases": ranks["case_count"],
            "necklace_cases": necklaces["case_count"],
            "subgroup_cases": subgroups["case_count"],
            "permutation_cases": permutation_pairs["case_count"],
        },
    }
    arguments.output.parent.mkdir(parents=True, exist_ok=True)
    arguments.output.write_text(json.dumps(report, indent=2, ensure_ascii=True) + "\n",
                                encoding="utf-8", newline="\n")
    print(f"PASS: {report['summary']['case_count']} exact cases "
          f"({ranks['case_count']} rank, {necklaces['case_count']} necklace, "
          f"{subgroups['case_count']} subgroup, "
          f"{permutation_pairs['case_count']} permutation).")
    print(f"Enumerated {necklaces['compositions_examined']} compositions, "
          f"{subgroups['candidate_subsets_examined']} subgroup candidates, and "
          f"{permutation_pairs['pair_exponent_checks']} pair/exponent checks.")
    print(f"Wrote {arguments.output}")


if __name__ == "__main__":
    main()
