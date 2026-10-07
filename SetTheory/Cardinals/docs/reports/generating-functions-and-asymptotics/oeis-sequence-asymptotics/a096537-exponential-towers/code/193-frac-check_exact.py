#!/usr/bin/env python3
"""Deterministic, standard-library-only finite exact checks.

Every mathematical operation here uses integers or fractions.Fraction.  These
checks certify the stated finite identities and rounded rational inequalities;
they do not certify an asymptotic theorem, Airy evaluation, or quadrature.

Run with no arguments to print the canonical JSON receipt.  --output PATH also
creates a new receipt file, subject to certificate_io's output-path policy.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from heapq import heapify, heappop, heappush
from itertools import product
from math import comb, factorial
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).absolute().parent
sys.path.insert(0, str(ROOT))
import certificate_io
_MAX_ROW = 30
_MAX_PRUFER = 6
_MAX_HEIGHT = 10
_SHIFTS = (
    Fraction(1, 10), Fraction(1, 2), Fraction(1),
    Fraction(3, 2), Fraction(2), Fraction(37, 10),
)


def _require(condition: bool, message: str) -> None:
    if type(condition) is not bool:
        raise TypeError("A check condition must be a bool")
    if not condition:
        raise ValueError(message)


def _integer(value: int, name: str, minimum: int = 0) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an integer (not bool)")
    if value < minimum:
        raise ValueError(f"{name} must be at least {minimum}")
    return value


def _exact(value: int | Fraction, name: str) -> Fraction:
    if type(value) not in (int, Fraction):
        raise TypeError(f"{name} must be an integer or Fraction")
    return Fraction(value)


def _polynomial(values: list[int], name: str) -> None:
    if type(values) is not list or not values:
        raise TypeError(f"{name} must be a nonempty list of integers")
    if any(type(value) is not int for value in values):
        raise TypeError(f"{name} must contain integers (not bool)")


def _multiply(left: list[int], right: list[int]) -> list[int]:
    _polynomial(left, "left polynomial")
    _polynomial(right, "right polynomial")
    result = [0] * (len(left) + len(right) - 1)
    for i, first in enumerate(left):
        for j, second in enumerate(right):
            result[i + j] += first * second
    return result


def _shift_one(polynomial: list[int]) -> list[int]:
    _polynomial(polynomial, "polynomial")
    return [
        sum(polynomial[j] * comb(j, k) for j in range(k, len(polynomial)))
        for k in range(len(polynomial))
    ]


def _row_polynomials(maximum: int) -> list[list[int]]:
    """P_0=1; P_n=y sum_k k C(n-1,k-1) P_(k-1)(y+1) P_(n-k)."""
    _integer(maximum, "maximum row")
    rows = [[1]]
    shifted = [[1]]
    for n in range(1, maximum + 1):
        current = [0] * (n + 1)
        for k in range(1, n + 1):
            term = _multiply(shifted[k - 1], rows[n - k])
            factor = k * comb(n - 1, k - 1)
            for j, coefficient in enumerate(term):
                current[j + 1] += factor * coefficient
        rows.append(current)
        shifted.append(_shift_one(current))
    return rows


def _check_recurrence(rows: list[list[int]]) -> int:
    """Recompute coefficient sums directly, without polynomial helper calls."""
    if type(rows) is not list or not rows:
        raise TypeError("rows must be a nonempty list")
    for n, row in enumerate(rows):
        _polynomial(row, f"row {n}")
        _require(len(row) == n + 1, f"Incorrect row length at n={n}")
    _require(rows[0] == [1], "Incorrect initial row")
    checked = 1
    for n in range(1, len(rows)):
        _require(rows[n][0] == 0, f"Incorrect constant coefficient at n={n}")
        checked += 1
        for degree in range(1, n + 1):
            expected = 0
            for k in range(1, n + 1):
                coefficient = 0
                for shifted_degree in range(min(k - 1, degree - 1) + 1):
                    other_degree = degree - 1 - shifted_degree
                    if other_degree >= len(rows[n - k]):
                        continue
                    shifted_coefficient = sum(
                        rows[k - 1][j] * comb(j, shifted_degree)
                        for j in range(shifted_degree, k)
                    )
                    coefficient += shifted_coefficient * rows[n - k][other_degree]
                expected += k * comb(n - 1, k - 1) * coefficient
            _require(rows[n][degree] == expected,
                     f"Polynomial recurrence failure at n={n}, degree={degree}")
            checked += 1
    return checked


def _decode_depths(sequence: tuple[int, ...], n: int) -> list[int]:
    _integer(n, "number of nonroot vertices", 1)
    if type(sequence) is not tuple or len(sequence) != n - 1:
        raise ValueError("A Pruefer sequence must be a tuple of length n-1")
    if any(type(vertex) is not int or not 0 <= vertex <= n for vertex in sequence):
        raise ValueError("Pruefer vertices must be integers in 0..n")
    degrees = [1] * (n + 1)
    for vertex in sequence:
        degrees[vertex] += 1
    leaves = [vertex for vertex, degree in enumerate(degrees) if degree == 1]
    heapify(leaves)
    adjacency: list[list[int]] = [[] for _ in degrees]
    for vertex in sequence:
        _require(bool(leaves), "Pruefer decoder has no leaf")
        leaf = heappop(leaves)
        adjacency[leaf].append(vertex)
        adjacency[vertex].append(leaf)
        degrees[leaf] -= 1
        degrees[vertex] -= 1
        if degrees[vertex] == 1:
            heappush(leaves, vertex)
    _require(len(leaves) == 2, "Pruefer decoder must end with two leaves")
    first, second = leaves
    adjacency[first].append(second)
    adjacency[second].append(first)
    _require(sum(map(len, adjacency)) == 2 * n, "Pruefer edge count mismatch")
    depths = [-1] * (n + 1)
    depths[0] = 0
    queue = [0]
    for vertex in queue:
        for neighbour in adjacency[vertex]:
            if depths[neighbour] < 0:
                depths[neighbour] = depths[vertex] + 1
                queue.append(neighbour)
    _require(min(depths) >= 0, "Pruefer graph disconnected")
    return depths


def _prufer_polynomial(n: int) -> tuple[list[int], int]:
    """Enumerate all labelled trees; multiply linear factors independently."""
    _integer(n, "number of nonroot vertices", 1)
    coefficients = [0] * (n + 1)
    count = 0
    for sequence in product(range(n + 1), repeat=n - 1):
        depths = _decode_depths(sequence, n)
        weight = [1]
        for depth in depths[1:]:
            following = [0] * (len(weight) + 1)
            for j, coefficient in enumerate(weight):
                following[j] += (depth - 1) * coefficient
                following[j + 1] += coefficient
            weight = following
        for j, coefficient in enumerate(weight):
            coefficients[j] += coefficient
        count += 1
    _require(count == (n + 1) ** (n - 1), f"Cayley enumeration count failure n={n}")
    return coefficients, count


def _evaluate(polynomial: list[int], shift: int | Fraction) -> Fraction:
    _polynomial(polynomial, "polynomial")
    y = _exact(shift, "shift")
    value = Fraction(0)
    for coefficient in reversed(polynomial):
        value = value * y + coefficient
    return value


def _rational_tower(height: int, maximum: int, shift: int | Fraction) -> list[Fraction]:
    """Return EGF-scaled coefficients n! [x^n] of a finite tower."""
    _integer(height, "height")
    _integer(maximum, "maximum degree")
    y = _exact(shift, "shift")
    _require(y > 0, "shift must be positive")
    child = [Fraction(1)] + [Fraction(0)] * maximum
    for level in range(height - 1, -1, -1):
        weight = y + level
        parent = [Fraction(1)]
        for n in range(1, maximum + 1):
            parent.append(weight * sum(
                (k * comb(n - 1, k - 1) * child[k - 1] * parent[n - k]
                 for k in range(1, n + 1)), Fraction(0)))
        child = parent
    return child


def _formal_tower(height: int, maximum: int, shift: int | Fraction) -> list[Fraction]:
    """Independent ordinary-series powers: exp(g)=sum_(j=0)^N g^j/j!."""
    _integer(height, "height")
    _integer(maximum, "maximum degree")
    y = _exact(shift, "shift")
    _require(y > 0, "shift must be positive")
    coefficients = [Fraction(1)] + [Fraction(0)] * maximum
    for level in range(height - 1, -1, -1):
        exponent = [Fraction(0)] + [(y + level) * c for c in coefficients[:-1]]
        result = [Fraction(1)] + [Fraction(0)] * maximum
        power = [Fraction(1)] + [Fraction(0)] * maximum
        for order in range(1, maximum + 1):
            # exponent[0] is zero; every term has degree at least order.
            next_power = [Fraction(0)] * (maximum + 1)
            for i in range(order - 1, maximum):
                for j in range(1, maximum - i + 1):
                    next_power[i + j] += power[i] * exponent[j]
            power = next_power
            denominator = factorial(order)
            for degree in range(order, maximum + 1):
                result[degree] += power[degree] / denominator
        coefficients = result
    return [factorial(n) * value for n, value in enumerate(coefficients)]


def _rational_coefficients(maximum: int, p: int, q: int) -> list[int]:
    """Integers q^n P_n(p/q), obtained by triangular tower stabilization."""
    _integer(maximum, "maximum degree")
    _integer(p, "shift numerator", 1)
    _integer(q, "shift denominator", 1)
    child = [1]
    for level in range(maximum - 1, -1, -1):
        numerator = p + q * level
        parent = [1]
        for n in range(1, maximum - level + 1):
            parent.append(numerator * sum(
                k * comb(n - 1, k - 1) * child[k - 1] * parent[n - k]
                for k in range(1, n + 1)))
        child = parent
    return child


def _ratio(value: int | Fraction) -> dict[str, int]:
    rational = _exact(value, "rational receipt value")
    return {"numerator": rational.numerator, "denominator": rational.denominator}


def _tail_inequalities() -> list[dict[str, object]]:
    """Check every source inequality, including the rational root bounds."""
    r = Fraction(4, 125)
    lo, hi = Fraction(99, 100), Fraction(101, 100)
    sqrt2lo, sqrt2hi = Fraction(7, 5), Fraction(283, 200)
    bx = hi / 2 + hi ** 3 / (6 * lo ** 2) + r * hi / (2 * sqrt2lo)
    by = hi ** 4 / (3 * lo ** 3) + r * hi / (2 * sqrt2lo)
    bz = hi / 2 + hi ** 3 / (2 * lo ** 2)
    base = (1875 * sqrt2hi * r ** 3 + 44680 * r ** 2
            + 128256 * sqrt2hi * r + 1594368) / (6912 * 48 ** 2)
    full = (Fraction(101, 1000) + Fraction(70, 100) * Fraction(1672, 10000)
            + Fraction(37, 100) * Fraction(6685, 10000)
            + Fraction(104, 100) * Fraction(5925, 10000))
    candidates = (
        ("positive_radius", Fraction(0), r),
        ("positive_lower_endpoint", Fraction(0), lo),
        ("endpoint_order", lo, hi),
        ("positive_sqrt2_lower_bound", Fraction(0), sqrt2lo),
        ("sqrt2_lower_square", sqrt2lo ** 2, Fraction(2)),
        ("sqrt2_upper_square", Fraction(2), sqrt2hi ** 2),
        ("gradient_x", bx, Fraction(70, 100)),
        ("gradient_y", by, Fraction(37, 100)),
        ("gradient_z", bz, Fraction(104, 100)),
        ("baseline", base, Fraction(101, 1000)),
        ("airy_coefficient", Fraction(385, 2304), Fraction(1672, 10000)),
        ("fourfold_airy_coefficient", 4 * Fraction(385, 2304), Fraction(6685, 10000)),
        ("threefold_airy_coefficient", 3 * Fraction(455, 2304), Fraction(5925, 10000)),
        ("rounded_combined_bound", full, Fraction(11, 10)),
        ("positive_cuberoot_lower_bound", Fraction(0), Fraction(79, 100)),
        ("cuberoot_lower_cube", Fraction(79, 100) ** 3, Fraction(1, 2)),
        ("final_tail_margin", Fraction(11, 10) / (10 * Fraction(79, 100))
         + Fraction(1, 10 ** 9) + Fraction(1, 10 ** 20), Fraction(141, 1000)),
    )
    inequalities = []
    for name, left, right in candidates:
        _require(left < right, f"Exact rational tail inequality failed: {name}")
        inequalities.append({
            "name": name, "left": _ratio(left), "relation": "<",
            "right": _ratio(right), "positive_margin": _ratio(right - left),
        })
    return inequalities


def run_checks() -> dict[str, object]:
    """Run the complete fixed finite exact-check suite and return its receipt."""
    rows = _row_polynomials(_MAX_ROW)
    recurrence_count = _check_recurrence(rows)
    enumeration = []
    for n in range(1, _MAX_PRUFER + 1):
        independent, count = _prufer_polynomial(n)
        _require(rows[n] == independent, f"Pruefer polynomial mismatch n={n}")
        enumeration.append({"n": n, "labelled_tree_count": count})
    for n in range(1, _MAX_ROW + 1):
        row = rows[n]
        _require(all(type(c) is int and c >= 0 for c in row),
                 f"Nonnegative integer row check failed n={n}")
        _require(row[-1] == (n + 1) ** (n - 1),
                 f"Cayley leading coefficient mismatch n={n}")
        one_child = [0] + [n * c for c in _shift_one(rows[n - 1])]
        _require(len(row) == len(one_child), f"One-child row length mismatch n={n}")
        _require(all(row[j] >= one_child[j] for j in range(len(row))),
                 f"One-child coefficient lower bound failed n={n}")
    height_checks = []
    for y in _SHIFTS:
        prior = _rational_tower(0, _MAX_HEIGHT, y)
        _require(prior == _formal_tower(0, _MAX_HEIGHT, y),
                 "Height-zero formal tower mismatch")
        diagonals = []
        for height in range(1, _MAX_HEIGHT + 1):
            values = _rational_tower(height, _MAX_HEIGHT, y)
            _require(values == _formal_tower(height, _MAX_HEIGHT, y),
                     f"Independent formal exponential mismatch y={y}, h={height}")
            differences = [values[n] - prior[n] for n in range(_MAX_HEIGHT + 1)]
            _require(all(value >= 0 for value in differences),
                     f"Negative exact height coefficient y={y}, h={height}")
            _require(all(differences[n] == 0 for n in range(height)),
                     f"Minimum degree failure y={y}, h={height}")
            path = Fraction(factorial(height))
            for level in range(height):
                path *= y + level
            _require(differences[height] == path and path > 0,
                     f"Path diagonal mismatch y={y}, h={height}")
            diagonals.append(_ratio(path))
            prior = values
        _require(all(prior[n] == _evaluate(rows[n], y) for n in range(_MAX_HEIGHT + 1)),
                 f"Stabilized tower/polynomial mismatch y={y}")
        scaled = _rational_coefficients(_MAX_ROW, y.numerator, y.denominator)
        _require(all(Fraction(scaled[n], y.denominator ** n) == _evaluate(rows[n], y)
                     for n in range(_MAX_ROW + 1)),
                 f"Scaled integer recurrence mismatch y={y}")
        height_checks.append({"shift": _ratio(y), "path_diagonal_egf_coefficients": diagonals})
    return {
        "schema_version": 1,
        "status": "PASS",
        "scope": "Finite exact identities and rational inequalities only; not an asymptotic or quadrature certificate",
        "arithmetic": "Python standard-library integer and Fraction arithmetic only",
        "polynomial_recurrence": {
            "maximum_n": _MAX_ROW,
            "coefficient_equalities_checked": recurrence_count,
            "identity": "P_0(y)=1; P_n(y)=y*sum(k*binom(n-1,k-1)*P_(k-1)(y+1)*P_(n-k)(y), k=1..n)",
        },
        "independent_exhaustive_prufer": enumeration,
        "row_checks": {
            "minimum_n": 1, "maximum_n": _MAX_ROW,
            "properties": ["nonnegative integer coefficients", "degree n",
                           "zero constant coefficient", "Cayley leading coefficient (n+1)^(n-1)",
                           "coefficientwise P_n(y) >= n*y*P_(n-1)(y+1)"],
        },
        "rational_shift_checks": {
            "maximum_height": _MAX_HEIGHT,
            "maximum_tower_coefficient_degree": _MAX_HEIGHT,
            "maximum_scaled_integer_recurrence_degree": _MAX_ROW,
            "properties": ["finite tower matches independent truncated formal exponential",
                           "exact-height nonnegative coefficients", "exact-height minimum degree h",
                           "EGF path diagonal h! times rising factorial (y)_h",
                           "height-10 tower stabilizes to P_n(y) through degree 10",
                           "q^n P_n(p/q) matches scaled integer tower recurrence through degree 30"],
            "shifts": height_checks,
        },
        "initial_polynomial_rows_low_degree_first": rows[:8],
        "tail_rational_inequalities": _tail_inequalities(),
    }


def main(argv: list[str] | None = None) -> int:
    """Validate the CLI destination before any expensive exact checks."""
    if argv is not None:
        if type(argv) is not list or any(type(argument) is not str for argument in argv):
            raise TypeError("argv must be None or a list of strings")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", help="create a new canonical JSON receipt file")
    arguments = parser.parse_args(argv)
    output = None
    if arguments.output is not None:
        output = certificate_io.checked_output(arguments.output, source=ROOT)
    result = run_checks()
    payload = certificate_io.canonical(result)
    if output is not None:
        certificate_io.write_new(output, payload)
    sys.stdout.buffer.write(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
