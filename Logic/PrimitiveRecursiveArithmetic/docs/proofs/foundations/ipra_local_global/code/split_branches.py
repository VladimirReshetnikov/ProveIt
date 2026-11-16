#!/usr/bin/env python3
"""Exact reference implementation of the split-branch height certificate.

Coefficient arrays are in ascending degree order.  The checker computes
A_i-A_j itself, rejects zero remainders and failed degree conditions, and
returns explicit bounds for the equation product(y-A_t(x)) = R(x).

The finite checks below are implementation checks.  They are not a proof
of the general height theorem or an embedded iPRA formalization.  See
paper/05_split_branches.tex for the complete mathematical argument.

Run from any directory:
    python3 code/split_branches.py
The report is written to evidence/split_checks.json beside this package.
"""

from dataclasses import dataclass
from math import prod
from pathlib import Path
import json


def normalize(poly):
    """Return canonical coefficients, or None for malformed coefficient data."""
    if not isinstance(poly, (tuple, list)):
        return None
    if any(type(c) is not int for c in poly):
        return None
    result = list(poly)
    while result and result[-1] == 0:
        result.pop()
    return tuple(result)


def evaluate(poly, x):
    """Horner evaluation, using exact integers."""
    value = 0
    for coefficient in reversed(poly):
        value = coefficient + x * value
    return value


def subtract(left, right):
    return normalize(tuple(
        (left[k] if k < len(left) else 0)
        - (right[k] if k < len(right) else 0)
        for k in range(max(len(left), len(right)))
    ))


def magnitude(poly, bound):
    return evaluate(tuple(abs(c) for c in poly), bound)


@dataclass(frozen=True)
class Certificate:
    branches: tuple
    remainder: tuple
    first: int
    second: int

    def check(self):
        """Return normalized certificate and bounds, or an explicit rejection."""
        if not isinstance(self.branches, (tuple, list)) or len(self.branches) < 2:
            return None, "At least two coefficient arrays are required."
        branches = tuple(normalize(p) for p in self.branches)
        remainder = normalize(self.remainder)
        if any(p is None for p in branches) or remainder is None:
            return None, "Every coefficient must be an integer."
        if not remainder:
            return None, "The remainder polynomial must be nonzero."
        if type(self.first) is not int or type(self.second) is not int:
            return None, "Branch indices must be integers."
        if not (0 <= self.first < len(branches) and 0 <= self.second < len(branches)):
            return None, "A branch index lies outside the finite list."
        difference = subtract(branches[self.first], branches[self.second])
        if len(difference) <= len(remainder):
            return None, "The branch difference must have larger degree than R."
        lower_sum = sum(abs(c) for c in difference[:-1])
        remainder_sum = sum(abs(c) for c in remainder)
        height_x = max(1, lower_sum + 2 * remainder_sum)
        height_y = max(magnitude(p, height_x) for p in branches) + magnitude(remainder, height_x)
        return CheckedCertificate(branches, remainder, self.first, self.second,
                                  difference, height_x, height_y), None


@dataclass(frozen=True)
class CheckedCertificate:
    branches: tuple
    remainder: tuple
    first: int
    second: int
    difference: tuple
    height_x: int
    height_y: int

    def equation_value(self, x, y):
        return prod(y - evaluate(p, x) for p in self.branches) - evaluate(self.remainder, x)

    def solutions(self):
        """Enumerate the proved complete box; no unbounded search is performed."""
        h, k = self.height_x, self.height_y
        return [(x, y) for x in range(-h, h + 1)
                for y in range(-k, k + 1)
                if self.equation_value(x, y) == 0]

    def metadata(self):
        return dict(branches=self.branches, remainder=self.remainder,
                    indices=(self.first, self.second), difference=self.difference,
                    height_x=self.height_x, height_y=self.height_y,
                    complete_box_tests=(2*self.height_x+1)*(2*self.height_y+1))


def expand_equation(branches, remainder):
    """Independent coefficient convolution for product(Y-A_t(X))-R(X)."""
    expanded = {(0, 0): 1}
    for branch in branches:
        factor = {(0, 1): 1}
        for exponent, coefficient in enumerate(branch):
            if coefficient:
                factor[(exponent, 0)] = -coefficient
        new = {}
        for (ax, ay), a in expanded.items():
            for (bx, by), b in factor.items():
                key = (ax + bx, ay + by)
                new[key] = new.get(key, 0) + a * b
        expanded = {key: value for key, value in new.items() if value}
    for exponent, coefficient in enumerate(remainder):
        key = (exponent, 0)
        expanded[key] = expanded.get(key, 0) - coefficient
    return {key: value for key, value in expanded.items() if value}


def evaluate_expansion(expanded, x, y):
    return sum(c * x**i * y**j for (i, j), c in expanded.items())


def power_family(branch_count):
    if type(branch_count) is not int or branch_count < 3:
        raise ValueError("The classification uses an integer m >= 3.")
    return Certificate(tuple((0,) * j + (1,) for j in range(1, branch_count+1)),
                       (1,), 0, 2)


def family_classification(branch_count):
    if type(branch_count) is not int or branch_count < 3:
        raise ValueError("The classification uses an integer m >= 3.")
    points = [(0, 1), (1, 2)]
    if branch_count % 2 == 0:
        points += [(0, -1), (1, 0)]
    if branch_count % 4 in (0, 1):
        points += [(-1, 0)]
    return sorted(points)


def checked(cert):
    value, error = cert.check()
    assert error is None, error
    return value


def verify():
    # A nontrivial mixed cubic, with an independently checked expansion.
    cubic = checked(power_family(3))
    expansion = expand_equation(cubic.branches, cubic.remainder)
    expected_expansion = {
        (0, 3): 1,
        (1, 2): -1, (2, 2): -1, (3, 2): -1,
        (3, 1): 1, (4, 1): 1, (5, 1): 1,
        (6, 0): -1, (0, 0): -1,
    }
    assert expansion == expected_expansion
    cubic_solutions = cubic.solutions()
    assert cubic_solutions == [(0, 1), (1, 2)]
    for x in range(-5, 6):
        for y in range(-6, 7):
            assert evaluate_expansion(expansion, x, y) == cubic.equation_value(x, y)

    # Small boxes check every parity/residue class several times.  These
    # boxes alone are NOT a proof of the global family classification.
    family_checks = []
    for m in range(3, 13):
        cert = checked(power_family(m))
        found = [(x, y) for x in range(-4, 5) for y in range(-4, 5)
                 if cert.equation_value(x, y) == 0]
        expected = family_classification(m)
        assert found == expected, (m, found, expected)
        family_checks.append(dict(m=m, small_box=[-4, 4, -4, 4],
                                  tests=81, expected_points=expected,
                                  observed_points=found,
                                  certificate_bounds=[cert.height_x, cert.height_y]))

    # Include a nonconstant remainder with integer zeros.  At x=-1 the
    # first example has two distinct y-values, so discarding R(x)=0 fails.
    examples = [
        ("three_branches_with_R_root", Certificate(
            ((0, 1), (0, 0, 1), (0, 0, 0, 1)), (1, 1), 0, 2),
         [(-1, -1), (-1, 1), (0, 1)]),
        ("zero_remainder_value", Certificate(((0,), (0, 0, 1)), (0, 1), 0, 1),
         [(0, 0)]),
        ("three_distinct_fibre_values", Certificate(
            ((2, 1), (-1, 0, 1), (1,)), (-1, 1), 0, 1),
         [(1, 0), (1, 1), (1, 3)]),
        ("signed_branch_coefficients", Certificate(
            ((0,), (1, 0, -1), (0, 1)), (2,), 0, 1),
         [(-1, 1)]),
    ]
    example_checks = []
    for name, raw, expected in examples:
        cert = checked(raw)
        found = cert.solutions()
        assert found == expected, (name, found, expected)
        expanded = expand_equation(cert.branches, cert.remainder)
        h, k = cert.height_x, cert.height_y
        extra_tests = 0
        for x in range(-h-2, h+3):
            for y in range(-k-2, k+3):
                value = cert.equation_value(x, y)
                assert value == evaluate_expansion(expanded, x, y)
                if value == 0:
                    assert (x, y) in found
                extra_tests += 1
        example_checks.append(dict(name=name, **cert.metadata(), points=found,
                                   enlarged_box_tests=extra_tests,
                                   remainder_zero_points=[p for p in found
                                                          if evaluate(cert.remainder, p[0]) == 0]))

    malformed = [
        ("zero_remainder_empty", Certificate(((0,), (0, 1)), (), 0, 1)),
        ("zero_remainder_trailing", Certificate(((0,), (0, 1)), (0, 0), 0, 1)),
        ("single_branch", Certificate(((0,),), (1,), 0, 0)),
        ("index_too_large", Certificate(((0,), (0, 1)), (1,), 0, 2)),
        ("negative_index", Certificate(((0,), (0, 1)), (1,), -1, 1)),
        ("equal_degrees", Certificate(((0,), (0, 1)), (0, 1), 0, 1)),
        ("identical_indices", Certificate(((0,), (0, 1)), (1,), 0, 0)),
        ("noninteger_coefficient", Certificate(((0,), (0, 1.5)), (1,), 0, 1)),
        ("boolean_coefficient", Certificate(((0,), (0, True)), (1,), 0, 1)),
        ("invalid_polynomial_shape", Certificate(((0,), "x"), (1,), 0, 1)),
        ("noninteger_index", Certificate(((0,), (0, 1)), (1,), 0, 1.0)),
    ]
    rejection_checks = []
    for name, cert in malformed:
        result, error = cert.check()
        assert result is None and error is not None, name
        rejection_checks.append(dict(name=name, rejection=error))

    # Canonicalization must not trust the number of supplied trailing zeros.
    canonical = checked(Certificate(((0, 1, 0), (0, 0, 1, 0)), (1, 0, 0), 0, 1))
    assert canonical.difference == (0, 1, -1)
    assert canonical.remainder == (1,)

    return dict(
        status="passed",
        arithmetic="exact Python integers; standard library only",
        scope="Finite regression checks; universal proofs are in the paper. No Lean or embedded iPRA proof is claimed by these checks.",
        mixed_cubic=dict(**cubic.metadata(), points=cubic_solutions,
                         expansion=[dict(x_degree=i, y_degree=j, coefficient=c)
                                    for (i, j), c in sorted(expansion.items())],
                         expansion_value_checks=11*13),
        family_small_boxes=family_checks,
        certificate_examples=example_checks,
        malformed_rejections=rejection_checks,
        trailing_zero_normalization="passed",
    )


if __name__ == "__main__":
    report = verify()
    target = Path(__file__).resolve().parents[1] / "evidence" / "split_checks.json"
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"Passed: mixed cubic, 10 family boxes, 4 certificate boxes, {len(report['malformed_rejections'])} malformed rejections.")
    print(f"Report: {target}")
