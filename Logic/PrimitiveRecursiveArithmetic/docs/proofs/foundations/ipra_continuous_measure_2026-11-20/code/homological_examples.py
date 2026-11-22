#!/usr/bin/env python3
"""Exact-rational checks for the signed homological perturbation chapter.

Only the Python standard library is used.  The computations are reproducible
examples and regression checks, not a proof of the universal theorem or an
object-language iPRA derivation.  All displayed residuals and bounds are
computed with fractions.Fraction; no floating-point tolerance is used.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as Q
import json
from pathlib import Path


@dataclass(frozen=True)
class Mat:
    rows: int
    cols: int
    data: tuple[tuple[Q, ...], ...]

    def __post_init__(self):
        assert self.rows >= 0 and self.cols >= 0
        assert len(self.data) == self.rows
        assert all(len(row) == self.cols for row in self.data)

    @staticmethod
    def of(rows):
        rows = tuple(tuple(Q(x) for x in row) for row in rows)
        return Mat(len(rows), len(rows[0]) if rows else 0, rows)

    @staticmethod
    def zero(rows, cols):
        return Mat(rows, cols, tuple(tuple(Q(0) for _ in range(cols))
                                    for _ in range(rows)))

    @staticmethod
    def identity(n):
        return Mat(n, n, tuple(tuple(Q(i == j) for j in range(n))
                              for i in range(n)))

    def __add__(self, other):
        assert (self.rows, self.cols) == (other.rows, other.cols)
        return Mat(self.rows, self.cols,
                   tuple(tuple(self.data[i][j] + other.data[i][j]
                               for j in range(self.cols))
                         for i in range(self.rows)))

    def __neg__(self):
        return Mat(self.rows, self.cols,
                   tuple(tuple(-x for x in row) for row in self.data))

    def __sub__(self, other):
        return self + (-other)

    def __matmul__(self, other):
        assert self.cols == other.rows
        return Mat(self.rows, other.cols,
                   tuple(tuple(sum((self.data[i][k] * other.data[k][j]
                                    for k in range(self.cols)), Q(0))
                               for j in range(other.cols))
                         for i in range(self.rows)))

    def scale(self, scalar):
        return Mat(self.rows, self.cols,
                   tuple(tuple(Q(scalar) * x for x in row)
                         for row in self.data))

    def norm(self):
        return max((sum((abs(x) for x in row), Q(0))
                    for row in self.data), default=Q(0))

    def power(self, exponent):
        assert self.rows == self.cols and exponent >= 0
        answer = Mat.identity(self.rows)
        for _ in range(exponent):
            answer = answer @ self
        return answer

    def inverse(self):
        """Independent exact Gaussian elimination, with bounded pivot scans."""
        assert self.rows == self.cols
        n = self.rows
        a = [list(row) + [Q(i == j) for j in range(n)]
             for i, row in enumerate(self.data)]
        for col in range(n):
            choices = [row for row in range(col, n) if a[row][col] != 0]
            if not choices:
                raise ValueError("singular matrix")
            pivot = choices[0]
            a[col], a[pivot] = a[pivot], a[col]
            scale = a[col][col]
            a[col] = [x / scale for x in a[col]]
            for row in range(n):
                if row != col:
                    scale = a[row][col]
                    a[row] = [x - scale * y for x, y in zip(a[row], a[col])]
        result = Mat(n, n, tuple(tuple(row[n:]) for row in a))
        assert self @ result == Mat.identity(n)
        assert result @ self == Mat.identity(n)
        return result

    def strings(self):
        return [[str(x) for x in row] for row in self.data]


@dataclass(frozen=True)
class Contraction:
    d: Mat
    b: Mat
    i: Mat
    p: Mat
    h: Mat
    c_degrees: tuple[int, ...]
    b_degrees: tuple[int, ...]


def is_degree(matrix, source, target, shift):
    return (matrix.cols == len(source) and matrix.rows == len(target)
            and all(matrix.data[i][j] == 0 or target[i] == source[j] + shift
                    for i in range(matrix.rows) for j in range(matrix.cols)))


def valid_contraction(c):
    d, b, i, p, h = c.d, c.b, c.i, c.p, c.h
    return all([
        is_degree(d, c.c_degrees, c.c_degrees, -1),
        is_degree(b, c.b_degrees, c.b_degrees, -1),
        is_degree(i, c.b_degrees, c.c_degrees, 0),
        is_degree(p, c.c_degrees, c.b_degrees, 0),
        is_degree(h, c.c_degrees, c.c_degrees, 1),
        (d @ d).norm() == 0, (b @ b).norm() == 0,
        d @ i == i @ b, p @ d == b @ p,
        p @ i == Mat.identity(b.rows),
        d @ h + h @ d == Mat.identity(d.rows) - i @ p,
        (h @ i).norm() == 0, (p @ h).norm() == 0,
        (h @ h).norm() == 0,
    ])


def base_contraction():
    # Total coordinates: C_0 first (2 entries), then C_1 (2 entries).
    # Small coordinates: one B_0 entry, then one B_1 entry.
    c = Contraction(
        Mat.of([[0, 0, 1, 0], [0, 0, 0, 0],
                [0, 0, 0, 0], [0, 0, 0, 0]]),
        Mat.zero(2, 2),
        Mat.of([[0, 0], [1, 0], [0, 0], [0, 1]]),
        Mat.of([[0, 1, 0, 0], [0, 0, 0, 1]]),
        Mat.of([[0, 0, 0, 0], [0, 0, 0, 0],
                [1, 0, 0, 0], [0, 0, 0, 0]]),
        (0, 0, 1, 1), (0, 1),
    )
    assert valid_contraction(c)
    return c


def perturbation(a, beta, gamma, tau):
    return Mat.of([[0, 0, a, beta], [0, 0, gamma, tau],
                   [0, 0, 0, 0], [0, 0, 0, 0]])


def three_degree_example():
    """A truncation whose transferred differential is not square-zero.

    C_0, C_1, C_2 have dimensions 2, 3, 2.  Two contractible pairs are
    split off, leaving one homology coordinate in each degree.  A small
    degree-preserving change of basis gives an independently square-zero
    perturbed differential.  Its exact transferred differential is zero,
    but the first Neumann truncation has nonzero square.
    """
    def sparse(n, m, entries):
        return Mat(n, m, tuple(tuple(Q(entries.get((i, j), 0))
                                    for j in range(m)) for i in range(n)))
    c = Contraction(
        sparse(7, 7, {(0, 2): 1, (3, 5): 1}), Mat.zero(3, 3),
        sparse(7, 3, {(1, 0): 1, (4, 1): 1, (6, 2): 1}),
        sparse(3, 7, {(0, 1): 1, (1, 4): 1, (2, 6): 1}),
        sparse(7, 7, {(2, 0): 1, (5, 3): 1}),
        (0, 0, 1, 1, 1, 2, 2), (0, 1, 2),
    )
    entries = {(j, k): (Q(1) if j == k else Q(1, 16))
               for block in [[0, 1], [2, 3, 4], [5, 6]]
               for j in block for k in block}
    change = sparse(7, 7, entries)
    delta = change @ c.d @ change.inverse() - c.d
    assert valid_contraction(c)
    return c, delta


def neumann(t, length):
    assert t.rows == t.cols and length >= 0
    result = Mat.zero(t.rows, t.cols)
    term = Mat.identity(t.rows)
    for _ in range(length):
        result = result + term
        term = term @ (-t)
    identity = Mat.identity(t.rows)
    assert (identity + t) @ result == identity - (-t).power(length)
    assert result @ (identity + t) == identity - (-t).power(length)
    return result


def transfer(c, a):
    return Contraction(c.d, c.b + c.p @ a @ c.i,
                       c.i - c.h @ a @ c.i,
                       c.p - c.p @ a @ c.h,
                       c.h - c.h @ a @ c.h,
                       c.c_degrees, c.b_degrees)


def put_d(c, d):
    return Contraction(d, c.b, c.i, c.p, c.h, c.c_degrees, c.b_degrees)


def exact_transfer(c, delta):
    assert valid_contraction(c)
    assert is_degree(delta, c.c_degrees, c.c_degrees, -1)
    dp = c.d + delta
    assert (dp @ dp).norm() == 0
    identity = Mat.identity(c.d.rows)
    f = (identity + c.h @ delta).inverse()
    g = (identity + delta @ c.h).inverse()
    a = g @ delta
    assert a == delta @ f
    result = put_d(transfer(c, a), dp)
    assert valid_contraction(result)
    return a, result


def check_finite(c, delta, length, exact_a, exact_c):
    d, b, i, p, h = c.d, c.b, c.i, c.p, c.h
    dp = d + delta
    a = delta @ neumann(h @ delta, length)
    r = delta @ (-(h @ delta)).power(length)
    assert r == (-(delta @ h)).power(length) @ delta
    assert delta - a - delta @ h @ a == r
    assert delta - a - a @ h @ delta == r
    m = d @ a + a @ d + a @ i @ p @ a
    t = transfer(c, a)
    assert t.p @ t.i == Mat.identity(b.rows)
    assert (t.h @ t.i).norm() == (t.p @ t.h).norm() == 0
    assert (t.h @ t.h).norm() == 0
    residuals = [
        t.b @ t.b,
        dp @ t.i - t.i @ t.b,
        t.p @ dp - t.b @ t.p,
        dp @ t.h + t.h @ dp - (Mat.identity(d.rows) - t.i @ t.p),
    ]
    factorizations = [
        p @ m @ i,
        r @ i + h @ m @ i,
        p @ r + p @ m @ h,
        r @ h + h @ r + h @ m @ h,
    ]
    assert residuals == factorizations
    left = Mat.identity(d.rows) + delta @ h
    right = Mat.identity(d.rows) + h @ delta
    e = i @ p
    assert left @ m @ right == (
        -(left @ d @ r) - r @ d @ right - delta @ e @ r
        - r @ e @ delta + r @ e @ r)

    D, H, U, I, P = d.norm(), h.norm(), delta.norm(), i.norm(), p.norm()
    q = max((h @ delta).norm(), (delta @ h).norm())
    assert 0 <= q < 1
    km = U * (2 * (1 + q) * D + 3 * U * I * P) / (1 - q) ** 2
    assert r.norm() <= U * q ** length
    assert m.norm() <= km * q ** length
    factors = [P * I * km, I * (U + H * km), P * (U + H * km),
               2 * H * U + H * H * km]
    bounds = [value * q ** length for value in factors]
    norms = [value.norm() for value in residuals]
    assert all(actual <= bound for actual, bound in zip(norms, bounds))
    # Independently obtained rational inverses serve as an exact tail oracle.
    errors = [(exact_a - a).norm(), (exact_c.i - t.i).norm(),
              (exact_c.p - t.p).norm(), (exact_c.h - t.h).norm(),
              (exact_c.b - t.b).norm()]
    tail_bounds = [U * q ** length / (1 - q),
                   I * q ** (length + 1) / (1 - q),
                   P * q ** (length + 1) / (1 - q),
                   H * q ** (length + 1) / (1 - q),
                   P * I * U * q ** length / (1 - q)]
    assert all(actual <= bound for actual, bound in zip(errors, tail_bounds))
    return {"N": length, "q": str(q), "K_M": str(km),
            "residuals": list(map(str, norms)),
            "residual_bounds": list(map(str, bounds)),
            "errors_A_i_p_h_b": list(map(str, errors)),
            "tail_bounds_A_i_p_h_b": list(map(str, tail_bounds))}, factors


def geometric_clock(q, k, constant):
    assert 0 <= q < 1 and k >= 0 and constant >= 1
    invgap = 1 / (1 - q)
    block = (invgap.numerator + invgap.denominator - 1) // invgap.denominator
    bits = constant.numerator.bit_length()
    length = block * (k + bits)
    assert constant <= 2 ** bits
    assert q ** block <= Q(1, 2)
    assert constant * q ** length <= Q(1, 2 ** k)
    return length


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    c = base_contraction()
    delta = perturbation(Q(1, 4), Q(1, 8), Q(1, 5), Q(1, 50))
    exact_a, exact_c = exact_transfer(c, delta)
    assert exact_c.b == Mat.zero(2, 2)
    rows = []
    for length in range(13):
        row, factors = check_finite(c, delta, length, exact_a, exact_c)
        rows.append(row)
    constant = max([Q(1)] + factors)
    clock_n = geometric_clock(Q(3, 8), 16, constant)
    clock_row, _ = check_finite(c, delta, clock_n, exact_a, exact_c)
    assert all(Q(x) <= Q(1, 2 ** 16) for x in clock_row["residual_bounds"])

    # Exact finite nilpotence, despite a product norm greater than one.
    nil_delta = perturbation(0, 3, 4, 5)
    assert (c.h @ nil_delta).power(2).norm() == 0
    assert (nil_delta @ c.h).power(2).norm() == 0
    nil_a = nil_delta @ neumann(c.h @ nil_delta, 2)
    nil_model = put_d(transfer(c, nil_a), c.d + nil_delta)
    assert valid_contraction(nil_model)
    assert nil_model.b.data[0][1] == -7
    assert max((c.h @ nil_delta).norm(), (nil_delta @ c.h).norm()) == 4

    # A small retained-model differential can change homology.
    changed_delta = perturbation(Q(1, 4), Q(1, 8), Q(1, 5), Q(1, 25))
    changed_a, changed_c = exact_transfer(c, changed_delta)
    assert changed_c.b.data[0][1] == Q(1, 50)
    eta = (changed_delta - delta).norm()
    sensitivity = eta / (1 - Q(3, 8)) ** 2
    assert (changed_a - exact_a).norm() <= sensitivity
    for actual, factor in [((changed_c.b - exact_c.b).norm(), c.p.norm()*c.i.norm()),
                           ((changed_c.i - exact_c.i).norm(), c.h.norm()*c.i.norm()),
                           ((changed_c.p - exact_c.p).norm(), c.p.norm()*c.h.norm()),
                           ((changed_c.h - exact_c.h).norm(), c.h.norm()**2)]:
        assert actual <= factor * sensitivity

    # An explicit cycle/filling transport check, independent of residual norms.
    original_filler = Mat.of([[0], [0], [2], [3]])
    z = exact_c.d @ original_filler
    s = exact_c.p @ original_filler
    filler = exact_c.h @ z + exact_c.i @ s
    assert exact_c.d @ filler == z
    assert filler.norm() <= (c.h.norm()*z.norm()+c.i.norm()*s.norm())/(1-Q(3,8))

    # Mutated input normalization and a wrong perturbation sign are rejected.
    corrupt = Contraction(c.d, c.b, c.i, c.p, c.h.scale(2),
                          c.c_degrees, c.b_degrees)
    assert not valid_contraction(corrupt)
    wrong_i = c.i + c.h @ exact_a @ c.i
    assert (exact_c.d @ wrong_i - wrong_i @ exact_c.b).norm() > 0

    # Two-term examples cannot test a nonzero b_N^2.  This three-degree
    # independent conjugation example resolves that concrete testing gap.
    three_c, three_delta = three_degree_example()
    three_a, three_exact = exact_transfer(three_c, three_delta)
    assert three_exact.b == Mat.zero(3, 3)
    three_rows = [check_finite(three_c, three_delta, length,
                              three_a, three_exact)[0] for length in range(9)]
    assert Q(three_rows[1]["residuals"][0]) == Q(1, 68850)
    assert Q(three_rows[1]["q"]) == Q(17, 135)

    # Deterministic rational parameter cases, including negative entries.
    cases = 0
    residual_cases = 0
    for a in [Q(-1, 3), Q(0), Q(1, 4)]:
        for beta in [Q(-1, 5), Q(1, 8)]:
            for gamma in [Q(1, 7), Q(1, 5)]:
                for tau in [Q(0), Q(1, 50), Q(1, 25)]:
                    dd = perturbation(a, beta, gamma, tau)
                    aa, cc = exact_transfer(c, dd)
                    assert cc.b.data[0][1] == tau - gamma*beta/(1+a)
                    cases += 1
                    for length in range(9):
                        check_finite(c, dd, length, aa, cc)
                        residual_cases += 1

    result = {
        "status": "all exact-rational checks passed",
        "scope": "finite examples; not a formal proof of the universal theorem",
        "schur_example": {"parameters_a_beta_gamma_tau": ["1/4", "1/8", "1/5", "1/50"],
                          "transferred_b": exact_c.b.strings(), "q": "3/8",
                          "neumann_rows": rows},
        "clock_example": {"requested_bits": 16, "K": str(constant),
                          "N": clock_n, "certificate": clock_row},
        "nilpotent_example": {"nilpotence_exponent": 2, "product_norm": "4",
                              "transferred_b": nil_model.b.strings()},
        "homology_change_example": {"new_tau": "1/25", "new_b": "1/50",
                                    "delta_distance": str(eta),
                                    "resolvent_bound": str(sensitivity)},
        "nonzero_square_defect_example": {
            "C_dimensions": [2, 3, 2], "B_dimensions": [1, 1, 1],
            "change_of_basis_offdiagonal": "1/16", "q": "17/135",
            "exact_transferred_differential": "zero",
            "N_1_square_defect_norm": "1/68850", "neumann_rows": three_rows},
        "parameter_cases": cases, "parameter_truncation_cases": residual_cases,
        "cycle_filling_transport": "passed", "mutated_input_rejection": "passed",
        "wrong_sign_detection": "passed",
    }
    output = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(output, encoding="utf-8")
        print(json.dumps({"status": result["status"], "parameter_cases": cases,
                          "parameter_truncation_cases": residual_cases,
                          "output": str(args.output)}, indent=2))
    else:
        print(output, end="")


if __name__ == "__main__":
    main()
