#!/usr/bin/env python3
"""Regenerate exact finite identities and compact Report214 result files.

Finite computations do not prove an asymptotic estimate or an inverse radius.
"""
import argparse
from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from itertools import permutations
from math import comb, factorial
from pathlib import Path
import csv
import io
import json
import sys
sys.dont_write_bytecode = True
from common import (MAX_K, ENUM_K, MAX_H, SELECTED_K, RESULT_FILES, require,
                    json_bytes, unique_json, sha256, falling, rising, bells,
                    recurrence, branch, profiles, multiplicity, compositions,
                    polynomial_product, polynomial_value, falling_coefficients,
                    falling_to_monomial, signed_stirling_first, shifted_bell,
                    exact_ratio, decimal_ratio)

HERE = Path(__file__).resolve().parent
SOURCE_ROOT = HERE.parent if HERE.name == "code" else HERE
MATH_GUARDS = ("recurrence_boundary", "walk_row", "newton_history", "urn_average",
               "polynomial_evaluation", "partition_egf", "explicit_G2",
               "integer_interpolation", "poisson_kernel")


class Audit:
    def __init__(self, injection):
        self.injection = injection
        self.counts = Counter()

    def equal(self, lhs, rhs, name, context=None):
        require((lhs + 1 if self.injection == name else lhs) == rhs, name, context)
        self.counts[name] += 1

    def at_most(self, lhs, rhs, name, context=None):
        require(lhs <= rhs, name, context)
        self.counts[name] += 1


def enumerate_walks(k):
    """Generate canonical words solely by discovered edges or a fresh next label.

    The discovered graph is always a tree. Existing non-neighbors are never used.
    No recurrence, Bell number, partition, or stored moment drives this search.
    """
    children, parents, depth, departures = [[]], [-1], [0], [0]
    roots, occupancy = Counter(), Counter()

    def visit(v, left):
        if depth[v] > left or (left - depth[v]) % 2:
            return
        if left == 0:
            if v == 0:
                roots[departures[0]] += 1
                occupancy.update(departures)
            return
        departures[v] += 1
        if v:
            visit(parents[v], left - 1)
        if depth[v] + 1 <= left - 1:
            for nxt in children[v]:
                visit(nxt, left - 1)
            nxt = len(parents)
            children[v].append(nxt)
            children.append([])
            parents.append(v)
            depth.append(depth[v] + 1)
            departures.append(0)
            visit(nxt, left - 1)
            departures.pop()
            depth.pop()
            parents.pop()
            children.pop()
            children[v].pop()
        departures[v] -= 1

    visit(0, 2 * k)
    return roots, occupancy


def csv_bytes(header, rows):
    stream = io.StringIO(newline="")
    writer = csv.writer(stream, lineterminator="\n")
    writer.writerow(header)
    writer.writerows(rows)
    return stream.getvalue().encode("utf-8")


def compute(injection=None):
    audit = Audit(injection)
    f, e = recurrence(MAX_K)
    a = [sum(row) for row in f]
    bell = bells(MAX_K + MAX_H + 3)
    for k in range(1, MAX_K + 1):
        audit.equal(f[k][1], a[k - 1], "recurrence_boundary", (k, 1))
        audit.equal(f[k][k], bell[k], "recurrence_boundary", (k, k))
        if k >= 2:
            audit.equal(f[k][k - 1], (k - 1) * bell[k - 1], "one_deficit", k)
        audit.at_most(a[k], comb(2 * k, k) // (k + 1) * factorial(k), "rough_bound", k)
    for t in range(MAX_K):
        for q in range(1, MAX_K - t + 1):
            audit.equal(e[t][q], branch(f, t, q), "branch_formula", (t, q))
    enum_rows = []
    for k in range(1, ENUM_K + 1):
        roots, occupancy = enumerate_walks(k)
        row = [roots[m] for m in range(1, k + 1)]
        for m in range(1, k + 1):
            audit.equal(roots[m], f[k][m], "walk_row", (k, m))
            audit.equal(Q(2 * k * roots[m], m), occupancy[m], "weighted_rotation", (k, m))
        enum_rows.append({"k": k, "a_k": sum(row), "root_row": row})

    @lru_cache(None)
    def R(q, t):
        return branch(f, t, q) / comb(q + t - 1, t)

    @lru_cache(None)
    def c(q, h):
        return sum((-1) ** (h - t) * comb(h, t) * R(q, t) for t in range(h + 1))

    @lru_cache(None)
    def d(q, h):
        return sum((-1) ** (h - t) * branch(f, t, q)
                   * Q(rising(q + t, h - t), factorial(h - t)) for t in range(h + 1))

    polys = {}
    serialized_polys = {}
    for h in range(1, MAX_H + 1):
        coefficients = falling_coefficients([d(q, h) for q in range(h + 1)])
        monomial = falling_to_monomial(coefficients)
        polys[h] = coefficients
        audit.equal(d(0, h), 0, "polynomial_zero", h)
        for q in range(0, 20):
            evaluated = sum(coefficients[u] * falling(q, u) for u in range(h + 1))
            audit.equal(evaluated, d(q, h), "polynomial_evaluation", (h, q))
            audit.equal(polynomial_value(monomial, q), d(q, h), "polynomial_monomial", (h, q))
            if q:
                audit.equal(d(q, h), Q(rising(q, h), factorial(h)) * c(q, h), "newton_d_identity", (h, q))
        serialized_polys[str(h)] = {
            "d_monomial_coefficients_ascending": [exact_ratio(x) for x in monomial],
            "d_falling_coefficients_ascending": [exact_ratio(x) for x in coefficients],
            "P_monomial_coefficients_ascending": [exact_ratio(x) for x in coefficients],
        }
    for q in range(1, 20):
        audit.equal(d(q, 2), Q(q * (q + 3), 2), "explicit_d2", q)
        audit.equal(d(q, 3), Q(q * (q + 4) * (q + 5), 6), "explicit_d3", q)
        for t in range(7):
            audit.equal(sum(c(q, h) * comb(t, h) for h in range(t + 1)), R(q, t), "binomial_inversion", (q, t))

    def history_pieces(qs, ts, p):
        values = [Q(1)] + [Q(0)] * p
        for q, t in zip(qs, ts):
            local = [Q(1)] + [c(q, j + 1) * comb(t, j + 1) if t >= j + 1 else Q(0)
                                  for j in range(1, p + 1)]
            values = [sum(values[i] * local[j - i] for i in range(j + 1)) for j in range(p + 1)]
        return values

    def conditional_pieces(qs, s, p):
        coefficients = {(0, 0): Q(1)}
        for q in qs:
            nxt = dict(coefficients)
            for (j, H), coefficient in coefficients.items():
                for h in range(2, p - j + 2):
                    key = (j + h - 1, H + h)
                    nxt[key] = nxt.get(key, Q(0)) + coefficient * d(q, h)
            coefficients = nxt
        n = sum(qs)
        result = [Q(0)] * (p + 1)
        for (j, H), coefficient in coefficients.items():
            result[j] += Q(falling(s, H), rising(n, H)) * coefficient
        return result

    def G1(n, s):
        return Q(comb(s, 2) * ((n - 1) * bell[n - 1] + 4 * bell[n]), (n + 1) * bell[n]) if s >= 2 else Q(0)

    def G2(n, s):
        def fb(degree, shift):
            # Guard vanishing falling factors before inspecting a Bell index.
            return falling(n, degree) * bell[n + shift] if n >= degree else 0
        first = fb(3, -2) + 12 * fb(2, -1) + 30 * n * bell[n]
        second = (fb(4, -2) - fb(4, -3) + 8 * (fb(3, -1) - fb(3, -2))
                  + 16 * (fb(2, 0) - fb(2, -1)))
        return (Q(falling(s, 3) * first, 6 * rising(n, 3) * bell[n])
                + Q(falling(s, 4) * second, 8 * rising(n, 4) * bell[n]))

    # Enumerate all profiles with exact set-partition multiplicities and all urn occupancies.
    for n in range(1, 6):
        partitions = list(profiles(n))
        audit.equal(sum(multiplicity(qs) for qs in partitions), bell[n], "partition_mass", n)
        for s in range(6):
            aggregate = [Q(0)] * 4
            branch_sum = Q(0)
            for qs in partitions:
                mass = Q(0)
                average = [Q(0)] * 4
                branch_average = Q(0)
                weighted_collisions = [Q(0)] * (s + 1)
                for ts in compositions(s, len(qs)):
                    probability = Q(1, comb(n + s - 1, s))
                    value, majorant = Q(1), 1
                    for q, t in zip(qs, ts):
                        probability *= comb(q + t - 1, t)
                        value *= R(q, t)
                        majorant *= 1 if t < 2 else 4 ** (t - 1) * factorial(t)
                    mass += probability
                    branch_average += probability * value
                    collision = s - sum(t > 0 for t in ts)
                    weighted_collisions[collision] += probability * majorant
                    pieces = history_pieces(qs, ts, 3)
                    for p in range(1, 4):
                        if collision <= p:
                            audit.equal(sum(pieces[:p + 1]), value, "newton_history", (qs, ts, p))
                    for j in range(4):
                        average[j] += probability * pieces[j]
                audit.equal(mass, 1, "urn_mass", (qs, s))
                expected = conditional_pieces(qs, s, 3)
                for j in range(4):
                    audit.equal(average[j], expected[j], "urn_average", (qs, s, j))
                    aggregate[j] += Q(multiplicity(qs), bell[n]) * average[j]
                branch_sum += multiplicity(qs) * branch_average * comb(n + s - 1, s)
                marker = [Q(1)]
                for j in range(s):
                    marker = polynomial_product(marker, [1, Q(8 * (max(qs) * j + j * j), n)])
                for j in range(s + 1):
                    audit.at_most(weighted_collisions[j], marker[j], "marked_collision", (qs, s, j))
            audit.equal(branch_sum, f[n + s][n], "partition_branch", (n, s))
            audit.equal(aggregate[1], G1(n, s), "explicit_G1", (n, s))
            audit.equal(aggregate[2], G2(n, s), "explicit_G2", (n, s))

    def block_egf(n, hs):
        poly = [Q(1)]
        for h in hs:
            poly = polynomial_product(poly, polys[h])
        return sum(coefficient * falling(n, u) * shifted_bell(n - u, len(hs), bell)
                   for u, coefficient in enumerate(poly) if u <= n)

    configurations = ((2,), (3,), (4,), (5,), (6,), (2, 2), (2, 3), (2, 2, 2))
    for n in range(1, 9):
        for hs in configurations:
            direct = Q(0)
            for qs in profiles(n):
                subtotal = Q(0)
                for indices in permutations(range(len(qs)), len(hs)):
                    value = Q(1)
                    for index, h in zip(indices, hs):
                        value *= d(qs[index], h)
                    subtotal += value
                direct += multiplicity(qs) * subtotal
            audit.equal(direct, block_egf(n, hs), "partition_egf", (n, hs))
        for s in range(7):
            first = Q(falling(s, 2), rising(n, 2) * bell[n]) * block_egf(n, (2,))
            second = (Q(falling(s, 3), rising(n, 3) * bell[n]) * block_egf(n, (3,))
                      + Q(falling(s, 4), 2 * rising(n, 4) * bell[n]) * block_egf(n, (2, 2)))
            audit.equal(first, G1(n, s), "explicit_G1", (n, s, "EGF"))
            audit.equal(second, G2(n, s), "explicit_G2", (n, s, "EGF"))
    for r in range(7):
        stirling = signed_stirling_first(r)
        for N in range(21):
            audit.equal(shifted_bell(N, r, bell), sum(stirling[j] * bell[N + j] for j in range(r + 1)),
                        "poisson_shift_bell", (N, r))

    transforms = {}
    for k in range(1, MAX_K + 1):
        T1 = sum(comb(k, s) * bell[k - s] * G1(k - s, s) for s in range(k))
        T2 = sum(comb(k, s) * bell[k - s] * G2(k - s, s) for s in range(k))
        explicit_T1 = sum(Q(comb(k, s) * comb(s, 2) * ((k - s - 1) * bell[k - s - 1] + 4 * bell[k - s]),
                            k - s + 1) for s in range(2, k))
        audit.equal(T1, explicit_T1, "first_transform", k)
        transforms[k] = (T1 / bell[k + 1], T2 / bell[k + 1])
        audit.equal(sum(comb(k, s) * bell[k - s] for s in range(k)), bell[k + 1] - 1, "fresh_sum", k)
        for h in range(min(k, 6) + 1):
            audit.equal(sum(falling(s, h) * comb(k, s) * bell[k - s] for s in range(k + 1)),
                        falling(k, h) * bell[k + 1 - h], "deficit_factorial_moment", (k, h))
        for s in range(k):
            audit.equal(Q(k * comb(k - 1, s), k - s), comb(k, s), "rotation_cancellation", (k, s))

    # Scalar identities are checked BEFORE any Poisson summation. No truncated
    # floating-point Poisson series is presented as an exact expectation.
    for H in range(2, 7):
        for u in range(1, H + 1):
            v = u + H - 1
            def qvalue(ell):
                return rising(ell - v + 1, u - 1)
            coefficients = falling_coefficients([qvalue(ell) for ell in range(u)])
            for ell in range(19):
                audit.equal(sum(coefficients[t] * falling(ell, t) for t in range(u)), qvalue(ell),
                            "interpolation_basis", (H, u, ell))
            for k in range(1, 19):
                for z in (1, 2, 5):
                    original = Q(0)
                    for n in range(1, k + 1):
                        if n < u or k - n < H:
                            continue
                        factor = Q(comb(k, n) * falling(k - n, H) * falling(n, u), rising(n, H))
                        audit.equal(factor, k * comb(k - 1, n - u + v) * rising(n - u + 1, u - 1),
                                    "interpolation_cancellation", (H, u, k, n))
                        original += factor * Q(z) ** (n - u)
                    full = k * sum(coefficients[t] * falling(k - 1, t) * Q(z) ** (t - v)
                                   * Q(z + 1) ** (k - 1 - t) for t in range(u))
                    boundary = k * sum(Q(falling(k - 1, ell), factorial(ell)) * qvalue(ell)
                                       * Q(z) ** (ell - v) for ell in range(v))
                    audit.equal(original, full - boundary, "integer_interpolation", (H, u, k, z))
    for b in range(1, 5):
        for H in range(b + 1, 7):
            for u in range(b, H + 1):
                v = u + H - 1
                for t in range(u):
                    for x in (3, 8, 20):
                        for m in range(9):
                            y = m + b + 1
                            lhs = Q(m + b) ** (t - v) * Q(y) ** (x - 1 - t) / factorial(m)
                            rhs = (Q(y) ** (x + 1) / factorial(y) * falling(y, b + 1)
                                   * Q(y - 1) ** (t - v) * Q(y) ** (-t - 2))
                            audit.equal(lhs, rhs, "poisson_kernel", (b, H, u, t, x, m))
    require(set(MATH_GUARDS) <= set(audit.counts), "guard_coverage", sorted(audit.counts))

    selected = []
    csv_rows = []
    tex = ["% Generated by code/finite_checks.py; exact rationals rounded half-even to 6 decimal places.",
           "% Finite values only; these residuals do not establish the asymptotic remainder.",
           r"\begin{tabular}{r r r r r}", r"\toprule",
           r"$k$ & $a_k/(2B_{k+1})$ & $A_1(k)$ & $A_2(k)$ & Residual \\", r"\midrule"]
    for k in SELECTED_K:
        ratio = Q(a[k], 2 * bell[k + 1])
        A1, A2 = transforms[k]
        residual = ratio - 1 - A1 - A2
        values = (ratio, A1, A2, residual)
        selected.append({"k": k, "a_k": str(a[k]), "B_k_plus_1": str(bell[k + 1]),
                         **{key: exact_ratio(value) for key, value in zip(("ratio", "A1", "A2", "residual"), values)}})
        csv_rows.append([k, a[k], bell[k + 1]] + [entry for value in values
                        for entry in (value.numerator, value.denominator, decimal_ratio(value))])
        tex.append(str(k) + " & " + " & ".join(decimal_ratio(value) for value in values) + r" \\")
    tex.extend([r"\bottomrule", r"\end{tabular}", ""])
    rows_tex = ["% Generated by code/finite_checks.py; impossible entries are zero.",
                r"\begin{tabular}{r r r r r r}", r"\toprule",
                r"$k$ & $F_{k,1}$ & $F_{k,2}$ & $F_{k,3}$ & $F_{k,4}$ & $F_{k,5}$ \\", r"\midrule"]
    for k in range(1, 6):
        rows_tex.append(str(k) + " & " + " & ".join(str(f[k][m]) for m in range(1, 6)) + r" \\")
    rows_tex.extend([r"\bottomrule", r"\end{tabular}", ""])
    checks = {
        "schema": "Report214.finite-checks.v1", "all_checks_passed": True,
        "scope": {
            "fresh_recurrence_max_k": MAX_K, "independent_walk_enumeration_max_k": ENUM_K,
            "independently_enumerated_walks": sum(row["a_k"] for row in enum_rows),
            "polynomial_max_h": MAX_H, "polynomial_evaluation_q_range": [0, 19],
            "partition_urn_n_range": [1, 5], "partition_urn_s_range": [0, 5], "newton_orders": [1, 2, 3],
            "partition_egf_n_range": [1, 8], "partition_egf_configurations": [list(hs) for hs in configurations],
            "scalar_interpolation_H_range": [2, 6], "scalar_interpolation_k_range": [1, 18],
            "scalar_interpolation_z_values": [1, 2, 5], "poisson_kernel_b_range": [1, 4],
            "poisson_kernel_H_range": ["b+1", 6], "poisson_kernel_x_values": [3, 8, 20],
            "poisson_kernel_m_range": [0, 8],
            "arithmetic": "Python unbounded integers and fractions.Fraction; Decimal only for final display.",
            "limits": "Finite identities and inequalities only. No asymptotic estimate, derivative bound, effective onset, remainder constant, inverse radius, or growing-order validity is established by these checks. Poisson kernel checks are termwise algebra at the listed integer x values, not evaluation of an infinite sum.",
        },
        "guard_counts": dict(audit.counts),
        "root_array_sha256": sha256(json_bytes([row[:k + 1] for k, row in enumerate(f)])),
        "enumerated_rows": enum_rows, "selected_table": selected,
    }
    polynomial_document = {
        "schema": "Report214.polynomials.v1", "coefficient_encoding": "Exact rational numerator/denominator strings, ascending degree",
        "construction": "d_h values at 0,...,h give Delta^u d_h(0)/u! in the falling basis. These same coefficients are the monomial coefficients of P_h. Independently checked at q=0,...,19 against the finite branch formula.",
        "convention": "d_0=1; P_h=e^(-x) sum_{q>=1} d_h(q)x^q/q! is used here only for h>=1. d_1=P_1=0.",
        "polynomials": serialized_polys,
    }
    header = ["k", "a_k", "B_k_plus_1"] + [key + suffix for key in ("ratio", "A1", "A2", "residual")
                                                    for suffix in ("_numerator", "_denominator", "_decimal")]
    return {"checks.json": json_bytes(checks), "selected_table.csv": csv_bytes(header, csv_rows),
            "polynomials.json": json_bytes(polynomial_document), "table.tex": "\n".join(tex).encode(),
            "rows.tex": "\n".join(rows_tex).encode()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True, help="New output directory outside the source tree")
    parser.add_argument("--compare", type=Path, help="Require exact agreement with this result directory")
    parser.add_argument("--inject-failure", choices=MATH_GUARDS, help="Deliberately corrupt a mathematical comparison")
    args = parser.parse_args()
    require(not args.out.exists() and not args.out.is_symlink(), "output_exists", str(args.out))
    out = args.out.resolve()
    require(out != SOURCE_ROOT and SOURCE_ROOT not in out.parents and out not in SOURCE_ROOT.parents,
            "output_inside_source", str(out))
    require(out.parent.is_dir(), "output_parent", str(out.parent))
    outputs = compute(args.inject_failure)
    if args.compare is not None:
        require(args.compare.is_dir() and not args.compare.is_symlink()
                and set(p.name for p in args.compare.iterdir()) == set(RESULT_FILES)
                and all((args.compare / name).is_file() and not (args.compare / name).is_symlink() for name in RESULT_FILES),
                "reference_inventory", "Expected exactly the five documented regular result files")
        for name in ("checks.json", "polynomials.json"):
            require(unique_json(args.compare / name) == json.loads(outputs[name]), "reference_comparison", name)
        for name in RESULT_FILES:
            require((args.compare / name).read_bytes() == outputs[name], "reference_comparison", name)
    out.mkdir()
    for name in RESULT_FILES:
        (out / name).write_bytes(outputs[name])
    print(json_bytes({"all_checks_passed": True, "result_sha256": {name: sha256(outputs[name]) for name in RESULT_FILES}}).decode(), end="")


if __name__ == "__main__":
    main()
