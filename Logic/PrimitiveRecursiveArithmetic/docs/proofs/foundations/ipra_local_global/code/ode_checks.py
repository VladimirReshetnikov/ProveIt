#!/usr/bin/env python3
"""Exact finite checks for the polynomial-flow section.

Only Fraction/integer arithmetic is used.  These are implementation checks
of specified finite instances, not an iPRA proof checker or universal proof.
The nonlinear example deliberately uses small meshes: exact unreduced
trajectory sizes can grow extremely rapidly even for a simple polynomial.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as Q
from itertools import product
import json
from pathlib import Path

Poly = dict[tuple[int, ...], Q]
Vector = tuple[Q, ...]
Field = tuple[Poly, ...]


def ceilq(x: Q) -> int:
    return -((-x.numerator) // x.denominator)


def clean(p: Poly) -> Poly:
    return {a: Q(c) for a, c in p.items() if c}


def padd(p: Poly, q: Poly) -> Poly:
    ans = dict(p)
    for a, c in q.items():
        ans[a] = ans.get(a, Q(0)) + c
    return clean(ans)


def pmul(p: Poly, q: Poly) -> Poly:
    ans: Poly = {}
    for a, c in p.items():
        for b, d in q.items():
            e = tuple(x + y for x, y in zip(a, b))
            ans[e] = ans.get(e, Q(0)) + c * d
    return clean(ans)


def pdiff(p: Poly, i: int) -> Poly:
    ans: Poly = {}
    for a, c in p.items():
        if a[i]:
            b = list(a)
            b[i] -= 1
            ans[tuple(b)] = c * a[i]
    return clean(ans)


def peval(p: Poly, x: Vector) -> Q:
    ans = Q(0)
    for a, c in p.items():
        term = c
        for y, e in zip(x, a):
            term *= y**e
        ans += term
    return ans


def feval(f: Field, x: Vector) -> Vector:
    return tuple(peval(p, x) for p in f)


def vadd(x: Vector, y: Vector) -> Vector:
    return tuple(a + b for a, b in zip(x, y))


def vsub(x: Vector, y: Vector) -> Vector:
    return tuple(a - b for a, b in zip(x, y))


def scale(a: Q, x: Vector) -> Vector:
    return tuple(a * y for y in x)


def norm(x: Vector) -> Q:
    return max((abs(y) for y in x), default=Q(0))


def bounds(f: Field, b: Q) -> tuple[Q, Q]:
    m = max(Q(1), *(sum((abs(c) * b**sum(a) for a, c in p.items()), Q(0)) for p in f))
    l = max(sum((abs(c) * sum(a) * b ** (sum(a) - 1)
                 for a, c in p.items() if sum(a)), Q(0)) for p in f)
    return m, l


def euler(f: Field, x0: Vector, t: Q, n: int) -> list[Vector]:
    count = 2**n
    h = t / count
    nodes = [x0]
    for _ in range(count):
        nodes.append(vadd(nodes[-1], scale(h, feval(f, nodes[-1]))))
    return nodes


def polygon(nodes: list[Vector], t: Q, q: Q) -> Vector:
    assert 0 <= q <= t and t > 0
    count = len(nodes) - 1
    if q == t:
        return nodes[-1]
    z = q * count / t
    j = z.numerator // z.denominator
    return vadd(nodes[j], scale(z - j, vsub(nodes[j + 1], nodes[j])))


def cert_derivative(hpoly: Poly, f: Field) -> Poly:
    ans: Poly = {}
    for i, fi in enumerate(f):
        ans = padd(ans, pmul(pdiff(hpoly, i), fi))
    return ans


def remainder_bound(hpoly: Poly, b: Q, m: Q, t: Q) -> Q:
    cap = max(Q(1), b, m * t)
    return sum((abs(c) * 2 ** sum(a) * cap ** (sum(a) - 2)
                for a, c in hpoly.items() if sum(a) >= 2), Q(0))


class Checks:
    def __init__(self) -> None:
        self.counts: Counter[str] = Counter()

    def check(self, predicate: bool, category: str) -> None:
        if not predicate:
            raise AssertionError(category)
        self.counts[category] += 1


def inspect_case(checks: Checks, name: str, f: Field, x0: Vector,
                 b: Q, t: Q, nmin: int, nmax: int,
                 invariants: tuple[Poly, ...] = ()) -> dict:
    m, l = bounds(f, b)
    growth = 3 ** ceilq(l * t)
    k = max(1, ceilq(growth * l * m * t * t))
    certs = []
    for hp in invariants:
        checks.check(cert_derivative(hp, f) == {}, "coefficient_conservation_certificate")
        certs.append(remainder_bound(hp, b, m, t))
    for n in range(nmin, nmax + 1):
        nodes = euler(f, x0, t, n)
        fine = euler(f, x0, t, n + 1)
        count = 2**n
        for x in nodes + fine:
            checks.check(norm(x) <= b, "Euler_box")
        pair_bound = Q(growth) * l * m * t * t / (2 * count)
        for j, x in enumerate(fine):
            q = t * j / (2 * count)
            checks.check(norm(vsub(x, polygon(nodes, t, q))) <= pair_bound,
                         "dyadic_refinement_at_all_fine_nodes")
        # A sparse rational time grid exercises interior cells and reversed times.
        times = [t * Q(j, 7) for j in range(8)]
        values = {q: polygon(nodes, t, q) for q in times}
        for q, r in product(times, repeat=2):
            v = abs(r - q)
            lhs = norm(vsub(vsub(values[r], values[q]),
                            scale(r - q, feval(f, values[q]))))
            rhs = l * m * (v * v / 2 + (t / count) * v)
            checks.check(lhs <= rhs, "controlled_increment_residual")
            checks.check(norm(vsub(values[r], values[q])) <= m * v,
                         "polygon_time_Lipschitz")
        for hp, rh in zip(invariants, certs):
            h0 = peval(hp, x0)
            for q in times:
                checks.check(abs(peval(hp, values[q]) - h0)
                             <= rh * m * m * t * t / count,
                             "conservation_error")
        if n + 2 <= nmax + 1:
            much_finer = euler(f, x0, t, n + 2)
            for q in times:
                checks.check(norm(vsub(polygon(nodes, t, q),
                                       polygon(much_finer, t, q))) <= Q(k, count),
                             "finite_Cauchy_comparison")
    return {"name": name, "dimension": len(f), "horizon": str(t),
            "box": str(b), "magnitude_bound": str(m), "Lipschitz_bound": str(l),
            "tested_mesh_exponents": [nmin, nmax + 1],
            "growth_bound_bit_length": growth.bit_length(),
            "cauchy_constant_bit_length": k.bit_length(),
            "conservation_certificates": len(invariants)}


def run() -> dict:
    checks = Checks()
    for numerator in range(17):
        a = Q(numerator, 3)
        for count in range(1, 21):
            checks.check((1 + a / count) ** count <= 3 ** ceilq(a),
                         "rational_growth_bound")
    for a in [Q(0), Q(1, 3), Q(3, 2), Q(7)]:
        for count in range(1, 12):
            r = 1 + a / count
            e = Q(1, 7)
            total = Q(0)
            for j in range(count):
                defect = Q((j * j + 1) % 5, 13)
                e = r * e + defect
                total += defect
                checks.check(e <= r ** (j + 1) * (Q(1, 7) + total),
                             "variable_error_Gronwall")
    cases = []
    cases.append(inspect_case(checks, "exponential", ({(1,): Q(1)},),
                              (Q(1),), Q(3), Q(1), 0, 5))
    osc = ({(0, 1): Q(-1)}, {(1, 0): Q(1)})
    circle = {(2, 0): Q(1), (0, 2): Q(1)}
    cases.append(inspect_case(checks, "oscillator", osc, (Q(1), Q(0)),
                              Q(3), Q(1), 0, 5, (circle,)))
    # Local horizon chosen automatically: B=1, M=2, T=1/(2M)=1/4.
    cases.append(inspect_case(checks, "nonlinear_local_1_plus_x_squared",
                              ({(0,): Q(1), (2,): Q(1)},), (Q(0),),
                              Q(1), Q(1, 4), 0, 2))
    hermite_field = ({(0, 0, 0): Q(1)}, {(0, 1, 0): Q(-1)},
                     {(0, 1, 0): Q(1), (2, 1, 0): Q(1)})
    hermite_h = {(2, 1, 0): Q(1), (1, 1, 0): Q(2),
                 (0, 1, 0): Q(3), (0, 0, 1): Q(1)}
    cases.append(inspect_case(checks, "Hermite_f_1_plus_t_squared", hermite_field,
                              (Q(0), Q(1), Q(0)), Q(10), Q(2), 1, 5,
                              (hermite_h,)))
    # Coordinates (c,s,tau,area).
    area_field = ({(0, 1, 0, 0): Q(-1)}, {(1, 0, 0, 0): Q(1)},
                  {(0, 0, 0, 0): Q(1)},
                  {(2, 0, 0, 0): Q(1, 2), (0, 2, 0, 0): Q(1, 2)})
    circle4 = {(2, 0, 0, 0): Q(1), (0, 2, 0, 0): Q(1)}
    area_h = {(0, 0, 0, 1): Q(1), (2, 0, 1, 0): Q(-1, 2),
               (0, 2, 1, 0): Q(-1, 2)}
    cases.append(inspect_case(checks, "circle_area_accumulator", area_field,
                              (Q(1), Q(0), Q(0), Q(0)), Q(9), Q(1), 0, 4,
                              (circle4, area_h)))
    # A deliberately false certificate must be rejected.
    checks.check(cert_derivative({(1,): Q(1)}, ({(1,): Q(1)},)) != {},
                 "invalid_conservation_certificate_rejected")
    return {"status": "passed", "arithmetic": "exact integers and Fraction only",
            "scope": "finite implementation checks; not universal proofs or an iPRA proof checker",
            "assertions": sum(checks.counts.values()),
            "categories": dict(sorted(checks.counts.items())), "cases": cases}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    report = run()
    text = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    print(text, end="")
