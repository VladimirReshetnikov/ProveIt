#!/usr/bin/env python3
"""Exact, finite checks accompanying article.tex (Python 3.10+, standard library).

The root-profile atlas compares the closed reduction formula against independent
exhaustive enumeration of all admissible divisors. It checks the combinatorial
formula, NOT the analytic realization or the classification theorem's proof.
No numerical root finding, floating-point sampling, or external packages are used.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
import sys


@dataclass(frozen=True)
class Factor:
    name: str
    radius: F
    negative: bool = False
    unit: str = ""  # '', '+', '-', or 'other'; conjugate pairs are one factor.


def check(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def is_minimal_spectrum(factors: tuple[Factor, ...], mult: tuple[int, ...]) -> bool:
    """Direct theorem predicate, deliberately separate from the core algorithm."""
    for f, m in zip(factors, mult):
        if f.unit == "other" and m:
            return False
        if f.unit in ("+", "-") and m > 1:
            return False
    active = [(f, m) for f, m in zip(factors, mult) if m and not f.unit]
    if not active:
        return any(f.unit == "-" and m == 1 for f, m in zip(factors, mult))
    radii = sorted({f.radius for f, _ in active})
    if not (radii[-1] < 1 or radii[0] > 1):
        return False
    for r in {radii[0], radii[-1]}:
        circle = [(f, m) for f, m in active if f.radius == r]
        anchors = [m for f, m in circle if f.negative]
        if not anchors or anchors[0] != max(m for _, m in circle):
            return False
    if len(radii) == 1:
        m = next(m for f, m in active if f.negative)
        if m % 2 == 0:
            return False
    return True


def side_core(factors: tuple[Factor, ...], mult: tuple[int, ...], inside: bool) -> tuple[int, ...]:
    chosen = [i for i, f in enumerate(factors)
              if mult[i] and not f.unit and (f.radius < 1) == inside]
    anchors = [i for i in chosen if factors[i].negative]
    out = [0] * len(factors)
    if not anchors:
        return tuple(out)
    anchors.sort(key=lambda i: factors[i].radius)
    left, right = anchors[0], anchors[-1]
    lo, hi = factors[left].radius, factors[right].radius
    if lo == hi:
        cap = mult[left] if mult[left] % 2 else mult[left] - 1
        for i in chosen:
            if factors[i].radius == lo:
                out[i] = min(mult[i], cap)
    else:
        for i in chosen:
            r = factors[i].radius
            if lo < r < hi:
                out[i] = mult[i]
            elif r == lo:
                out[i] = min(mult[i], mult[left])
            elif r == hi:
                out[i] = min(mult[i], mult[right])
    return tuple(out)


def closed_core(factors: tuple[Factor, ...], mult: tuple[int, ...]) -> tuple[int, ...]:
    if not any(m and (f.negative or f.unit == "-") for f, m in zip(factors, mult)):
        return (0,) * len(factors)
    sides = [side_core(factors, mult, s) for s in (True, False)]
    return tuple(int(m > 0) if f.unit in ("+", "-") else
                 max(s[i] for s in sides)
                 for i, (f, m) in enumerate(zip(factors, mult)))


def audit_atlas(name: str, factors: tuple[Factor, ...], caps: tuple[int, ...]) -> dict:
    inputs = divisors = feasible = two_witness = 0
    for p in product(*(range(k + 1) for k in caps)):
        inputs += 1
        brute = [0] * len(factors)
        found = False
        for d in product(*(range(k + 1) for k in p)):
            divisors += 1
            if is_minimal_spectrum(factors, d):
                found = True
                brute = [max(a, b) for a, b in zip(brute, d)]
        expected = closed_core(factors, p)
        check(tuple(brute) == expected, f"{name}: mismatch at {p}")
        feasible += int(found)
        sides = [side_core(factors, p, s) for s in (True, False)]
        count = sum(any(s) for s in sides)
        if found:
            check(any(expected), "A nonempty solution class needs nonconstant core")
            if count:
                for side in sides:
                    if any(side):
                        branch = tuple(expected[i] if f.unit else side[i]
                                       for i, f in enumerate(factors))
                        check(is_minimal_spectrum(factors, branch), "Branch not attained")
            else:
                check(is_minimal_spectrum(factors, expected), "Involution core invalid")
            check(is_minimal_spectrum(factors, expected) == (count <= 1),
                  "One-/two-witness criterion failed")
        if count == 2:
            two_witness += 1
    return dict(name=name, input_profiles=inputs, divisors_tested=divisors,
                feasible_profiles=feasible, two_witness_profiles=two_witness,
                result="PASS")


def mul(p: list[F], q: list[F]) -> list[F]:
    r = [F(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] += a * b
    return r


def from_roots(roots: list[F]) -> list[F]:
    p = [F(1)]
    for r in roots:
        p = mul(p, [-r, F(1)])
    return p


def value(p: list[F], x: F) -> F:
    result = F(0)
    for a in reversed(p):
        result = result * x + a
    return result


def determinant(matrix: list[list[F]]) -> F:
    a = [row[:] for row in matrix]
    n, ans = len(a), F(1)
    for k in range(n):
        pivot = next((j for j in range(k, n) if a[j][k]), None)
        if pivot is None:
            return F(0)
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            ans = -ans
        v = a[k][k]
        ans *= v
        for j in range(k + 1, n):
            ratio = a[j][k] / v
            for i in range(k + 1, n):
                a[j][i] -= ratio * a[k][i]
            a[j][k] = F(0)
    return ans


def example_checks() -> dict:
    # Cubic nonreal spectrum: exact cos(2*pi*n/3) at integer n.
    def orbit(n: int) -> F:
        cos = F(1) if n % 3 == 0 else F(-1, 2)
        return F(-2) ** n * (1 + cos / 100)
    for n in range(-15, 16):
        check(orbit(n + 3) + 8 * orbit(n) == 0, "Cubic recurrence")
    cubic_det = determinant([[orbit(i + j) for j in range(3)] for i in range(3)])
    check(cubic_det != 0, "Cubic minimum degree must be three")
    # Polynomial-conjugate smooth example: H=t+t^2/4+t^3, a=-2.
    h = [F(0), F(1), F(1, 4), F(1)]
    mu = from_roots([F(-2), F(4), F(-8)])
    for k in range(4):
        check(sum(mu[j] * h[k] * F(-2) ** (j * k)
                  for j in range(len(mu))) == 0, "Polynomial identity")
    def smooth_orbit(n: int) -> F:
        return value(h, F(-2) ** n)
    smooth_det = determinant([[smooth_orbit(i + j) for j in range(3)] for i in range(3)])
    check(smooth_det != 0, "Smooth cubic minimum degree must be three")
    check(F(1) - F(1, 48) == F(47, 48), "Derivative square completion")
    # Plateau with b=1, r=2: mu=(z+1)(z+2).
    def plateau(x: F) -> F:
        if abs(x) <= 1:
            return -x
        return -2 * x + (1 if x > 0 else -1)
    point_count = 0
    for j in range(-200, 201):
        x = F(j, 20)
        check(plateau(plateau(x)) + 3 * plateau(x) + 2 * x == 0,
              "Plateau recurrence")
        point_count += 1
    check(plateau(F(1, 2)) == F(-1, 2), "Plateau orbit")
    check(plateau(F(2)) == F(-3), "Exterior orbit")
    # Smooth witness atlas: slopes in (2,3) have no higher power in that interval.
    slopes = [F(2) + F(j, 9) for j in range(1, 9)]
    check(all(F(2) < r < F(3) for r in slopes), "Cluster interval")
    check(min(slopes) ** 2 > max(slopes), "Higher-power separation")
    return dict(cubic_orbit=[str(orbit(n)) for n in range(6)],
                cubic_hankel_determinant=str(cubic_det),
                smooth_minimal_polynomial_ascending=[str(c) for c in mu],
                smooth_hankel_determinant=str(smooth_det),
                plateau_rational_points=point_count,
                clustered_slope_witness_example=len(slopes), result="PASS")



def audit_smooth_atlas() -> dict:
    """Independent subset enumeration for the squarefree smooth core."""
    roots = (F(-1, 8), F(-1, 2), F(1, 4), F(-2), F(4),
             F(-8), F(-32), F(16), F(1), F(-1))
    lo, hi = min(map(abs, roots)), max(map(abs, roots))
    powers: dict[F, dict[F, int]] = {}
    for a in roots:
        if a >= 0 or a == -1:
            continue
        table: dict[F, int] = {}
        value_a, k = a, 1
        while lo <= abs(value_a) <= hi:
            table[value_a] = k
            value_a *= a
            k += 1
        powers[a] = table
    subsets = [{r for j, r in enumerate(roots) if mask & (1 << j)}
               for mask in range(1 << len(roots))]

    def admissible(s: set[F]) -> bool:
        nonunit = s - {F(1), F(-1)}
        if not nonunit:
            return F(-1) in s
        if F(-1) in s:
            return False
        for a in nonunit:
            if a in powers and nonunit <= powers[a].keys():
                if max(powers[a][r] for r in nonunit) % 2:
                    return True
        return False

    valid = [admissible(s) for s in subsets]
    tests = 0
    for mask, p in enumerate(subsets):
        formula: set[F] = set()
        unit = {F(1)} if F(1) in p else set()
        if F(-1) in p:
            formula |= unit | {F(-1)}
        for a in p:
            if a not in powers:
                continue
            present = {r: k for r, k in powers[a].items() if r in p}
            odd_max = max(k for k in present.values() if k % 2)
            formula |= unit | {r for r, k in present.items() if k <= odd_max}
        brute: set[F] = set()
        sub = mask
        while True:
            tests += 1
            if valid[sub]:
                brute |= subsets[sub]
            if sub == 0:
                break
            sub = (sub - 1) & mask
        check(brute == formula, f"Smooth core mismatch at {p}")
    return dict(input_profiles=len(subsets), divisor_tests=tests,
                admissible_minimal_profiles=sum(valid), result="PASS")


def main() -> None:
    if len(sys.argv) > 2:
        raise SystemExit("Usage: python code/verify.py [output.json]")
    atlases = [
        ("squarefree two-sided atlas", (
            Factor("-1/3", F(1, 3), True), Factor("-1/2", F(1, 2), True),
            Factor("+-i/2", F(1, 2)), Factor("-2", F(2), True),
            Factor("-3", F(3), True), Factor("+2", F(2)),
            Factor("+-5i/2", F(5, 2)), Factor("+1", F(1), unit="+"),
            Factor("-1", F(1), unit="-"), Factor("+-i", F(1), unit="other")
        ), (1,) * 10),
        ("one-circle multiplicities", (
            Factor("-2", F(2), True), Factor("+2", F(2)), Factor("+-2i", F(2)),
            Factor("+1", F(1), unit="+"), Factor("-1", F(1), unit="-")
        ), (4, 4, 4, 2, 2)),
        ("interior and boundary multiplicities", (
            Factor("-2", F(2), True), Factor("-4", F(4), True),
            Factor("+-3i", F(3)), Factor("+4", F(4))
        ), (3, 3, 5, 2)),
        ("two-sided multiplicities", (
            Factor("-1/2", F(1, 2), True), Factor("-2", F(2), True),
            Factor("+1/2", F(1, 2)), Factor("+-2i", F(2))
        ), (3, 3, 3, 3)),
    ]
    results = [audit_atlas(*atlas) for atlas in atlases]
    data = dict(atlases=results, smooth_atlas=audit_smooth_atlas(),
                examples=example_checks(),
                continuous_total_profiles=sum(r["input_profiles"] for r in results),
                continuous_total_divisor_tests=sum(r["divisors_tested"] for r in results),
                scope="Finite exact consistency checks; not proof-assistant verification.")
    target = (Path(sys.argv[1]) if len(sys.argv) == 2 else
              Path(__file__).resolve().parents[1] / "results" / "verification.json")
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(data, indent=2))


if __name__ == "__main__":
    main()
