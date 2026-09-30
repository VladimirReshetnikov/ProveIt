#!/usr/bin/env python3
"""Exact finite checks for Affine Residues and Tropical Mixed Volumes.

Python 3.10+, standard library only. No numerical approximations or CAS.
The ordered coefficient ring is Q[eta^+-1, epsilon^+-1], with exponent
(a,b) ordered lexicographically: eta is smaller than every epsilon power.
This audits examples and many finite instances, not the universal proofs.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as F
from functools import cmp_to_key
from itertools import combinations, product
import json
from pathlib import Path
import random
from typing import Iterable

Exp = tuple[int, int]


@dataclass(frozen=True)
class Laurent:
    terms: tuple[tuple[Exp, F], ...] = ()

    @staticmethod
    def make(terms: Iterable[tuple[Exp, F | int]]) -> Laurent:
        out: dict[Exp, F] = {}
        for exponent, coefficient in terms:
            out[exponent] = out.get(exponent, F(0)) + F(coefficient)
        return Laurent(tuple(sorted((e, c) for e, c in out.items() if c)))

    @staticmethod
    def scalar(x: F | int) -> Laurent:
        return Laurent.make([((0, 0), F(x))])

    @staticmethod
    def coerce(x: Laurent | F | int) -> Laurent:
        return x if isinstance(x, Laurent) else Laurent.scalar(x)

    def __bool__(self) -> bool:
        return bool(self.terms)

    def __add__(self, other: Laurent | F | int) -> Laurent:
        return Laurent.make(self.terms + self.coerce(other).terms)

    __radd__ = __add__

    def __neg__(self) -> Laurent:
        return Laurent(tuple((e, -c) for e, c in self.terms))

    def __sub__(self, other: Laurent | F | int) -> Laurent:
        return self + (-self.coerce(other))

    def __rsub__(self, other: Laurent | F | int) -> Laurent:
        return self.coerce(other) - self

    def __mul__(self, other: Laurent | F | int) -> Laurent:
        other = self.coerce(other)
        return Laurent.make(
            (((a + c, b + d), x * y)
             for ((a, b), x) in self.terms for ((c, d), y) in other.terms)
        )

    __rmul__ = __mul__

    def __truediv__(self, other: F | int) -> Laurent:
        other = F(other)
        if not other:
            raise ZeroDivisionError("Only division by a nonzero rational is supported")
        return Laurent(tuple((e, c / other) for e, c in self.terms))

    def sign(self) -> int:
        return 0 if not self else (1 if self.terms[0][1] > 0 else -1)

    def __abs__(self) -> Laurent:
        return self if self.sign() >= 0 else -self

    def __lt__(self, other: Laurent | F | int) -> bool:
        return (self - other).sign() < 0

    def __le__(self, other: Laurent | F | int) -> bool:
        return (self - other).sign() <= 0

    def __gt__(self, other: Laurent | F | int) -> bool:
        return (self - other).sign() > 0

    def __ge__(self, other: Laurent | F | int) -> bool:
        return (self - other).sign() >= 0

    def valuation(self) -> Exp | None:
        return self.terms[0][0] if self else None  # None represents +infinity.

    def leading(self) -> F:
        if not self:
            raise ValueError("Zero has no leading coefficient")
        return self.terms[0][1]

    def data(self) -> list[dict]:
        return [{"exponent": list(e), "coefficient": str(c)} for e, c in self.terms]


ZERO = Laurent()
ONE = Laurent.scalar(1)
EPS = Laurent.make([((0, 1), 1)])
ETA = Laurent.make([((1, 0), 1)])
ORIGIN = (ZERO, ZERO)
Point = tuple[Laurent, Laurent]


def point(x: Laurent | F | int, y: Laurent | F | int) -> Point:
    return Laurent.coerce(x), Laurent.coerce(y)


def plus(a: Point, b: Point) -> Point:
    return a[0] + b[0], a[1] + b[1]


def minus(a: Point, b: Point) -> Point:
    return a[0] - b[0], a[1] - b[1]


def det(a: Point, b: Point) -> Laurent:
    return a[0] * b[1] - a[1] * b[0]


def cmp_point(a: Point, b: Point) -> int:
    for x, y in zip(a, b):
        s = (x - y).sign()
        if s:
            return s
    return 0


def hull(points: Iterable[Point]) -> list[Point]:
    pts = sorted(set(points), key=cmp_to_key(cmp_point))
    if len(pts) <= 1:
        return pts

    def half(seq: Iterable[Point]) -> list[Point]:
        out: list[Point] = []
        for p in seq:
            while len(out) >= 2 and det(minus(out[-1], out[-2]), minus(p, out[-2])) <= 0:
                out.pop()
            out.append(p)
        return out

    return half(pts)[:-1] + half(reversed(pts))[:-1]


def area(p: list[Point]) -> Laurent:
    if len(p) < 3:
        return ZERO
    return abs(sum((det(p[i], p[(i + 1) % len(p)]) for i in range(len(p))), ZERO)) / 2


def minkowski(p: list[Point], q: list[Point]) -> list[Point]:
    return hull(plus(a, b) for a in p for b in q)


def mixed(p: list[Point], q: list[Point]) -> Laurent:
    return (area(minkowski(p, q)) - area(p) - area(q)) / 2


def segment(u: Point) -> list[Point]:
    return hull([ORIGIN, u])


def zonotope(gens: Iterable[Point]) -> list[Point]:
    p = [ORIGIN]
    for u in gens:
        p = minkowski(p, segment(u))
    return p


def max_basis(p: list[Point]) -> tuple[Point, list[Point], Laurent]:
    if not p:
        raise ValueError("Only nonempty polytopes are supported")
    if len(p) == 1:
        return p[0], [], ZERO
    if len(p) == 2:
        return p[0], [minus(p[1], p[0])], ZERO
    best = ZERO
    ans: tuple[Point, list[Point], Laurent] | None = None
    for a, b, c in combinations(p, 3):
        u, v = minus(b, a), minus(c, a)
        d = det(u, v)
        if abs(d) > best:
            best = abs(d)
            ans = (a, [u, v] if d > 0 else [v, u], best)
    if ans is None:
        raise AssertionError("Convex hull did not remove collinear intermediate points")
    return ans


def standard_ratio(numerator: Laurent, denominator: Laurent) -> F:
    if not denominator:
        raise ZeroDivisionError("A scale denominator must be nonzero")
    if not numerator:
        return F(0)
    a, b = numerator.valuation(), denominator.valuation()
    assert a is not None and b is not None
    if a < b:
        raise ValueError("The ratio is infinite and has no standard part")
    return numerator.leading() / denominator.leading() if a == b else F(0)


def audit_residue(p: list[Point]) -> None:
    origin, basis, scale = max_basis(p)
    if len(basis) != 2:
        return
    u, v = basis
    shadow: list[Point] = []
    for a in p:
        w = minus(a, origin)
        c1, c2 = det(w, v), det(u, w)
        assert abs(c1) <= scale and abs(c2) <= scale
        shadow.append(point(standard_ratio(c1, scale), standard_ratio(c2, scale)))
    real_area = area(hull(shadow))
    assert real_area > 0
    assert real_area == Laurent.scalar(standard_ratio(area(p), scale))
    assert area(p).valuation() == scale.valuation()
    assert scale / 2 <= area(p) <= 4 * scale


def audit_pair(p: list[Point], q: list[Point]) -> dict:
    _, u, _ = max_basis(p)
    _, v, _ = max_basis(q)
    mv = mixed(p, q)
    determinants = [abs(det(a, b)) for a in u for b in v]
    maximum = max(determinants, default=ZERO)
    z_mv = sum(determinants, ZERO) / 2
    assert mv >= 0
    assert mv.valuation() == maximum.valuation()
    assert maximum / 2 <= mv
    assert mv <= 4 * len(u) * len(v) * maximum / 2
    if u and v:
        assert z_mv / (len(u) * len(v)) <= mv <= 4 * z_mv
    else:
        assert not mv
    # Check the formula with ALL vertex differences, not merely the selected bases.
    du = [minus(a, b) for a, b in combinations(p, 2)]
    dv = [minus(a, b) for a, b in combinations(q, 2)]
    all_max = max((abs(det(a, b)) for a in du for b in dv), default=ZERO)
    assert all_max.valuation() == mv.valuation()
    audit_residue(p)
    audit_residue(q)
    return {"mixed_area": mv.data(), "valuation": mv.valuation(),
            "selected_determinants": len(determinants)}


def mat_apply(matrix: tuple[Point, Point], p: Point) -> Point:
    a, b = matrix  # Columns, not rows.
    return a[0] * p[0] + b[0] * p[1], a[1] * p[0] + b[1] * p[1]


def transformed(p: list[Point], matrix: tuple[Point, Point], shift: Point = ORIGIN) -> list[Point]:
    return hull(plus(mat_apply(matrix, a), shift) for a in p)


def same_lattice(p: list[Point], q: list[Point]) -> bool:
    _, bp, dp = max_basis(p)
    _, bq, dq = max_basis(q)
    if len(bp) != 2 or len(bq) != 2:
        raise ValueError("This comparison is for full-dimensional polygons")

    def contained(gens: list[Point], basis: list[Point], scale: Laurent) -> bool:
        for u in gens:
            for n in (det(u, basis[1]), det(basis[0], u)):
                if n and n.valuation() < scale.valuation():
                    return False
        return True

    return contained(bq, bp, dp) and contained(bp, bq, dq)


def probe_test(p: list[Point], q: list[Point]) -> bool:
    _, bp, _ = max_basis(p)
    return (area(p).valuation() == area(q).valuation()
            and all(mixed(p, segment(u)).valuation() == mixed(q, segment(u)).valuation()
                    for u in bp))


def random_polygon(rng: random.Random) -> list[Point]:
    # Begin with a guaranteed full-dimensional rational cloud, then deform it.
    raw = [point(0, 0), point(1, 0), point(0, 1)]
    raw += [point(rng.randint(-3, 3), rng.randint(-3, 3))
            for _ in range(rng.randint(0, 5))]
    a = Laurent.make([((rng.randint(-1, 1), rng.randint(-2, 2)), 1)])
    b = Laurent.make([((rng.randint(-1, 1), rng.randint(-2, 2)), 1)])
    shear = rng.randint(-2, 2) + rng.randint(-1, 1) * EPS + rng.randint(-1, 1) * ETA
    matrix = (point(a, a * shear), point(0, b))
    shift = point(rng.randint(-2, 2) + ETA, rng.randint(-2, 2) - EPS)
    p = transformed(hull(raw), matrix, shift)
    # Occasionally add a tiny perturbation that can change the actual face lattice.
    if rng.randrange(3) == 0:
        p = hull(p + [plus(p[0], point(ETA * EPS, -ETA * EPS * EPS))])
    return p


def compression_audit(polys: list[Laurent]) -> dict:
    # M a + b is positive on every lex-positive difference in these supports.
    exps = sorted({e for f in polys for e, _ in f.terms})
    differences = [(b[0] - a[0], b[1] - a[1]) for a, b in combinations(exps, 2)]
    M = 1 + max((abs(b) for a, b in differences), default=0)
    assert all(M * a + b > 0 for a, b in differences)
    transformed_polys: list[list[tuple[int, F]]] = []
    threshold = F(1)
    for f in polys:
        terms = [(M * a + b, c) for (a, b), c in f.terms]
        assert terms == sorted(terms)
        transformed_polys.append(terms)
        if len(terms) > 1:
            tail = sum((abs(c) for _, c in terms[1:]), F(0))
            threshold = min(threshold, abs(terms[0][1]) / (2 * tail))
    s = threshold / 2
    for f, terms in zip(polys, transformed_polys):
        if not terms:
            continue
        # Remove the lowest exponent to avoid enormous negative powers.
        e0 = terms[0][0]
        value = sum((c * s ** (e - e0) for e, c in terms), F(0))
        assert (1 if value > 0 else -1 if value < 0 else 0) == f.sign()
    return {"polynomials": len(polys), "strict_order_constraints": len(differences),
            "lambda_eta": M, "lambda_epsilon": 1,
            "rational_specialization": str(s)}


def value_add(a: Exp, b: Exp) -> Exp:
    return a[0] + b[0], a[1] + b[1]


def select_inner_segments(polygons: list[list[Point]], rng: random.Random) -> int:
    """Find and audit a simultaneous generic rational choice in the proved grid.

    Random search is used for convenience; exhaustive enumeration of this same
    finite grid is the terminating algorithm in the article, not this routine.
    """
    m = len(polygons)
    bases = [max_basis(p)[1] for p in polygons]
    target = {(i, j): mixed(polygons[i], polygons[j]).valuation()
              for i, j in combinations(range(m), 2)}
    # In dimension two H=choose(m-1,1)=m-1; grid has m points.
    for trial in range(1, 2001):
        vectors = []
        for basis in bases:
            coeffs = [F(rng.randint(1, m), len(basis) * (m + 1)) for _ in basis]
            assert all(c > 0 for c in coeffs) and sum(coeffs) < 1
            vectors.append(tuple(sum((c * u[k] for c, u in zip(coeffs, basis)), ZERO)
                                 for k in range(2)))
        if all(det(vectors[i], vectors[j]).valuation() == v for (i, j), v in target.items()):
            return trial
    raise AssertionError("Random generic selection exceeded its audit budget")


def audit_exchange(polygons: list[list[Point]]) -> int:
    """Audit the full degree-two, three-color M-convex exchange axiom."""
    n = len(polygons)
    profiles: dict[tuple[int, ...], Exp] = {}
    for i in range(n):
        for j in range(i, n):
            alpha = tuple(int(k == i) + int(k == j) for k in range(n))
            v = mixed(polygons[i], polygons[j]).valuation()
            assert v is not None  # Test families in this routine have full dimension.
            profiles[alpha] = v
    checks = 0
    for x, y in product(profiles, repeat=2):
        for i in range(n):
            if x[i] <= y[i]:
                continue
            witnesses = []
            for j in range(n):
                if x[j] >= y[j]:
                    continue
                xp, yp = list(x), list(y)
                xp[i] -= 1
                xp[j] += 1
                yp[i] += 1
                yp[j] -= 1
                witnesses.append(value_add(profiles[tuple(xp)], profiles[tuple(yp)]))
            assert witnesses and min(witnesses) <= value_add(profiles[x], profiles[y])
            checks += 1
    return checks


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pairs", type=int, default=160)
    parser.add_argument("--seed", type=int, default=20260930)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("verification.json"))
    args = parser.parse_args()
    if args.pairs < 1:
        parser.error("--pairs must be positive")
    rng = random.Random(args.seed)
    examples: dict[str, dict] = {}
    thin = hull([point(0, 0), point(1, 0), point(0, EPS)])
    audit_residue(thin)
    assert area(thin) == EPS / 2
    examples["thin_triangle"] = {"area": area(thin).data(), "affine_residue_area": "1/2"}
    cancellation = det(point(1, 1), point(1, 1 + ETA))
    assert cancellation == ETA
    examples["cancellation"] = {"determinant": cancellation.data()}
    p = zonotope([point(1, 0), point(0, EPS)])
    q = zonotope([point(1, EPS), point(0, ETA)])
    q_perp = zonotope([point(ETA, 0), point(0, 1)])
    assert area(p) == EPS and area(q) == area(q_perp) == ETA
    assert mixed(p, q) == EPS + ETA / 2
    assert mixed(p, q_perp) == (1 + EPS * ETA) / 2
    examples["aligned_rank_two"] = audit_pair(p, q)
    examples["transverse_rank_two"] = audit_pair(p, q_perp)
    square = hull([point(0, 0), point(1, 0), point(1, 1), point(0, 1)])
    pentagon = hull(square + [point(-EPS, F(1, 2))])
    assert len(pentagon) == 5
    audit_residue(pentagon)
    assert same_lattice(square, pentagon)
    examples["pentagon_with_square_residue"] = {"vertices": len(pentagon), "area": area(pentagon).data()}
    # Lower-dimensional and zero mixed-volume cases.
    degenerate_pairs = [([ORIGIN], square), (segment(point(1, 0)), segment(point(1, 0))),
                        (segment(point(1, 0)), segment(point(0, ETA))),
                        (segment(point(1, 0)), thin)]
    for a, b in degenerate_pairs:
        audit_pair(a, b)
    probe_checks = 0
    affine_checks = 0
    random_max_vertices = 0
    for _ in range(args.pairs):
        a, b = random_polygon(rng), random_polygon(rng)
        audit_pair(a, b)
        random_max_vertices = max(random_max_vertices, len(a), len(b))
        assert same_lattice(a, b) == probe_test(a, b)
        probe_checks += 1
        # A homothetic translate has exactly the same O-lattice.
        c = hull(plus(point(ETA, -EPS), (2 * x, 2 * y)) for x, y in a)
        assert same_lattice(a, c) and probe_test(a, c)
        probe_checks += 1
        if affine_checks < 24:
            matrix = (point(EPS, ETA), point(0, 1 + EPS))
            da = abs(det(*matrix))
            ta = transformed(a, matrix)
            tb = transformed(b, matrix, point(1, ETA))
            assert mixed(ta, tb) == da * mixed(a, b)
            affine_checks += 1
    generic_trials = []
    plucker_checks = 0
    for _ in range(20):
        family = [random_polygon(rng) for _ in range(4)]
        generic_trials.append(select_inner_segments(family, rng))
        v = {(i, j): mixed(family[i], family[j]).valuation()
             for i, j in combinations(range(4), 2)}
        sums = [value_add(v[0, 1], v[2, 3]), value_add(v[0, 2], v[1, 3]),
                value_add(v[0, 3], v[1, 2])]
        assert sums.count(min(sums)) >= 2
        plucker_checks += 1
    clone_trials = []
    exchange_checks = 0
    for _ in range(12):
        family = [random_polygon(rng) for _ in range(3)]
        clone_trials.append(select_inner_segments([p for p in family for _ in range(2)], rng))
        exchange_checks += audit_exchange(family)
    # Rank-two certificates, including high-order cancellation and signed differences.
    polys = [cancellation, EPS + ETA / 2, (1 + EPS * ETA) / 2,
             1 - EPS, EPS * EPS - ETA,
             ETA - EPS * ETA, 3 * ETA - 2 * ETA * EPS + ETA * ETA,
             det(point(1 + EPS, 1), point(1, 1 - EPS)), ZERO]
    compression = compression_audit(polys)
    output = {
        "status": "all assertions passed", "arithmetic": "exact rational sparse Laurent polynomials",
        "exponent_order": "Z^2 lexicographic, eta=(1,0), epsilon=(0,1)",
        "seed": args.seed, "random_full_dimensional_pairs": args.pairs,
        "degenerate_pairs": len(degenerate_pairs), "explicit_mixed_pairs": 2,
        "random_pair_max_vertex_count": random_max_vertices,
        "random_residue_audits": 2 * args.pairs,
        "probe_equivalence_checks": probe_checks,
        "affine_covariance_checks": affine_checks,
        "generic_four_body_families": len(generic_trials),
        "generic_selection_trials": generic_trials,
        "tropical_plucker_checks": plucker_checks,
        "six_clone_families": len(clone_trials),
        "clone_selection_trials": clone_trials,
        "M_convex_exchange_checks": exchange_checks,
        "examples": examples, "finite_compression": compression,
        "scope": "Finite-instance audits only; no claim of a Lean formalization or exhaustive proof search."
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in output.items() if k != "examples"}, indent=2))


if __name__ == "__main__":
    main()
