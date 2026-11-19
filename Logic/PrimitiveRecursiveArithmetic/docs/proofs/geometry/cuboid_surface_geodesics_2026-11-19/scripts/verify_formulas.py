#!/usr/bin/env python3
"""Independent symbolic and numerical checks for the cuboid formulas.

This is validation, not a formal proof.  It is intentionally separate from the
calculator and from the Lean blueprint.
"""

from __future__ import annotations

import math
import random
import sys
from pathlib import Path

import sympy as sp

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

from cuboid_surface import (  # noqa: E402
    antipodal_distance_from_five_unfoldings,
    fixed_vertex_farthest,
    intrinsic_diameter,
)


def symbolic_checks() -> list[str]:
    A, B, C, x, y, ell, H = sp.symbols(
        "A B C x y ell H", positive=True, real=True
    )
    L0 = (A + B) ** 2 + C**2

    # Fixed-vertex calculation.
    delta = A * (C - B) / (2 * C)
    px, py = A - delta, B - delta
    s1 = (px + C) ** 2 + py**2
    s2 = (px - A - C) ** 2 + (py + A) ** 2
    s3 = px**2 + (py + C) ** 2
    s4 = (px + B) ** 2 + (py - B - C) ** 2
    R2 = (B**2 + C**2) * (A**2 + 2 * A * C + 2 * C**2) / (2 * C**2)
    assert sp.simplify(s1 - R2) == 0
    assert sp.simplify(s2 - R2) == 0
    assert sp.simplify(s4 - R2) == 0
    assert sp.simplify(s3 - R2 - 2 * C * (B - A)) == 0
    K = 2 * C**2 - 2 * B * C - A * C - A * B
    assert sp.simplify(R2 - L0 - A * (C - B) * K / (2 * C**2)) == 0

    t123 = A * (A + C) / (2 * C)
    RA2 = (A**2 + C**2) * (A**2 + 2 * A * C + 2 * C**2) / (2 * C**2)
    assert sp.simplify((t123 + C) ** 2 + t123**2 - RA2) == 0
    assert sp.simplify(
        R2 - RA2 - (B - A) * (A + B) * (A**2 + 2 * A * C + 2 * C**2) / (2 * C**2)
    ) == 0

    # Five-unfolding algebra.
    d1 = (A + C) ** 2 + (B - 2 * y) ** 2
    d2 = (B + C) ** 2 + (A - 2 * x) ** 2
    d3 = (C + x + y) ** 2 + (A + B - x - y) ** 2
    d4 = (A + B) ** 2 + (C + 2 * y) ** 2
    d5 = (A + B) ** 2 + (C + 2 * x) ** 2

    q1 = (x + (C - A) / 2) * (y + (C - B) / 2) - (C**2 - A * B) / 4
    q2 = (y - B / 2) ** 2 - (x - A / 2) ** 2 - (B - A) * (A + B + 2 * C) / 4
    assert sp.simplify((2 * d3 - d1 - d2) / 8 - q1) == 0
    assert sp.simplify((d1 - d2) / 4 - q2) == 0

    threshold_x = B * (C - A) / (2 * (A + C))
    threshold_y = A * (C - B) / (2 * (B + C))
    assert sp.simplify(d2 - d5 + 4 * (A + C) * (x - threshold_x)) == 0
    assert sp.simplify(d1 - d4 + 4 * (B + C) * (y - threshold_y)) == 0
    assert sp.simplify(d3 - L0 - 2 * (x + y) * (C - A - B + x + y)) == 0

    # Boundary candidate. Reduce modulo H^2 = the defining radicand.
    tau = (B + C - H) / 2
    boundary_D2 = B**2 + 3 * C**2 + 2 * B * (A + C) - 2 * C * H
    relation = H**2 - ((B + C) ** 2 - 2 * A * (C - B) - A**2)
    expr1 = sp.expand(d1.subs({x: A / 2, y: tau}) - boundary_D2)
    expr3 = sp.expand(d3.subs({x: A / 2, y: tau}) - boundary_D2)
    _, rem1 = sp.div(expr1, relation, H)
    _, rem3 = sp.div(expr3, relation, H)
    assert sp.simplify(rem1) == 0
    assert sp.simplify(rem3) == 0

    # Interior coordinate reconstruction from ell.
    u, v = sp.symbols("u v", nonnegative=True, real=True)
    xi, yi = (A - u) / 2, (B - v) / 2
    assert sp.expand(d2.subs(x, xi) - ((B + C) ** 2 + u**2)) == 0
    assert sp.expand(d1.subs(y, yi) - ((A + C) ** 2 + v**2)) == 0
    d3_uv = sp.expand(d3.subs({x: xi, y: yi}))
    assert sp.factor(2 * d3_uv - (A + B + C) ** 2 - (C - u - v) ** 2) == 0

    return [
        "fixed-vertex triple-source equalities",
        "fixed gap factorization R^2-L0^2",
        "all five unfolding identities",
        "q1/q2 hyperbola identities",
        "d4/d5 nonbinding gap identities",
        "boundary-candidate identities modulo H^2",
        "interior root-coordinate reconstruction",
    ]


def top_face_distance_sq(A: float, B: float, C: float, p: float, q: float) -> float:
    sources = ((-C, 0.0), (A + C, -A), (0.0, -C), (-B, B + C))
    return min((p - sx) ** 2 + (q - sy) ** 2 for sx, sy in sources)


def numerical_checks(seed: int = 20261119) -> tuple[int, int, float, float]:
    rng = random.Random(seed)
    fixed_count = 0
    diameter_count = 0
    fixed_worst = 0.0
    diameter_worst = 0.0

    for _ in range(120):
        raw = [10 ** rng.uniform(-0.5, 0.8) for _ in range(3)]
        A, B, C = sorted(raw)

        fixed = fixed_vertex_farthest((A, B, C))
        claimed_sq = fixed.distance**2
        # Dense deterministic grid over the only face that can exceed L0.
        sampled = 0.0
        n = 90
        for i in range(n + 1):
            p = A * i / n
            for j in range(n + 1):
                q = B * j / n
                sampled = max(sampled, top_face_distance_sq(A, B, C, p, q))
        violation = sampled - claimed_sq
        fixed_worst = max(fixed_worst, violation)
        if violation > 2.0e-9 * max(1.0, claimed_sq):
            raise AssertionError(("fixed grid violation", A, B, C, violation, fixed))
        fixed_count += 1

        diam = intrinsic_diameter((A, B, C))
        claimed = diam.distance
        sampled_d = 0.0
        n2 = 100
        for i in range(n2 + 1):
            xx = (A / 2.0) * i / n2
            for j in range(n2 + 1):
                yy = (B / 2.0) * j / n2
                value, _ = antipodal_distance_from_five_unfoldings(A, B, C, xx, yy)
                sampled_d = max(sampled_d, value)
        violation_d = sampled_d - claimed
        diameter_worst = max(diameter_worst, violation_d)
        if violation_d > 3.0e-9 * max(1.0, claimed):
            raise AssertionError(("diameter grid violation", A, B, C, violation_d, diam))

        # Verify the returned sorted pair against the five unfolding formula.
        perm = diam.sorting_permutation
        p_sorted = tuple(diam.endpoint_P[i] for i in perm)
        q_sorted = tuple(diam.endpoint_Q[i] for i in perm)
        assert all(abs(q_sorted[k] - ((A, B, C)[k] - p_sorted[k])) < 2e-9 for k in range(3))
        exact_at_pair, lengths = antipodal_distance_from_five_unfoldings(
            A, B, C, p_sorted[0], p_sorted[1]
        )
        if abs(exact_at_pair - claimed) > 5.0e-9 * max(1.0, claimed):
            raise AssertionError(("returned pair mismatch", A, B, C, exact_at_pair, claimed, lengths))
        diameter_count += 1

    return fixed_count, diameter_count, fixed_worst, diameter_worst


def main() -> None:
    checks = symbolic_checks()
    fixed_count, diameter_count, fw, dw = numerical_checks()
    print("SYMBOLIC CHECKS: PASS")
    for item in checks:
        print(f"  - {item}")
    print()
    print("NUMERICAL GRID CHECKS: PASS")
    print(f"  fixed-vertex random boxes: {fixed_count}")
    print(f"  diameter random boxes:     {diameter_count}")
    print(f"  largest sampled fixed excess over claimed value:    {fw:.3e}")
    print(f"  largest sampled diameter excess over claimed value: {dw:.3e}")
    print()
    print("These checks support the algebra and implementation; they are not formal proofs.")


if __name__ == "__main__":
    main()
