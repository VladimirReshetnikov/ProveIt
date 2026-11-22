#!/usr/bin/env python3
"""Reproduce exact validation receipts. Tests complement the report's proofs.

Run: python3 code/validate.py
Outputs are written under validation/ relative to this package.
Only the Python standard library is required.
"""

from __future__ import annotations

import csv
import hashlib
import json
import platform
import random
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from pathlib import Path

from stokes_reference import (
    Poly, boundary_of_chain, boundary_sum, bridge_bound, cubical_boundary,
    curved_closed_sums, curved_example, eps, grid, polynomial_family,
    rounded, telescope_sum, volume_sum,
)


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "validation"


def arbitrary_table_tests() -> list[dict]:
    records = []
    for k in range(1, 5):
        for cells in (1, 2, 3):
            for seed in (17, 29, 101):
                generator = random.Random(seed + 1000 * k + 100 * cells)
                points = [tuple(Q(j, cells) for j in index) for index in product(range(cells + 1), repeat=k)]
                tables = [{point: Q(generator.randint(-100, 100), generator.randint(1, 13)) for point in points} for _ in range(k)]
                coefficients = [(lambda point, table=table: table[point]) for table in tables]
                T = telescope_sum(coefficients, cells)
                B = boundary_sum(coefficients, cells)
                assert T == B
                records.append({"dimension": k, "N": cells, "seed": seed, "T": str(T), "B": str(B), "equal": True})
    return records


def boundary_square_tests() -> list[dict]:
    records = []
    for k in range(2, 7):
        first = cubical_boundary((None,) * k)
        second = boundary_of_chain(first)
        assert len(first) == 2 * k
        assert len(second) == 4 * k * (k - 1) // 2
        assert all(value == 0 for value in second.values())
        records.append({"dimension": k, "first_faces": len(first), "codimension_two_faces": len(second), "all_coefficients_zero": True})
    return records


def noisy_case(coefficients: list[Poly], derivatives: list[Poly], cells: int, t: int, p: int, label: str) -> dict:
    k = len(coefficients)
    h = Q(1, cells)
    A = [lru_cache(None)(rounded(a, p)) for a in coefficients]
    G = [lru_cache(None)(rounded(g, p)) for g in derivatives]
    max_local_error = Q(0)
    for point in grid(k, cells):
        for axis, (a, g) in enumerate(zip(coefficients, derivatives)):
            upper = point[:axis] + (point[axis] + h,) + point[axis + 1 :]
            exact_remainder = abs(a(upper) - a(point) - h * g(point))
            assert exact_remainder <= h * eps(t)
            assert abs(A[axis](point) - a(point)) < eps(p)
            assert abs(A[axis](upper) - a(upper)) < eps(p)
            assert abs(G[axis](point) - g(point)) < eps(p)
            local_error = abs(A[axis](upper) - A[axis](point) - h * G[axis](point))
            assert local_error <= h * eps(t) + (2 + h) * eps(p)
            max_local_error = max(max_local_error, local_error)
    V, B, T = volume_sum(G, cells), boundary_sum(A, cells), telescope_sum(A, cells)
    bound = bridge_bound(k, cells, t, p)
    assert T == B
    assert abs(V - B) <= bound
    return {"family": label, "dimension": k, "N": cells, "t": t, "p": p,
            "V": str(V), "B": str(B), "T": str(T), "max_local_error": str(max_local_error),
            "absolute_defect": str(abs(V - B)), "proved_bridge_bound": str(bound),
            "defect_over_bound": str(abs(V - B) / bound), "all_checks_passed": True}


def noisy_tests() -> list[dict]:
    records = []
    for k in range(1, 5):
        a, g = polynomial_family(k)
        for t in range(3):
            cells = 1 << t
            for p in (2, 5, 9):
                records.append(noisy_case(a, g, cells, t, p, "bounded_separable_polynomial"))
    a, g, _ = curved_example()
    for t in range(4):
        cells = 1 << (t + 2)
        for p in (t + 1, t + 4, t + 8):
            records.append(noisy_case(a, g, cells, t, p, "curved_surface"))
    return records


def symbolic_checks() -> dict:
    """Compare exact coefficient dictionaries after clearing denominators."""
    n = Poly.variable(1, 0)
    zero = Poly.constant(1, 0)
    S1 = Q(1, 2) * n * (n - 1)
    S2 = Q(1, 6) * n * (n - 1) * (2 * n - 1)
    assert S1.compose([n + 1]) - S1 - n == zero
    assert S2.compose([n + 1]) - S2 - n**2 == zero
    assert S1((Q(0),)) == S2((Q(0),)) == 0
    Vnumerator = (n - 1)**2 * (8 * n - 1)
    Bnumerator = 2 * n * (n - 1) * (4 * n + 1)
    Dnumerator = (n - 1) * (11 * n - 1)
    assert Bnumerator - Vnumerator == Dnumerator
    # Independent assembly of V from the two one-dimensional power sums:
    # V = (S2/N^3 + 2*S1/N^2)*(S1/N^2).
    assert 12 * (S2 + 2 * n * S1) * S1 == Vnumerator * n**2
    # B = 2*S1/N^2 - S2/N^3.
    assert 12 * (2 * n * S1 - S2) == Bnumerator
    # Finite polynomial remainder identities for the curved example.
    u, v, h = (Poly.variable(3, i) for i in range(3))
    a1 = u**2 * v * (1 + u)
    g1 = (2 * u + 3 * u**2) * v
    a2 = -(u**2 * v**2)
    g2 = -2 * u**2 * v
    R1 = a1.compose([u + h, v, h]) - a1 - h * g1
    R2 = a2.compose([u, v + h, h]) - a2 - h * g2
    assert R1 == v * h**2 * (1 + 3 * u + h)
    assert R2 == -(u**2 * h**2)
    return {"sum_first_powers_recurrence": True, "sum_squares_recurrence": True,
            "closed_V_assembly": True, "closed_B_assembly": True,
            "defect_numerator_identity": True, "curved_remainder_identities": True,
            "method": "exact coefficient equality; no sampled-point polynomial identity test"}


def curved_grid_tests() -> tuple[list[dict], dict]:
    a, g, metadata = curved_example()
    assert [p.lipschitz_l1_bound() for p in a + g] == [Q(7), Q(4), Q(13), Q(6)]
    records = []
    for cells in (1, 2, 4, 8, 16, 32):
        V, B, T = volume_sum(g, cells), boundary_sum(a, cells), telescope_sum(a, cells)
        Vf, Bf, Df = curved_closed_sums(cells)
        assert (V, B, B - V) == (Vf, Bf, Df)
        assert T == B
        records.append({"N": cells, "V_N": str(V), "B_N": str(B), "T_N": str(T),
                        "B_minus_V": str(B - V), "integral_minus_V": str(Q(2, 3) - V),
                        "integral_minus_B": str(Q(2, 3) - B), "V_decimal": float(V),
                        "B_decimal": float(B), "integral_decimal": 2 / 3,
                        "direct_grid_equals_closed_formula": True})
    return records, metadata


def schedule_tests() -> list[dict]:
    records = []
    for r in list(range(17)) + [24, 32]:
        t, n, p = r + 5, r + 9, 2 * r + 16
        N = 1 << n
        assert n >= t + 4 and n >= t + 2
        V, B, defect = curved_closed_sums(N)
        bound = bridge_bound(2, N, t, p)
        ratio = bound / eps(r)
        assert ratio == Q(3, 32) + eps(r + 15)
        assert ratio < Q(1, 8)
        assert defect + 6 * eps(p) <= bound
        assert abs(V - Q(2, 3)) + 2 * eps(p) < eps(r)
        assert abs(B - Q(2, 3)) + 4 * eps(p) < eps(r)
        records.append({"r": r, "t": t, "mesh_exponent_n": n, "N": N, "p": p,
                        "grid_points_if_enumerated": N**2,
                        "V_exact_closed_formula": str(V), "B_exact_closed_formula": str(B),
                        "exact_defect": str(defect), "bridge_bound": str(bound),
                        "bridge_bound_over_2_to_minus_r": str(ratio),
                        "enumerated_large_grid": False, "all_checks_passed": True})
    return records


def write_csv(path: Path, rows: list[dict]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    symbolic = symbolic_checks()
    arbitrary = arbitrary_table_tests()
    boundary = boundary_square_tests()
    curved, metadata = curved_grid_tests()
    noisy = noisy_tests()
    schedules = schedule_tests()
    source_hashes = {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                     for path in [Path(__file__).resolve(), ROOT / "code" / "stokes_reference.py"]}
    receipt = {
        "status": "passed", "validation_scope": "executable exact-arithmetic checks; not a theorem proof or an iPRA derivation",
        "python": platform.python_version(), "arithmetic": "fractions.Fraction", "external_dependencies": [],
        "source_sha256": source_hashes,
        "counts": {"arbitrary_table_telescoping": len(arbitrary), "boundary_square_dimensions": len(boundary),
                   "curved_direct_grid_comparisons": len(curved), "noisy_derivative_cases": len(noisy),
                   "large_schedule_closed_formula_cases": len(schedules)},
        "symbolic_polynomial_checks": symbolic, "curved_example": metadata,
        "arbitrary_table_telescoping": arbitrary, "cubical_boundary_squared": boundary,
        "curved_grid_comparisons": curved, "noisy_derivative_bounds": noisy,
        "precision_schedules": schedules,
        "precision_schedule_note": "Large grids are not enumerated. Evaluations use formulas independently checked by polynomial coefficient identities and small direct grids."
    }
    (OUT / "exact_validation.json").write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    write_csv(OUT / "curved_grid_table.csv", curved)
    write_csv(OUT / "precision_schedule_table.csv", schedules)
    print(json.dumps({"status": "passed", **receipt["counts"], "outputs": ["validation/exact_validation.json", "validation/curved_grid_table.csv", "validation/precision_schedule_table.csv"]}, indent=2))


if __name__ == "__main__":
    main()
