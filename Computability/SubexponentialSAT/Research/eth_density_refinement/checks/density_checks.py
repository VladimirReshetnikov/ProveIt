#!/usr/bin/env python3
"""Exact small checks for the density-sensitive parity-check construction.

This is a validation artifact, not an implementation of the asymptotic #SAT
algorithm. It checks rational parameter inequalities, small graph instances,
the Tanner-distance mechanism, and greedy parity selection using a brute-force
counting oracle. Finite checks do not prove the general expander theorem or
the preprint's tensor-contraction theorem.

Run: python3 density_checks.py --output density_checks_results.json
Only Python's standard library is required. If NumPy is installed, optional
small-graph spectral diagnostics are also recorded.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import itertools
import json
import math
from pathlib import Path
from typing import Iterable


def ceil_log2_positive(x: int) -> int:
    assert x >= 1
    return (x - 1).bit_length()


def parameter_checks() -> list[dict]:
    records = []
    for B in [1, 2, 3, 4, 8, 16, 31, 64, 127, 256, 1024]:
        b = ceil_log2_positive(2 * B)
        delta = Fraction(1, 1024 * B * b)
        # The analytical entropy proof uses log2(e/delta) < 11+2b <= 13b.
        assert 2 ** (b - 1) <= 2 * B <= 2**b
        assert B <= 2 ** (b - 1)
        assert b <= 2**b
        assert 11 + 2 * b <= 13 * b
        entropy_upper = Fraction(13, 1024 * B)
        assert entropy_upper < Fraction(1, 64 * B)
        assert delta * 13 * b == entropy_upper
        r = 0
        while 2048 * B * b * 19**r > 20**r:
            r += 1
        d = 16**r
        assert Fraction(19, 20) ** r <= delta / 2
        assert r == 0 or Fraction(19, 20) ** (r - 1) > delta / 2
        assert d >= 32 * B
        assert Fraction(20, 19) ** 55 > 16
        assert d <= 16 * (2048 * B * b) ** 55
        P = 2 * (1024 * B * b) ** 2
        assert Fraction(1, P) == delta * delta / 2
        records.append(
            {
                "B": B,
                "b": b,
                "r": r,
                "d_binary_length": d.bit_length(),
                "P": P,
                "delta": str(delta),
                "entropy_upper": str(entropy_upper),
                "status": "passed_exact_rational_checks",
            }
        )
    return records


def mgg_neighbors(t: int, x: int, y: int) -> list[tuple[int, int]]:
    """Eight symmetric Margulis--Gabber--Galil ports, including multiplicity."""
    return [
        ((x + 2 * y) % t, y),
        ((x - 2 * y) % t, y),
        ((x + 2 * y + 1) % t, y),
        ((x - 2 * y - 1) % t, y),
        (x, (y + 2 * x) % t),
        (x, (y - 2 * x) % t),
        (x, (y + 2 * x + 1) % t),
        (x, (y - 2 * x - 1) % t),
    ]


def graph_checks() -> list[dict]:
    try:
        import numpy as np
    except ImportError:
        np = None
    records = []
    for t in range(2, 9):
        vertices = list(itertools.product(range(t), repeat=2))
        index = {v: j for j, v in enumerate(vertices)}
        q = t * t
        adjacency = [[0] * q for _ in range(q)]
        for u, (x, y) in enumerate(vertices):
            ports = mgg_neighbors(t, x, y)
            for v in ports:
                adjacency[u][index[v]] += 1
        for port in range(8):
            images = {mgg_neighbors(t, x, y)[port] for x, y in vertices}
            assert len(images) == q  # Every port map is a permutation.
        for i in range(q):
            assert sum(adjacency[i]) == 8
            assert sum(adjacency[j][i] for j in range(q)) == 8
            for j in range(q):
                assert adjacency[i][j] == adjacency[j][i]
        lazy = [row[:] for row in adjacency]
        for i in range(q):
            lazy[i][i] += 8
            assert sum(lazy[i]) == 16
        record = {
            "t": t,
            "vertices": q,
            "base_degree": 8,
            "lazy_degree": 16,
            "exact_checks": "port_permutations_symmetry_and_row_sums_passed",
        }
        if np is not None:
            eigs = np.linalg.eigvalsh(np.array(lazy, dtype=float) / 16.0)
            assert abs(float(eigs[-1]) - 1.0) < 1e-9
            assert float(eigs[0]) >= -1e-9
            rho = max(abs(float(x)) for x in eigs[:-1])
            assert rho <= 0.95 + 1e-9
            record["nontrivial_normalized_spectral_radius_float"] = rho
            record["spectral_note"] = "numerical_check_only_for_this_small_graph"
        else:
            record["spectral_note"] = "NumPy_unavailable_optional_diagnostic_skipped"
        records.append(record)
    return records


def parity(word: int, mask: int) -> int:
    return (word & mask).bit_count() & 1


def tanner_checks() -> list[dict]:
    # Every local code here is an even-parity code: local distance 2.
    # Matrices list the multiplicity of each edge between left/right vertices.
    cases = [
        ("K_2_2_repetition", [[1, 1], [1, 1]], Fraction(0)),
        ("K_3_3_even_parity", [[1, 1, 1]] * 3, Fraction(0)),
        ("parallel_expander", [[2, 1], [1, 2]], Fraction(1, 3)),
        ("one_vertex_parallel", [[4]], Fraction(0)),
    ]
    records = []
    for name, matrix, epsilon in cases:
        q = len(matrix)
        d = sum(matrix[0])
        assert d >= 2
        assert all(sum(row) == d for row in matrix)
        assert all(sum(matrix[i][j] for i in range(q)) == d for j in range(q))
        edges = [(u, v) for u in range(q) for v in range(q)
                 for _ in range(matrix[u][v])]
        M = len(edges)
        row_masks = [sum(1 << e for e, (u, _) in enumerate(edges) if u == v)
                     for v in range(q)]
        col_masks = [sum(1 << e for e, (_, w) in enumerate(edges) if w == v)
                     for v in range(q)]
        checks = row_masks + col_masks
        delta = Fraction(2, d)
        assert epsilon < delta
        theoretical_weight = delta * (delta - epsilon) * q * d
        accepted = [word for word in range(1, 1 << M)
                    if not any(parity(word, check) for check in checks)]
        assert accepted
        for word in accepted:
            h = word.bit_count()
            U = {u for e, (u, _) in enumerate(edges) if (word >> e) & 1}
            V = {v for e, (_, v) in enumerate(edges) if (word >> e) & 1}
            assert h >= delta * d * max(len(U), len(V))
            assert Fraction(h) >= theoretical_weight
            # Squared rational version of sqrt(|U||V|)>=(delta-epsilon)q.
            assert len(U) * len(V) >= (delta - epsilon)**2 * q**2
        # Check every shortening to a prefix of edge coordinates.
        shortening_cases = 0
        for m in range(1, M + 1):
            for word in range(1, 1 << m):
                if not any(parity(word, check) for check in checks):
                    assert word.bit_count() >= theoretical_weight
                    assert word.bit_count() >= delta * (delta - epsilon) * m
            shortening_cases += 1
        records.append(
            {
                "case": name,
                "edges": M,
                "delta": str(delta),
                "epsilon": str(epsilon),
                "nonzero_codewords": len(accepted),
                "minimum_weight": min(word.bit_count() for word in accepted),
                "theoretical_weight_lower_bound": str(theoretical_weight),
                "shortening_cases": shortening_cases,
                "status": "exhaustive_exact_checks_passed",
            }
        )
    return records


def clause_satisfied(assignment: int, clause: tuple[int, ...]) -> bool:
    return any(bool((assignment >> (abs(lit) - 1)) & 1) == (lit > 0)
               for lit in clause)


def violation_vector(assignment: int, clauses: list[tuple[int, ...]]) -> int:
    return sum((not clause_satisfied(assignment, clause)) << e
               for e, clause in enumerate(clauses))


def candidate_rows(m: int, P: int) -> Iterable[int]:
    # Repeated representations and coefficient-zero pairs are intentional:
    # they preserve exactly the uniform-list averaging argument.
    choices = list(itertools.product(range(m), [0, 1]))
    for pairs in itertools.product(choices, repeat=P):
        row = 0
        for e, coefficient in pairs:
            if coefficient:
                row ^= 1 << e
        yield row


def run_greedy_case(name: str, n: int, clauses: list[tuple[int, ...]],
                    initial: list[int], P: int) -> dict:
    m = len(clauses)
    violations = [violation_vector(x, clauses) for x in range(1 << n)]
    exact_count = sum(v == 0 for v in violations)
    rows = list(initial)
    survivors = [v for v in violations if not any(parity(v, row) for row in rows)]
    assert all(v == 0 or v.bit_count() * P >= m for v in survivors)
    records = []
    number_candidates = (2 * m) ** P
    for stage in range(3 * n):
        before = len(survivors) - exact_count
        best_count = None
        best_row = None
        unwanted_total = 0
        evaluated = 0
        for row in candidate_rows(m, P):
            count = sum(parity(v, row) == 0 for v in survivors)
            unwanted_total += count - exact_count
            evaluated += 1
            if best_count is None or count < best_count:
                best_count, best_row = count, row
        assert evaluated == number_candidates
        average_unwanted = Fraction(unwanted_total, evaluated)
        assert average_unwanted <= Fraction(3, 4) * before
        assert best_row is not None
        rows.append(best_row)
        survivors = [v for v in survivors if parity(v, best_row) == 0]
        after = len(survivors) - exact_count
        assert after <= Fraction(3, 4) * before
        records.append({"stage": stage + 1, "unwanted_before": before,
                        "unwanted_after": after,
                        "average_unwanted": str(average_unwanted),
                        "selected_row_mask": best_row})
    assert len(survivors) == exact_count
    assert Fraction(2**n) * Fraction(3, 4) ** (3 * n) < 1
    return {"case": name, "variables": n, "clauses": m, "P": P,
            "candidate_lists_per_stage": number_candidates,
            "exact_satisfying_count": exact_count,
            "final_parity_system_count": len(survivors),
            "stages": records, "status": "exhaustive_oracle_checks_passed"}


def greedy_checks() -> list[dict]:
    # K_2,2 edge-order (0,0),(0,1),(1,0),(1,1): even parity at four vertices.
    initial_tanner_checks = [0b0011, 0b1100, 0b0101, 0b1010]
    return [
        run_greedy_case("unit_clauses_with_Tanner_initial_checks", 4,
                        [(1,), (2,), (3,), (4,)], initial_tanner_checks, 1),
        run_greedy_case("mixed_2CNF_with_empty_initial_checks", 3,
                        [(1, 2), (-1, 3), (-2, -3)], [], 3),
    ]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("density_checks_results.json"))
    args = parser.parse_args()
    result = {
        "artifact": "density_sensitive_parity_checks_validation",
        "scope": "finite exact checks and optional floating-point diagnostics; not a full solver",
        "parameters": parameter_checks(),
        "graphs": graph_checks(),
        "tanner_distance": tanner_checks(),
        "greedy_parity": greedy_checks(),
        "overall_status": "passed",
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"overall_status": "passed", "output": str(args.output),
                      "parameter_cases": len(result["parameters"]),
                      "graph_cases": len(result["graphs"]),
                      "tanner_cases": len(result["tanner_distance"]),
                      "greedy_cases": len(result["greedy_parity"])}))


if __name__ == "__main__":
    main()
