#!/usr/bin/env python3
"""Exact finite checks for the graph-coupled root compression theorem.

These checks use rational arithmetic in SymPy. They establish the recorded
finite identities, not the universal theorem or a Lean formalization.
Run: python3 verify_graph.py
"""
from __future__ import annotations

import json
from pathlib import Path

import sympy as s

z = s.Symbol("z")


def laplacian(n, edges):
    L = s.zeros(n)
    for i, j, weight in edges:
        assert 0 <= i < n and 0 <= j < n and i != j
        weight = s.Rational(weight)
        assert weight > 0
        b = s.zeros(n, 1)
        b[i] = 1
        b[j] = -1
        L += weight * b * b.T
    return L


def build(root_lists, edges):
    n = len(root_lists)
    assert n >= 1 and all(root_lists)
    roots = [s.Rational(a) for row in root_lists for a in row]
    N = len(roots)
    L = laplacian(n, edges)
    one_n = s.ones(n, 1)
    J = one_n * one_n.T / n
    assert L.rank() == n - 1
    Lplus = (L + J).inv() - J
    assert Lplus == Lplus.T
    assert L * Lplus == s.eye(n) - J
    assert Lplus * one_n == s.zeros(n, 1)
    tau = L.minor_submatrix(0, 0).det() if n > 1 else s.Integer(1)
    assert tau > 0
    F = [s.prod(z - s.Rational(a) for a in row) for row in root_lists]
    V = s.zeros(N, n)
    index = 0
    for i, row in enumerate(root_lists):
        for _ in row:
            V[index, i] = 1
            index += 1
    one_N = s.ones(N, 1)
    Q = s.eye(N) - one_N * one_N.T / N
    Lambda = s.diag(*roots)
    K = Q * Lambda * Q - Q * V * Lplus * V.T * Q
    assert K == K.T
    assert K * one_N == s.zeros(N, 1)
    # Column-wise denominator clearing gives an entire polynomial matrix.
    P = s.Poly((L * s.diag(*F) + s.diag(*[s.diff(f, z) for f in F])).det(), z)
    ambient_characteristic = K.charpoly(z).as_poly()
    compressed_characteristic, remainder = s.div(ambient_characteristic, s.Poly(z, z))
    assert remainder.is_zero
    assert P == s.Poly(N * tau * compressed_characteristic.as_expr(), z)
    assert P.degree() == N - 1
    assert P.LC() == N * tau
    degrees = s.Matrix([len(row) for row in root_lists])
    resistance_sum = s.Integer(0)
    resistances = {}
    for i in range(n):
        for j in range(i + 1, n):
            R = Lplus[i, i] + Lplus[j, j] - 2 * Lplus[i, j]
            assert R > 0
            resistance_sum += degrees[i] * degrees[j] * R
            resistances[f"{i + 1}-{j + 1}"] = str(R)
    centroid_sum = s.Rational(N - 1, N) * sum(roots) - resistance_sum / N
    assert s.trace(K) == centroid_sum, (s.trace(K), centroid_sum, degrees, resistance_sum)
    vieta_sum = -P.nth(N - 2) / P.LC() if N > 1 else s.Integer(0)
    assert vieta_sum == centroid_sum
    collisions = []
    for a in sorted(set(roots)):
        S = [i for i, f in enumerate(F) if f.subs(z, a) == 0]
        T = [i for i in range(n) if i not in S]
        multiplicities = [sum(s.Rational(v) == a for v in root_lists[i]) for i in S]
        C = L.extract(T, T)
        for k, i in enumerate(T):
            C[k, k] += s.diff(F[i], z).subs(z, a) / F[i].subs(z, a)
        nullity = len(T) - C.rank()
        predicted = sum(m - 1 for m in multiplicities) + nullity
        shifted = s.Poly(P.as_expr().subs(z, z + a), z)
        actual = min(power[0] for power, coefficient in shifted.terms() if coefficient)
        assert actual == predicted
        collisions.append({"root": str(a), "vanishing_inputs": [i + 1 for i in S],
                           "input_multiplicities": multiplicities,
                           "complementary_nullity": nullity,
                           "predicted_order": predicted, "actual_order": actual})
    return {"n": n, "N": N, "L": L, "Lplus": Lplus, "tau": tau,
            "F": F, "V": V, "Q": Q, "K": K, "P": P,
            "root_lists": root_lists, "edges": edges,
            "record": {"vertices": n, "total_input_degree": N,
                       "weighted_tree_sum": str(tau), "degree": P.degree(),
                       "polynomial_factored": str(s.factor(P.as_expr())),
                       "sum_output_roots": str(centroid_sum),
                       "resistance_sum_unordered": str(resistance_sum),
                       "resistances": resistances, "collisions": collisions,
                       "compression_identity": True, "centroid_identity": True}}


def edge_check(data, i, j, h):
    n = data["n"]
    h = s.Rational(h)
    assert h > 0
    b = s.zeros(n, 1)
    b[i], b[j] = 1, -1
    R = (b.T * data["Lplus"] * b)[0]
    q = data["Q"] * data["V"] * data["Lplus"] * b
    new = build(data["root_lists"], data["edges"] + [(i, j, h)])
    c = h / (1 + h * R)
    update = c * q * q.T
    assert new["K"] - data["K"] == update
    assert c > 0
    assert update.rank() == 1
    assert new["tau"] == data["tau"] * (1 + h * R)
    shift = (c * q.T * q)[0]
    assert s.trace(new["K"] - data["K"]) == shift
    return {"edge": [i + 1, j + 1], "increment": str(h),
            "prior_effective_resistance": str(R),
            "rank_one_coefficient": str(c), "centroid_shift": str(shift),
            "rank": update.rank(), "positive_semidefinite_by_outer_product": True,
            "update_identity": True, "tree_update_identity": True}


def main():
    cases = [
        ("one_vertex_constant_output", [[5]], []),
        ("one_vertex_derivative", [[-2, 1, 1, 4]], []),
        ("two_vertex_linear", [[-1], [3]], [(0, 1, s.Rational(2, 3))]),
        ("path_shared_pole_collision", [[0, 0], [0, 2], [1, 3]],
         [(0, 1, 1), (1, 2, s.Rational(4, 3))]),
        ("triangle_mixed_multiplicities", [[-2, 0, 0], [0, 3], [-1, 3]],
         [(0, 1, 1), (1, 2, s.Rational(3, 2)), (0, 2, s.Rational(2, 5))]),
        ("four_cycle_all_shared", [[0, 0], [0], [0, 0, 0], [0, 2]],
         [(0, 1, 1), (1, 2, 2), (2, 3, 3), (3, 0, 4)]),
    ]
    result = {"method": "Exact rational SymPy polynomial and matrix identities",
              "sympy_version": s.__version__, "cases": {}, "edge_updates": {},
              "scope": "Finite checks of explicit cases; universal claims are proved in the paper, not by this script."}
    data_by_name = {}
    for name, roots, edges in cases:
        data = build(roots, edges)
        data_by_name[name] = data
        result["cases"][name] = data["record"]
        print(f"PASS {name}: N={data['N']}, degree={data['P'].degree()}, tau={data['tau']}")
        print("  P(z) =", s.factor(data["P"].as_expr()))
    edge_cases = [
        ("increase_existing_edge", "triangle_mixed_multiplicities", 0, 1, s.Rational(7, 5)),
        ("add_absent_edge", "path_shared_pole_collision", 0, 2, s.Rational(5, 7)),
        ("leave_collision", "path_shared_pole_collision", 1, 2, s.Rational(1, 3)),
        ("add_cycle_diagonal", "four_cycle_all_shared", 0, 2, s.Rational(11, 13)),
    ]
    for name, base, i, j, h in edge_cases:
        record = edge_check(data_by_name[base], i, j, h)
        result["edge_updates"][name] = record
        print(f"PASS {name}: resistance={record['prior_effective_resistance']}, sum-root shift={record['centroid_shift']}")
    tuned = result["cases"]["path_shared_pole_collision"]["collisions"]
    assert next(r for r in tuned if r["root"] == "0")["actual_order"] == 2
    changed = build([[0, 0], [0, 2], [1, 3]], [(0, 1, 1), (1, 2, s.Rational(5, 3))])
    assert next(r for r in changed["record"]["collisions"] if r["root"] == "0")["actual_order"] == 1
    result["collision_transition"] = {"edge_weight_before": "4/3", "edge_weight_after": "5/3",
                                      "order_at_zero_before": 2, "order_at_zero_after": 1}
    path = Path(__file__).resolve().parents[1] / "checks" / "graph_checks.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(result, indent=2) + "\n")
    print(f"PASS all {len(cases)} base models, {len(edge_cases)} edge updates, and the shared-pole collision transition.")


if __name__ == "__main__":
    main()
