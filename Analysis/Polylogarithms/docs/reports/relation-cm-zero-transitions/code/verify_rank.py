#!/usr/bin/env python3
"""Independent exact replay of the manuscript's level-4 imaginary product matrix.

Uses only the displayed stuffle and shuffle coefficient rules.  It does not
import or copy the baseline implementation.  SymPy is used for exact ranks
and Smith forms; polynomial basis witnesses are constructed independently.
"""
from __future__ import annotations

import argparse
import json
from math import comb
from pathlib import Path

import sympy as sp
from sympy.matrices.normalforms import smith_normal_form

PAIRS = ((0, 1), (1, 0), (1, 1), (1, 2), (1, 3), (2, 1))
X, Y = sp.symbols("X Y")


def canonical(r, s):
    r, s = r % 4, s % 4
    if r % 2 == s % 2 == 0:
        return None, 0
    if (r, s) in PAIRS:
        return (r, s), 1
    pair = ((-r) % 4, (-s) % 4)
    assert pair in PAIRS
    return pair, -1


def product_matrix(w):
    """Return the exact original matrix after the one divergent omission."""
    assert w >= 3
    omitted = (1, w - 1, 0, 1)
    coords_full = [
        (a, w-a, r, s)
        for a in range(1, w)
        for r, s in PAIRS
    ]
    idx = {c: j for j, c in enumerate(coords_full)}
    omitted_index = idx[omitted]
    coords = [c for c in coords_full if c != omitted]
    rows, tags = [], []

    def add(row, a, b, r, s, coefficient=1):
        pair, sign = canonical(r, s)
        if pair is not None:
            row[idx[(a, b, *pair)]] += sign * coefficient

    for p in range(1, w):
        q = w-p
        for r in range(4):
            for s in range(4):
                stuffle, shuffle = [0] * len(coords_full), [0] * len(coords_full)
                add(stuffle, p, q, r, s)
                add(stuffle, q, p, s, r)
                for j in range(p):
                    add(shuffle, q+j, p-j, s, r-s, comb(q+j-1, j))
                for j in range(q):
                    add(shuffle, p+j, q-j, r, s-r, comb(p+j-1, j))
                divergent_count = int(p == 1 and r == 0) + int(q == 1 and s == 0)
                if divergent_count == 1:
                    candidates = [("regularized_difference", [a-b for a, b in zip(stuffle, shuffle)])]
                else:
                    assert divergent_count == 0
                    candidates = [("stuffle", stuffle), ("shuffle", shuffle)]
                for kind, row in candidates:
                    assert row[omitted_index] == 0
                    row = row[:omitted_index] + row[omitted_index+1:]
                    if any(row):
                        rows.append(row)
                        tags.append((p, q, r, s, kind))
    return sp.Matrix(rows), coords, tags


def vector_from_BD(w, B, D, coords):
    """Use the theorem's six explicit polynomial formulas."""
    def sub(poly, x, y):
        return sp.expand(poly.subs({X: x, Y: y}, simultaneous=True))
    polys = {
        (0, 1): -sub(B, Y, X),
        (1, 0): B,
        (1, 1): -sub(D, X-Y, X),
        (1, 2): D,
        (1, 3): sub(B, X-Y, X),
        (2, 1): -sub(D, Y, X),
    }
    polys = {pair: sp.Poly(p, X, Y) for pair, p in polys.items()}
    return sp.Matrix([polys[(r, s)].coeff_monomial(X**(a-1)*Y**(b-1))
                      for a, b, r, s in coords])


def primitive_nullspace(w, coords):
    """A full integral nullspace basis (odd weight only).

    The integral coordinate change u=Y,v=X-Y makes T swap u,v.
    Antisymmetric/symmetric paired monomials therefore form primitive bases.
    """
    if w % 2 == 0:
        return sp.zeros(len(coords), 0), []
    n, m = w-2, (w-1)//2
    columns, names = [], []
    for which in ("B", "D"):
        for j in range(m):
            first = Y**j * (X-Y)**(n-j)
            second = Y**(n-j) * (X-Y)**j
            poly = sp.expand(first + (-1 if which == "B" else 1) * second)
            B, D = (poly, sp.Integer(0)) if which == "B" else (sp.Integer(0), poly)
            columns.append(vector_from_BD(w, B, D, coords))
            names.append(f"{which}_{j}")
    return sp.Matrix.hstack(*columns), names


def smith_factors(M):
    S = smith_normal_form(M, domain=sp.ZZ)
    return [abs(int(S[j,j])) for j in range(min(S.shape)) if S[j,j]]


def expected(w, without_g=False):
    cols = (5*w-6) if without_g else (6*w-7)
    if w % 2:
        rank = (9*w-11)//2 if without_g else 5*w-6
        return cols, [1]*rank
    twos = w//2 if without_g else w
    return cols, [1]*(cols-twos) + [2]*twos


def verify(max_weight, smith_max_weight, output):
    receipt = {
        "baseline_commit": "9bc738d3be22b8586a24693f19fb2e2a50ecd1bf",
        "meaning": "Exact formal matrix verification; no numerical independence claim.",
        "weights": [],
    }
    for w in range(3, max_weight+1):
        A, coords, tags = product_matrix(w)
        g_cols = [j for j,c in enumerate(coords) if c[2:] == (1,0)]
        other_cols = [j for j in range(A.cols) if j not in g_cols]
        Ag = A[:, other_cols]
        K, names = primitive_nullspace(w, coords)
        assert A*K == sp.zeros(A.rows, K.cols)
        assert K.rank() == (w-1 if w % 2 else 0)
        rank, rank_g = A.rank(), Ag.rank()
        assert rank == len(expected(w)[1])
        assert rank_g == len(expected(w, True)[1])
        row = {"weight":w, "rows":A.rows, "columns":A.cols,
               "rank":rank, "nong_rank":rank_g,
               "primitive_nullspace_columns":K.cols,
               "all_basis_residuals_exactly_zero":True}
        if w <= smith_max_weight:
            s, sg = smith_factors(A), smith_factors(Ag)
            assert s == expected(w)[1]
            assert sg == expected(w, True)[1]
            row["smith_counts"] = {"one":s.count(1),"two":s.count(2)}
            row["nong_smith_counts"] = {"one":sg.count(1),"two":sg.count(2)}
        print(json.dumps(row), flush=True)
        receipt["weights"].append(row)
        if w == 5:
            witness = vector_from_BD(5, sp.Integer(0), X**3, coords)
            assert A*witness == sp.zeros(A.rows,1)
            T = sp.zeros(len(coords),1)
            for c, coefficient in (((4,1,1,0),3), ((3,2,1,0),3),
                                   ((2,3,1,0),9), ((4,1,1,2),7)):
                T[coords.index(c)] = coefficient
            assert (T.T*witness)[0] == 7
            receipt["weight_five_obstruction"] = {
                "coordinates":[list(c) for c in coords],
                "nonzero_witness":[{"coordinate":list(c),"value":int(v)}
                                   for c,v in zip(coords,witness) if v],
                "target_pairing":7,
                "all_row_residuals_exactly_zero":True,
            }
            # Full exact matrix and primitive integral basis, for external replay.
            package = {"weight":5,"coordinates":[list(c) for c in coords],
                       "rows":[[int(v) for v in A.row(j)] for j in range(A.rows)],
                       "row_tags":[list(t) for t in tags],
                       "basis_names":names,
                       "basis_columns":[[int(v) for v in K.col(j)] for j in range(K.cols)]}
            output.with_name("weight_five_matrix_and_kernel.json").write_text(
                json.dumps(package,indent=2)+"\n")
    output.write_text(json.dumps(receipt,indent=2)+"\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-weight", type=int, default=13)
    parser.add_argument("--smith-max-weight", type=int, default=10)
    parser.add_argument("--output",type=Path,
                        default=Path(__file__).with_name("exact_rank_receipt.json"))
    args=parser.parse_args()
    verify(args.max_weight,args.smith_max_weight,args.output)
