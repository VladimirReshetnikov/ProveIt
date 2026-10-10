#!/usr/bin/env python3
"""Independent raw-orbit Smith checks for cyclic prime distribution quotients.

No normal-form implementation or character table is imported.  The matrix
is constructed directly from the defining q-grid distribution rows, after
identifying points in each orbit of multiplication by u.
"""
from __future__ import annotations

import argparse
from collections import Counter, deque
from math import gcd, prod
import json
from pathlib import Path
import time

import sympy as sp
from sympy.matrices.normalforms import smith_normal_form


def factors(n: int) -> dict[int, int]:
    return {int(p): int(e) for p, e in sp.factorint(n).items()}


def phi(n: int) -> int:
    return prod((p - 1) * p ** (e - 1) for p, e in factors(n).items())


def orbits(q: int, u: int) -> tuple[list[list[int]], list[int]]:
    out: list[list[int]] = []
    index = [-1] * q
    for a in range(q):
        if index[a] >= 0:
            continue
        block: list[int] = []
        b = a
        while index[b] < 0:
            index[b] = len(out)
            block.append(b)
            b = u * b % q
        assert b == a
        out.append(block)
    return out, index


def raw_orbit_matrix(q: int, u: int, weights: dict[int, list[int]], length=1):
    obs, oi = orbits(q, u)
    rows: list[list[int]] = []
    for p in factors(q):
        seen: set[tuple[int, ...]] = set()
        for x in range(0, q, p):
            # py=x (mod q), since x is divisible by p.
            roots = [x // p + j * (q // p) for j in range(p)]
            coeffs = [[0] * length for _ in obs]
            for y in roots:
                coeffs[oi[y]][0] += 1
            for j, a in enumerate(weights[p][:length]):
                coeffs[oi[x]][j] -= a
            flat = tuple(a for block in coeffs for a in block)
            if flat in seen:
                continue
            seen.add(flat)
            for shift in range(length):
                row = [0] * (length * len(obs))
                for i, poly in enumerate(coeffs):
                    for j in range(length - shift):
                        row[length * i + j + shift] += poly[j]
                rows.append(row)
    return sp.Matrix(rows), obs


def compatibility(m: int, active_primes: list[int], constants: dict[int, int], ell: int):
    """Build the proposed H-character by group closure and detect conflicts."""
    one = 1 % m
    values = {one: 1}
    queue = deque([one])
    if any(constants[p] % ell == 0 for p in active_primes):
        return {"compatible": False, "H_size": None, "character_count": 0}
    while queue:
        h = queue.popleft()
        for p in active_primes:
            hp = h * p % m
            val = values[h] * constants[p] % ell
            if hp in values:
                if values[hp] != val:
                    return {"compatible": False, "H_size": None, "character_count": 0}
            else:
                values[hp] = val
                queue.append(hp)
    return {
        "compatible": True,
        "H_size": len(values),
        "character_count": phi(m) // len(values),
        "character_values": {str(h): values[h] for h in sorted(values)},
    }


def predicted(q: int, u: int, ell: int, weights: dict[int, list[int]], length=1):
    assert sp.isprime(ell) and gcd(u, q) == 1
    assert pow(u, ell, q) == 1 and u % q != 1
    m = gcd(u - 1, q)
    d = q // m
    assert gcd(m, d) == 1, "The tame split hypothesis fails"
    assert phi(m) % ell != 0, "The semisimple fixed-denominator hypothesis fails"
    assert gcd(u - 1, d) == 1
    active = list(factors(d))
    comp = compatibility(m, active, {p: weights[p][0] % ell for p in active}, ell)
    contact = 0
    if comp["compatible"]:
        contact = min(
            [j for p in active for j in range(1, min(length, len(weights[p])))
             if weights[p][j] % ell] or [length]
        )
    torsion = comp["character_count"] * 2 ** (len(active) - 1) * contact
    return {
        "m": m, "d": d, "active_primes": active,
        **comp, "contact": contact,
        "free_rank": length * phi(q) // ell,
        "torsion_prime": ell, "torsion_multiplicity": torsion,
    }


def check_case(q: int, u: int, ell: int, weights: dict[int, list[int]], length=1):
    expected = predicted(q, u, ell, weights, length)
    matrix, obs = raw_orbit_matrix(q, u, weights, length)
    start = time.monotonic()
    diag = smith_normal_form(matrix, domain=sp.ZZ)
    nonzero = [abs(int(diag[i, i])) for i in range(min(diag.shape)) if diag[i, i]]
    actual_torsion = [x for x in nonzero if x != 1]
    actual_free = matrix.cols - len(nonzero)
    assert actual_free == expected["free_rank"], (q, u, ell, actual_free, expected)
    assert actual_torsion == [ell] * expected["torsion_multiplicity"], (
        q, u, ell, weights, actual_torsion, expected
    )
    return {
        "q": q, "u": u, "ell": ell, "length": length,
        "weights": weights, "orbit_count": len(obs),
        "matrix_shape": list(matrix.shape),
        "smith_nonzero_counts": dict(sorted(Counter(nonzero).items())),
        **expected, "passed": True,
        "seconds": round(time.monotonic() - start, 4),
    }


def run():
    checks = []
    # Fixed-point-free diagonal actions, including non-squarefree q.
    for q, u, ell in [(7, 2, 3), (13, 3, 3), (11, 3, 5), (31, 2, 5),
                      (49, 18, 3), (91, 16, 3), (21, 20, 2)]:
        for a in range(ell):
            checks.append(check_case(q, u, ell, {p: [a] for p in factors(q)}))
        if len(factors(q)) > 1:
            weights = {p: [1] for p in factors(q)}
            weights[min(weights)] = [2]
            checks.append(check_case(q, u, ell, weights))
    # Partial fixed grids and local-to-global multiplicative compatibility.
    for q, u, ell, moving in [(35, 16, 3, [7]), (105, 16, 3, [7]),
                                (455, 16, 3, [7, 13])]:
        choices = [(0,), (1,), (2,)] if len(moving) == 1 else [(1, 1), (2, 2), (1, 2), (0, 1)]
        for choice in choices:
            weights = {p: [-2] for p in factors(q)}
            weights.update({p: [a] for p, a in zip(moving, choice)})
            checks.append(check_case(q, u, ell, weights))
    # Finite jets: constant compatibility, nontrivial contact, and incompatible.
    for L in (1, 2, 3, 4):
        checks.append(check_case(91, 16, 3, {7: [1, 0, 1], 13: [1, 3, 0, 1]}, L))
        checks.append(check_case(35, 16, 3, {5: [7, 1], 7: [2, 3, 1]}, L))
        checks.append(check_case(35, 16, 3, {5: [0, 1], 7: [0, 1]}, L))
        checks.append(check_case(11, 3, 5, {11: [1, 5, 5, 1]}, L))
    # An action outside the stated tame split hypothesis, for a limitation check.
    wild = []
    for a in range(3):
        M, obs = raw_orbit_matrix(9, 4, {3: [a]})
        diag = smith_normal_form(M, domain=sp.ZZ)
        nz = [abs(int(diag[i, i])) for i in range(min(diag.shape)) if diag[i, i]]
        wild.append({"q": 9, "u": 4, "ell": 3, "a_3": a,
                     "free_rank": M.cols - len(nz), "nonunit_factors": [x for x in nz if x > 1]})
    return {"verified_cases": len(checks), "all_passed": all(c["passed"] for c in checks),
            "checks": checks, "outside_hypotheses_examples": wild,
            "method": "Exact Smith normal form of raw orbit distribution rows over ZZ"}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1] / "results" / "cyclic_prime_results.json")
    args = parser.parse_args()
    result = run()
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "checks"}, indent=2))
