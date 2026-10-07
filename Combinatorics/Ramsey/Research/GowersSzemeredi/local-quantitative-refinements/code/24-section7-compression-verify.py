#!/usr/bin/env python3
"""Exact finite checks for gowers_section7_refinements.tex (Python 3.10+).

These tests are regression checks, not proofs or Lean verification.
No third-party libraries or network access are required.
Run: python3 verify.py --output verification_results.json
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path
import random


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def scalar_checks() -> int:
    count = 0
    for i in range(1, 41):
        u = F(i, 40)
        for j in range(101):
            s = F(j, 100)
            h = s**3 * (-9 if 2*s < u else 1)
            line = F(49, 12)*u*u*s - F(343, 108)*u**3
            require(h >= line, f"Cubic minorant failed: {u=}, {s=}")
            b = F(7, 6)*u
            require(s**3-line == (s-b)**2*(s+2*b), "Factorization")
            count += 1
    return count


def incidence_checks() -> int:
    n, m = 4, 3
    count = 0
    for mask in range(1 << (n*m)):
        rows = [{v for v in range(m) if mask & (1 << (i*m+v))}
                for i in range(n)]
        codeg = [[len(rows[i] & rows[j]) for j in range(n)]
                  for i in range(n)]
        u = F(sum(map(sum, codeg)), m*n*n)
        bad = [[2*F(codeg[i][j], m) < u for j in range(n)]
                for i in range(n)]
        scores = []
        for sample in product(range(m), repeat=3):
            core = [i for i in range(n) if all(v in rows[i] for v in sample)]
            bcount = sum(bad[i][j] for i in core for j in core)
            scores.append(len(core)**2 - 10*bcount)
        exact_moment = sum(F(codeg[i][j], m)**3 * (-9 if bad[i][j] else 1)
                           for i in range(n) for j in range(n))
        require(F(sum(scores), m**3) == exact_moment, "Moment identity")
        require(max(scores) >= F(49, 54)*u**3*n*n, "Cubic selector")
        count += 1
    return count


def weighted_checks() -> int:
    rng = random.Random(701)
    count = 0
    for _ in range(100):
        n, m, t = 3, 3, 2
        x, y = [rng.randint(1, 5) for _ in range(n)], [rng.randint(1, 5) for _ in range(m)]
        mu, nu = [F(a, sum(x)) for a in x], [F(b, sum(y)) for b in y]
        rows = [{v for v in range(m) if rng.randrange(2)} for _ in range(n)]
        codeg = [[sum((nu[v] for v in rows[i] & rows[j]), F(0))
                   for j in range(n)] for i in range(n)]
        beta, eta = F(1, 4), F(1, 3)
        lhs = F(0)
        for sample in product(range(m), repeat=t):
            prob = nu[sample[0]] * nu[sample[1]]
            core = [i for i in range(n) if all(v in rows[i] for v in sample)]
            mass = sum((mu[i] for i in core), F(0))
            badmass = sum((mu[i]*mu[j] for i in core for j in core
                           if codeg[i][j] < beta), F(0))
            lhs += prob*(mass*mass-badmass/eta)
        rhs = sum((mu[i]*mu[j]*codeg[i][j]**t * (1-1/eta if codeg[i][j] < beta else 1)
                   for i in range(n) for j in range(n)), F(0))
        require(lhs == rhs, "Weighted moment identity")
        count += 1
    return count


def graph_core(rows: list[set[int]]) -> tuple[list[int], list[int], F, list[list[int]]]:
    m = len(rows)
    p = F(sum(map(len, rows)), m*m)
    require(p > 0, "Nonzero edge density required")
    codeg = [[len(rows[i] & rows[j]) for j in range(m)] for i in range(m)]
    beta = p*p/16
    bad = [[F(codeg[i][j], m) < beta for j in range(m)] for i in range(m)]
    candidates = []
    for v in range(m):
        core = [i for i in range(m) if v in rows[i]]
        defects = sum(bad[i][j] for i in core for j in core)
        candidates.append((len(core)**2-8*defects, core))
    score, core = max(candidates, key=lambda item: item[0])
    require(score >= p*p*m*m/2, "One-sample score")
    good = [i for i in core if 4*sum(bad[i][j] for j in core) <= len(core)]
    require(2*len(good) >= len(core), "Pruning")
    for i in good:
        for j in good:
            common = [v for v in core if not bad[i][v] and not bad[j][v]]
            require(2*len(common) >= len(core), "Common good vertices")
            walks = sum(codeg[i][v]*codeg[v][j] for v in common)
            require(walks >= F(len(core), 2)*beta**2*m*m, "Walk bound")
    return core, good, p, codeg


def graph_checks() -> int:
    n = 4
    positions = [(i, j) for i in range(n) for j in range(i, n)]
    count = 0
    for mask in range(1, 1 << len(positions)):
        rows = [set() for _ in range(n)]
        for b, (i, j) in enumerate(positions):
            if mask & (1 << b):
                rows[i].add(j)
                rows[j].add(i)
        graph_core(rows)
        count += 1
    return count


def additive_checks() -> int:
    count = 0
    for q in (3, 5, 7, 11):
        for mask in range(1, 1 << q):
            A = [a for a in range(q) if mask & (1 << a)]
            m = len(A)
            reps = Counter((a-b) % q for a in A for b in A)
            kappa = F(sum(v*v for v in reps.values()), m**3)
            tau = kappa/2
            D = {d for d, r in reps.items() if r >= tau*m}
            rows = [{j for j, b in enumerate(A) if (a-b) % q in D} for a in A]
            core, good, p, _ = graph_core(rows)
            require(p >= (kappa-tau)/(1-tau), "Popular energy split")
            require(len(D) <= p*m/tau, "Popular difference count")
            S = [A[i] for i in good]
            diff = {(a-b) % q for a in S for b in S}
            require(len(diff) <= 512*F(m*m, len(core))/tau**4, "Absolute profile")
            require(F(len(diff), len(S)) <= 2048/(p*p*tau**4), "Relative profile")
            require(len(S) >= kappa*m/8, "Rounded retained size")
            require(len(diff) <= 2**15*kappa**(-5)*m, "Rounded difference bound")
            require(len(diff) <= 2**17*kappa**(-6)*len(S), "Rounded doubling")
            count += 1
    return count


def sumset(X: set[tuple[int, int]], Y: set[tuple[int, int]], q: int) -> set[tuple[int, int]]:
    return {((a+c) % q, (b+d) % q) for a, b in X for c, d in Y}


def graph_sums(phi: dict[int, int], q: int, k: int) -> set[tuple[int, int]]:
    S = {(0, 0)}
    G = set(phi.items())
    for _ in range(k):
        S = sumset(S, G, q)
    return S


def fibre_trial(phi: dict[int, int], p: int, k: int) -> bool:
    G = set(phi.items())
    sums = graph_sums(phi, p, k)
    Fk = {(y-v) % p for x, y in sums for u, v in sums if x == u}
    Q = len(Fk)
    image = {(x, (y+z) % p) for x, y in G for z in Fk}
    require(len(image) == Q*len(G), "Fibre injection")
    sums_more = sumset(sums, G, p)
    large = {((x-u) % p, (y-v) % p) for x, y in sums_more for u, v in sums}
    require(image <= large, "Injection range")
    diff = {((x-u) % p, (y-v) % p) for x, y in G for u, v in G}
    C = F(len(diff), len(G))
    require(Q <= C**(2*k+1), "Fibre cardinality")
    L = (p-2)//(k*(Q-1)) if Q > 1 else 0
    good_d = [d for d in range(1, p) if all((j*d) % p not in Fk
              for j in range(-k*L, k*L+1) if j)]
    require(bool(good_d), "Avoidance scalar exists")
    d = good_d[0]
    colors = Counter((y-j*d) % p for y in phi.values() for j in range(L+1))
    a = max(colors, key=colors.get)
    chosen = ({x: y for x, y in phi.items() if any((y-j*d) % p == a for j in range(L+1))}
              if Q > 1 else dict(phi))
    require(len(chosen) >= F(len(phi), k*Q), "Avoidance retained size")
    output_sets: dict[int, set[int]] = {}
    for x, y in graph_sums(chosen, p, k):
        output_sets.setdefault(x, set()).add(y)
    require(all(len(values) == 1 for values in output_sets.values()), "Freiman property")
    return L > 0 and Q > 1


def fibre_checks() -> dict[str, int]:
    count = active = 0
    for p in (2, 3, 5):
        for outputs in product(range(p), repeat=p):
            active += fibre_trial(dict(enumerate(outputs)), p, 2)
            count += 1
    rng = random.Random(705)
    for p in (101, 503):
        for _ in range(30):
            phi = {x: rng.randrange(p) for x in (0, 1, 2)}
            active += fibre_trial(phi, p, 2)
            count += 1
    require(active > 0, "Nontrivial progression avoidance exercised")
    return {"maps": count, "nontrivial_avoidance_cases": active}


def ledger_checks() -> dict[str, int]:
    k = 8
    exponent = 1+6*(2*k+1)
    power2 = 3+3+17*(2*k+1)
    require(exponent == 103 and power2 == 295, "Final constants")
    return {"order": k, "energy_exponent": exponent, "power_of_two_loss": power2}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('verification_results.json'))
    args = parser.parse_args()
    report = {"status": "PASS", "arithmetic": "exact integers and fractions",
              "scope": "Finite regression checks; not a general proof or Lean verification",
              "scalar_grid_points": scalar_checks(),
              "incidence_matrices_4_by_3": incidence_checks(),
              "weighted_incidence_trials": weighted_checks(),
              "symmetric_graphs_4_vertices_with_loops_nonempty": graph_checks(),
              "nonempty_cyclic_additive_sets": additive_checks(),
              "fibre_checks": fibre_checks(), "constant_ledger": ledger_checks()}
    args.output.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
