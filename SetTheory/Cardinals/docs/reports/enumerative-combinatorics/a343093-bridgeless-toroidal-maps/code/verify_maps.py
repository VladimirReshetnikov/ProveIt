#!/usr/bin/env python3
"""Independent exact checks for the A343093 map-enumeration section.

Run with Python 3.  SymPy is used for algebraic checks, and mpmath for
asymptotic diagnostics.  The exhaustive permutation check uses only the
standard library.  No network access or downloaded OEIS data is needed.

The 20-term reference prefix was read from https://oeis.org/A343093 on
2026-10-04 UTC.  The identity is proved in the accompanying article;
finite agreement is an implementation check, not a substitute for proof.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
from pathlib import Path


REFERENCE = [
    1, 14, 159, 1680, 17147, 171612, 1696491, 16631840,
    162090756, 1572801142, 15210259585, 146710561296,
    1412132981778, 13569013500024, 130199055578307,
    1247825314752768, 11947157409479180, 114288613130155608,
    1092495810452593564, 10436544808441964352,
]


def convolution(n: int) -> int:
    """Cauchy-product formula, using the integral binomial factors."""
    return sum(math.comb(4*k-1, k-1)*math.comb(4*(n-k)-1, n-k-1)
               for k in range(1, n))


def lagrange(n: int) -> int:
    """The separate single-sum formula from Lagrange inversion."""
    if n < 2:
        return 0
    numerator = sum((j+1)*(j+2)*3**j*math.comb(4*n, n-2-j)
                    for j in range(n-1))
    answer, remainder = divmod(numerator, n)
    assert remainder == 0
    return answer


def cycle_data(perm: tuple[int, ...]) -> tuple[int, list[int]]:
    labels = [-1]*len(perm)
    number = 0
    for dart in range(len(perm)):
        if labels[dart] >= 0:
            continue
        current = dart
        while labels[current] < 0:
            labels[current] = number
            current = perm[current]
        number += 1
    return number, labels


def connected(vertices: int, edges: list[tuple[int, int]],
              omit: int = -1) -> bool:
    adjacency = [[] for _ in range(vertices)]
    for edge, (v, w) in enumerate(edges):
        if edge == omit:
            continue
        adjacency[v].append(w)
        adjacency[w].append(v)
    seen = {0}
    stack = [0]
    while stack:
        v = stack.pop()
        for w in adjacency[v]:
            if w not in seen:
                seen.add(w)
                stack.append(w)
    return len(seen) == vertices


def enumerate_maps(n: int) -> dict[str, object]:
    """Brute-force rotation systems with fixed edge pairing and root 0.

    alpha(d)=d xor 1.  Enumerating vertex permutations labels all darts.
    The root-preserving centralizer of alpha has size 2^(n-1)*(n-1)!;
    it acts freely on connected rooted rotation systems.
    """
    all_by_genus: dict[int, int] = {}
    free_by_genus: dict[int, int] = {}
    for sigma in itertools.permutations(range(2*n)):
        vertices, vertex_of = cycle_data(sigma)
        edges = [(vertex_of[2*j], vertex_of[2*j+1]) for j in range(n)]
        if not connected(vertices, edges):
            continue
        phi = tuple(sigma[d ^ 1] for d in range(2*n))
        faces, _ = cycle_data(phi)
        twice_genus = 2-vertices+n-faces
        assert twice_genus >= 0 and twice_genus % 2 == 0
        genus = twice_genus//2
        all_by_genus[genus] = all_by_genus.get(genus, 0)+1
        if all(connected(vertices, edges, omit=j) for j in range(n)):
            free_by_genus[genus] = free_by_genus.get(genus, 0)+1
    factor = 2**(n-1)*math.factorial(n-1)
    for counts in (all_by_genus, free_by_genus):
        for genus, value in counts.items():
            quotient, remainder = divmod(value, factor)
            assert remainder == 0
            counts[genus] = quotient
    assert free_by_genus.get(1, 0) == convolution(n)
    planar = 2*3**n*math.factorial(2*n)//(
        math.factorial(n)*math.factorial(n+2))
    assert all_by_genus.get(0, 0) == planar
    return {
        "edges": n,
        "permutations_examined": math.factorial(2*n),
        "labeling_factor": factor,
        "all_rooted_maps_by_genus": all_by_genus,
        "bridgeless_rooted_maps_by_genus": free_by_genus,
    }


def symbolic_checks() -> list[str]:
    import sympy as s
    u, r, t, w = s.symbols("u r t w")
    z = u/(1+3*u)**2
    m0 = (1-u)*(1+3*u)
    m1 = u*u*(1+3*u)/((1+u)*(1-3*u)**2)
    q = 1-z*m0
    t0 = z/q**2
    b0 = s.factor(m0-1-z*m0**2)
    assert s.cancel(t0-u/(1+u)**4) == 0
    assert s.expand(b0-(u-u*u-u**3)) == 0
    derivative = s.cancel(s.diff(b0, u)/s.diff(t0, u))
    assert s.cancel(derivative-(1+u)**6) == 0
    b1 = s.factor(m1*(1-2*z*m0-2*z*z*derivative/q**3))
    assert s.cancel(b1-u*u/(1-3*u)**2) == 0

    a = u*u/(1-3*u)**2
    e = t+(96*t-9)*a+(256*t-27)*a*a
    o = (16*t-1)+(256*t-27)*a
    assert s.factor((e*e-a*o*o).subs(t, u/(1+u)**4)) == 0

    # Exact rational/radical coefficients, independently substituted into
    # the rational inverse relation.  This avoids numerical branch choices.
    inverse = (s.sqrt(6)*w/3+w*w/9+19*s.sqrt(6)*w**3/648
               -11*w**4/972+677*s.sqrt(6)*w**5/93312
               -595*w**6/52488)
    delta_squared = s.series(
        1-16*(1-r)*(1+r)**3/(r+2)**4, r, 0, 8).removeO()
    residual = s.series(delta_squared.subs(r, inverse), w, 0, 8)
    assert s.simplify(residual.removeO()-w*w) == 0
    result = s.series((1-inverse)**2/(36*inverse**2), w, 0, 3).removeO()
    expected = (1/(24*w*w)-7*s.sqrt(6)/(216*w)+s.Rational(83, 2592)
                +161*s.sqrt(6)*w/46656-s.Rational(1249, 279936)*w*w)
    assert s.simplify(result-expected) == 0
    return [
        "planar substitution and bridge identity",
        "genus-one derivative identity",
        "quartic elimination polynomial",
        "Puiseux inverse residual through degree 7",
        "Puiseux expansion through w^2",
    ]


def asymptotic_diagnostics() -> list[dict[str, object]]:
    import mpmath as mp
    mp.mp.dps = 70
    rho = mp.mpf(27)/256
    c1 = -7*mp.sqrt(6)/(216*mp.sqrt(mp.pi))
    c3 = 217*mp.sqrt(6)/(93312*mp.sqrt(mp.pi))
    rows = []
    for n in (32, 128, 512):
        scaled = mp.mpf(convolution(n))*rho**n
        approximate = mp.mpf(1)/24+c1/mp.sqrt(n)+c3/n**mp.mpf("1.5")
        rows.append({
            "n": n,
            "rho_power_n_times_b_n": mp.nstr(scaled, 35),
            "three_term_scaled_approximation": mp.nstr(approximate, 35),
            "error_times_n_to_5_over_2": mp.nstr(
                (scaled-approximate)*n**mp.mpf("2.5"), 25),
        })
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exhaustive-max-n", type=int, default=4)
    parser.add_argument("--formula-max-n", type=int, default=100)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parent.parent/
                        "verification"/"maps_checks.json")
    args = parser.parse_args()
    if not 1 <= args.exhaustive_max_n <= 5:
        parser.error("exhaustive bound must be between 1 and 5")
    assert [convolution(n) for n in range(2, 22)] == REFERENCE
    assert [lagrange(n) for n in range(2, 22)] == REFERENCE
    for n in range(2, args.formula_max_n+1):
        assert convolution(n) == lagrange(n)
    result = {
        "status": "passed",
        "reference_url": "https://oeis.org/A343093",
        "reference_retrieved_utc": "2026-10-04",
        "oeis_reference_terms_checked": len(REFERENCE),
        "two_exact_formulas_compared_through_n": args.formula_max_n,
        "exhaustive_rotation_system_checks": [
            enumerate_maps(n) for n in range(1, args.exhaustive_max_n+1)],
        "symbolic_checks": symbolic_checks(),
        "asymptotic_diagnostics_not_proofs": asymptotic_diagnostics(),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
