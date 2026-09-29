#!/usr/bin/env python3
"""Exact finite checks accompanying Specialization-Safe Radical Solvers.

Python 3.10+ and SymPy are required. No numerical root matching is used.
This is a reproducibility/checking script, not a Lean or Rocq proof.

Run: python verify_results.py --out certificates
"""
from __future__ import annotations

import argparse
import csv
import json
import platform
import sys
from collections import Counter
from fractions import Fraction
from itertools import combinations
from pathlib import Path
from typing import Iterable
import sympy as sp

T, X, Y = sp.symbols("T X Y")
Pair = tuple[tuple[int, ...], tuple[int, ...]]


def canonical_pair(a: Iterable[int], b: Iterable[int]) -> Pair:
    aa, bb = tuple(sorted(a)), tuple(sorted(b))
    return tuple(sorted((aa, bb)))  # type: ignore[return-value]


def affine_orbit(pair: Pair, p: int) -> set[Pair]:
    return {
        canonical_pair(((a*i+b) % p for i in pair[0]),
                       ((a*i+b) % p for i in pair[1]))
        for a in range(1, p) for b in range(p)
    }


def difference_polynomial(pair: Pair) -> sp.Expr:
    return sum(T**i for i in pair[0]) - sum(T**i for i in pair[1])


def norm_matrix(q: sp.Expr, p: int) -> sp.Matrix:
    """Integer multiplication matrix of q in Z[T]/Phi_p, in powers of T."""
    phi = sp.Poly(sum(T**i for i in range(p)), T, domain=sp.ZZ)
    columns = []
    for j in range(p-1):
        r = sp.rem(sp.Poly(q*T**j, T, domain=sp.ZZ), phi)
        columns.append([r.nth(i) for i in range(p-1)])
    return sp.Matrix.hstack(*(sp.Matrix(c) for c in columns))


EXPECTED = {
    (5, 2): {5: 40, 25: 5},
    (7, 2): {7: 147, 49: 21, 56: 42},
    (7, 3): {7: 357, 49: 63, 56: 126, 203: 42, 343: 7},
}


def check_norms(out: Path) -> dict:
    details = []
    summaries = {}
    all_pair_count = 0
    for (p, k), expected in EXPECTED.items():
        subsets = list(combinations(range(p), k))
        pairs = set(combinations(subsets, 2))
        phi = sum(T**i for i in range(p))
        norms = {}
        for pair in sorted(pairs):
            q = difference_polynomial(pair)
            n = abs(int(sp.resultant(phi, q, T)))
            if not n:
                raise AssertionError((p, k, pair, "zero resultant"))
            norms[pair] = n
        counts = dict(sorted(Counter(norms.values()).items()))
        assert counts == expected, (p, k, counts)
        todo = set(pairs)
        rows = []
        while todo:
            pair = min(todo)
            orbit = affine_orbit(pair, p)
            assert orbit <= todo, "Orbits must partition the pair set."
            n = norms[pair]
            assert all(norms[s] == n for s in orbit)
            matrix = norm_matrix(difference_polynomial(pair), p)
            assert abs(int(matrix.det(method="bareiss"))) == n
            row = {"p": p, "k": k, "A": list(pair[0]), "B": list(pair[1]),
                   "orbit_size": len(orbit), "norm": n,
                   "multiplication_matrix": [[int(v) for v in row]
                                             for row in matrix.tolist()]}
            rows.append(row)
            details.append(row)
            todo.difference_update(orbit)
        assert sum(row["orbit_size"] for row in rows) == len(pairs)
        primes = sorted({int(l) for n in norms.values() for l in sp.factorint(n)})
        summaries[f"p{p}_k{k}"] = {
            "subsets": len(subsets), "pairs": len(pairs),
            "orbits": len(rows), "norm_counts": counts, "bad_primes": primes}
        all_pair_count += len(pairs)
    (out / "cyclotomic_norm_certificates.json").write_text(
        json.dumps(details, indent=2) + "\n", encoding="utf-8")
    with (out / "affine_orbits.csv").open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["p", "k", "A", "B", "orbit_size", "norm"])
        for r in details:
            w.writerow([r["p"], r["k"], "".join(map(str, r["A"])),
                        "".join(map(str, r["B"])), r["orbit_size"], r["norm"]])
    return {"resultants_checked": all_pair_count,
            "independent_determinants_checked": len(details), "cases": summaries}


def gf8_mul(a: int, b: int) -> int:
    """F_2[z]/(z^3+z+1), represented by three-bit integers."""
    result = 0
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
        if a & 8:
            a ^= 0b1011
    return result


def check_finite_fields(out: Path) -> dict:
    pows29 = [pow(23, i, 29) for i in range(7)]
    assert len(set(pows29)) == 7 and pow(23, 7, 29) == 1
    assert (sum(pows29[i] for i in (0, 1, 2)) -
            sum(pows29[i] for i in (3, 4, 6))) % 29 == 0
    sums29 = Counter(sum(pows29[i] for i in a) % 29
                     for a in combinations(range(7), 3))
    seventh_counts = Counter()
    for value, count in sums29.items():
        seventh_counts[pow(value, 7, 29)] += count
    assert dict(seventh_counts) == {1: 7, 12: 14, 17: 7, 28: 7}
    assert all(sums29[c] == (2 if pow(c, 7, 29) == 12 else 1)
               for c in sums29)
    assert sp.Poly((Y-1)*(Y-12)*(Y-17)*(Y-28) - (Y**4-1),
                   Y, modulus=29).is_zero
    # A repaired elementary-symmetric subset descriptor has three independent
    # alpha-coefficients; check all 35 coefficient vectors are distinct.
    vectors = set()
    for subset in combinations(pows29, 3):
        a, b, c = subset
        vectors.add(((a+b+c) % 29, (a*b+a*c+b*c) % 29, (a*b*c) % 29))
    assert len(vectors) == 35
    pows8 = [1]
    for _ in range(6):
        pows8.append(gf8_mul(pows8[-1], 2))
    assert gf8_mul(pows8[-1], 2) == 1 and len(set(pows8)) == 7
    sums8 = Counter(pows8[a] ^ pows8[b] ^ pows8[c]
                    for a, b, c in combinations(range(7), 3))
    assert sums8[0] == 7
    assert all(sums8[i] == 4 for i in range(1, 8))
    sums7 = Counter(sum(a) % 7 for a in combinations(range(7), 3))
    assert all(sums7[i] == 5 for i in range(7))
    sums5 = Counter(sum(a) % 5 for a in combinations(range(5), 2))
    assert all(sums5[i] == 2 for i in range(5))
    result = {"F29_primitive_root": 23, "F29_powers": pows29,
              "F29_triple_sums": dict(sorted(sums29.items())),
              "F29_seventh_power_counts": dict(sorted(seventh_counts.items())),
              "F29_repaired_distinct_vectors": len(vectors),
              "F8_powers": pows8, "F8_triple_sums": dict(sorted(sums8.items())),
              "F7_index_sums": dict(sorted(sums7.items())),
              "F5_index_sums": dict(sorted(sums5.items()))}
    (out / "finite_field_witnesses.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8")
    return {"finite_field_witnesses": 4, "repaired_F29_vectors": 35}


# Elements of Q[a,z]/(a^p-2, Phi_p(z)); coefficients are exact Fractions.
Elem = dict[tuple[int, int], Fraction]


def monomial(p: int, a: int, z: int, coefficient=Fraction(1)) -> Elem:
    q, a = divmod(a, p)
    coefficient = Fraction(coefficient) * Fraction(2)**q
    z %= p
    if not coefficient:
        return {}
    if z == p-1:
        return {(a, j): -coefficient for j in range(p-1)}
    return {(a, z): coefficient}


def plus(*items: Elem) -> Elem:
    out: Elem = {}
    for item in items:
        for index, coefficient in item.items():
            out[index] = out.get(index, Fraction(0)) + coefficient
    return {k: v for k, v in out.items() if v}


def scale(item: Elem, coefficient) -> Elem:
    c = Fraction(coefficient)
    return {k: v*c for k, v in item.items() if v*c}


def times(p: int, a: Elem, b: Elem) -> Elem:
    return plus(*(monomial(p, i+k, j+l, c*d)
                  for (i, j), c in a.items() for (k, l), d in b.items()))


def power(p: int, a: Elem, n: int) -> Elem:
    assert n >= 0
    result = monomial(p, 0, 0)
    while n:
        if n & 1:
            result = times(p, result, a)
        a = times(p, a, a)
        n >>= 1
    return result


def check_fourier_and_examples(out: Path) -> dict:
    supports = pivots = entries = fourier_modes = 0
    for p in (5, 7):
        for mask in range(1, 1 << (p-1)):
            support = [j for j in range(1, p) if mask & (1 << (j-1))]
            roots = [plus(*(monomial(p, k, i*k) for k in support))
                     for i in range(p)]
            modes = [plus(*(times(p, monomial(p, 0, -i*j), roots[i])
                            for i in range(p))) for j in range(p)]
            for j in range(p):
                assert modes[j] == (monomial(p, j, 0, p) if j in support else {})
                fourier_modes += 1
            for pivot in support:
                invers = pow(pivot, -1, p)
                pivot_mode = modes[pivot]
                a = power(p, pivot_mode, p)
                assert a == monomial(p, 0, 0, p**p * 2**pivot)
                for r in range(p):
                    rho = times(p, monomial(p, 0, r), pivot_mode)
                    assert power(p, rho, p) == a
                    for i in range(p):
                        recovered = {}
                        for k in support:
                            e = (invers*k) % p
                            assert 1 <= e <= p-1
                            c = Fraction(p)**(1-e) * Fraction(2)**((k-pivot*e)//p)
                            term = times(p, monomial(p, 0, i*k, c), power(p, rho, e))
                            recovered = plus(recovered, term)
                        recovered = scale(recovered, Fraction(1, p))
                        assert recovered == roots[(i+r*invers) % p]
                        entries += 1
                pivots += 1
            supports += 1
    examples = []
    for p in (5, 7):
        for support in ((1, 2), (2, 3), tuple(range(1, p))):
            polynomial = sp.Poly(sp.resultant(X**p-2,
                                             Y-sum(X**j for j in support), X), Y)
            assert polynomial.degree() == p and polynomial.LC() == 1
            assert polynomial.is_irreducible
            examples.append({"p": p, "support": list(support),
                             "polynomial": str(polynomial.as_expr())})
    (out / "worked_polynomials.json").write_text(
        json.dumps(examples, indent=2) + "\n", encoding="utf-8")
    return {"support_patterns": supports, "Fourier_modes_checked": fourier_modes,
            "pivot_charts_checked": pivots, "reconstructed_root_entries": entries,
            "exact_irreducible_worked_polynomials": len(examples)}


def check_affine_factor_patterns(out: Path) -> dict:
    expected = {1: [7, 7, 7, 7, 7], 2: [7, 7, 7, 14],
                3: [7, 7, 21], 6: [14, 21]}
    generators = {1: 1, 2: 6, 3: 2, 6: 3}
    results = {}
    for d, generator in generators.items():
        multipliers = {pow(generator, i, 7) for i in range(d)}
        assert len(multipliers) == d
        remaining = set(combinations(range(7), 3))
        sizes = []
        while remaining:
            subset = min(remaining)
            current = {tuple(sorted((a*i+b) % 7 for i in subset))
                       for a in multipliers for b in range(7)}
            assert current <= remaining
            remaining.difference_update(current)
            sizes.append(len(current))
        assert sorted(sizes) == expected[d]
        results[str(d)] = sorted(sizes)
    (out / "affine_factor_patterns.json").write_text(
        json.dumps(results, indent=2) + "\n", encoding="utf-8")
    return {"affine_septic_factor_patterns": len(results)}


def check_septic_rigidity(out: Path) -> dict:
    # Evaluate every possible relation on all six primitive characters.
    # F29 contains mu_7; in characteristic two use the explicit F8 model.
    pows8 = [1]
    for _ in range(6):
        pows8.append(gf8_mul(pows8[-1], 2))
    counts2 = {}
    counts29 = Counter()
    checked2 = checked29 = 0
    for k in (2, 3):
        counts = Counter()
        subsets = list(combinations(range(7), k))
        for left, right in combinations(subsets, 2):
            zeros2 = []
            for j in range(1, 7):
                value = 0
                for i in left+right:
                    value ^= pows8[(i*j) % 7]
                if value == 0:
                    zeros2.append(j)
            assert zeros2 in ([], [1, 2, 4], [3, 5, 6])
            counts[len(zeros2)] += 1
            checked2 += 1
            if k == 3:
                zeros29 = [j for j in range(1, 7)
                           if (sum(pow(23, i*j, 29) for i in left)-
                               sum(pow(23, i*j, 29) for i in right)) % 29 == 0]
                assert len(zeros29) in (0, 1)
                counts29[len(zeros29)] += 1
                checked29 += 1
        assert dict(counts) == {2: {0: 168, 3: 42},
                                3: {0: 469, 3: 126}}[k]
        counts2[str(k)] = dict(sorted(counts.items()))
    assert dict(counts29) == {0: 553, 1: 42}
    data = {"F2_primitive_character_zero_counts": counts2,
            "F29_primitive_character_zero_counts": dict(sorted(counts29.items())),
            "F2_checks": checked2, "F29_checks": checked29}
    (out / "septic_rigidity_checks.json").write_text(
        json.dumps(data, indent=2) + "\n", encoding="utf-8")
    return {"septic_rigidity_character_patterns": checked2+checked29}


def main() -> None:
    if not __debug__:
        raise RuntimeError("Run without -O; assertions are part of the checker.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=Path("certificates"))
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    report = {"status": "PASS", "python": platform.python_version(),
              "sympy": sp.__version__, "arithmetic": "exact integer and rational"}
    report.update(check_norms(args.out))
    print("Cyclotomic norm and orbit checks passed.", flush=True)
    report.update(check_finite_fields(args.out))
    print("Finite-field witnesses and repair passed.", flush=True)
    report.update(check_fourier_and_examples(args.out))
    report.update(check_affine_factor_patterns(args.out))
    report.update(check_septic_rigidity(args.out))
    (args.out / "verification_report.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, OSError, ValueError) as exc:
        print(f"Verification failed: {exc}", file=sys.stderr)
        raise
