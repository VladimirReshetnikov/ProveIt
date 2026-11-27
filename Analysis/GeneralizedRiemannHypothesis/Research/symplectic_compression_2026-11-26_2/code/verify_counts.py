#!/usr/bin/env python3
"""Exact independent checks of the arbitrary symplectic compression law.

Python 3 standard library only.  The experiment enumerates group elements from
the defining pairings of symplectic bases; it does not sample, and it does not
use the proposed compression formula to construct any observed distribution.

The theorem covers every finite field.  This verifier enumerates prime fields
F_2 and F_3 only; no extension-field experiment is claimed.

Default cases:
  * every feasible source/target dimension and alternating-form type for
    Sp_2(F_2), Sp_4(F_2), and Sp_2(F_3);
  * every feasible type with a*b <= 9 for Sp_4(F_3).
For every selected type, every one of the q^(a*b) possible matrices is checked,
including matrices of zero probability.  An additional independent comparison
checks the Article's Lagrangian-target formula.

Usage: python3 verify_counts.py --check-calculator --output ../results.json
The optional --check-calculator flag also compares the separately implemented
compression_law.py calculator directly with every enumerated probability.
The final small experiments enumerate unrestricted maps and their alternating
Gram matrices to check the fixed-complement boundary law and its exact TV.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import product
import json
from pathlib import Path
import time


def pairing(x, y, q, m):
    return sum(x[i] * y[m + i] - x[m + i] * y[i] for i in range(m)) % q


def rank(matrix, q, ncols=None):
    """Gaussian elimination over a prime field, independent of count formulas."""
    if not matrix:
        return 0
    a = [[x % q for x in row] for row in matrix]
    width = len(a[0]) if ncols is None else ncols
    pivot_row = 0
    for col in range(width):
        pivot = next((i for i in range(pivot_row, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[pivot_row], a[pivot] = a[pivot], a[pivot_row]
        inv = pow(a[pivot_row][col], -1, q)
        a[pivot_row] = [(inv * x) % q for x in a[pivot_row]]
        for i in range(pivot_row + 1, len(a)):
            if a[i][col]:
                factor = a[i][col]
                a[i] = [(x - factor * y) % q for x, y in zip(a[i], a[pivot_row])]
        pivot_row += 1
        if pivot_row == len(a):
            break
    return pivot_row


def kernel_basis(matrix, q, ncols):
    a = [[x % q for x in row] for row in matrix]
    pivots = []
    pivot_row = 0
    for col in range(ncols):
        pivot = next((i for i in range(pivot_row, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[pivot_row], a[pivot] = a[pivot], a[pivot_row]
        inv = pow(a[pivot_row][col], -1, q)
        a[pivot_row] = [(inv * x) % q for x in a[pivot_row]]
        for i in range(len(a)):
            if i != pivot_row and a[i][col]:
                factor = a[i][col]
                a[i] = [(x - factor * y) % q for x, y in zip(a[i], a[pivot_row])]
        pivots.append(col)
        pivot_row += 1
        if pivot_row == len(a):
            break
    free = [j for j in range(ncols) if j not in pivots]
    basis = []
    for j in free:
        v = [0] * ncols
        v[j] = 1
        for i, col in enumerate(pivots):
            v[col] = (-a[i][j]) % q
        basis.append(v)
    return basis


def gram_form(dimension, half_rank, q):
    h = [[0] * dimension for _ in range(dimension)]
    for i in range(half_rank):
        h[2 * i][2 * i + 1] = 1
        h[2 * i + 1][2 * i] = q - 1
    return h


def canonical_indices(m, dimension, half_rank):
    indices = []
    for i in range(half_rank):
        indices.extend((i, m + i))
    indices.extend(range(half_rank, dimension - half_rank))
    assert len(indices) == dimension
    assert all(0 <= i < 2 * m for i in indices)
    return indices


def feasible_types(m):
    return [(d, r) for d in range(2 * m + 1)
            for r in range(d // 2 + 1) if d - r <= m]


def symplectic_group(q, m):
    """Enumerate all ordered symplectic bases by their defining pairings."""
    all_vectors = list(product(range(q), repeat=2 * m))
    zero = (0,) * (2 * m)

    def extend(available, xs, ys):
        if len(xs) == m:
            yield tuple(xs + ys)  # columns in e_1,...,e_m,f_1,...,f_m order
            return
        for x in available:
            if x == zero:
                continue
            for y in available:
                if pairing(x, y, q, m) != 1:
                    continue
                complement = [v for v in available
                              if pairing(v, x, q, m) == 0
                              and pairing(v, y, q, m) == 0]
                yield from extend(complement, xs + [x], ys + [y])

    result = list(extend(all_vectors, [], []))
    assert len(result) == len(set(result)), "Repeated group matrix"
    for columns in result:
        for i in range(2 * m):
            for j in range(2 * m):
                expected = (1 if j == m + i else -1 if i == m + j else 0) % q
                assert pairing(columns[i], columns[j], q, m) == expected
    return result


@lru_cache(maxsize=None)
def gaussian(q, n, k):
    if k < 0 or k > n or n < 0:
        return 0
    k = min(k, n - k)
    num = den = 1
    for i in range(k):
        num *= q ** (n - i) - 1
        den *= q ** (k - i) - 1
    value, remainder = divmod(num, den)
    assert remainder == 0
    return value


@lru_cache(maxsize=None)
def independent_frames(q, n, k):
    if k < 0 or k > n:
        return 0
    ans = 1
    for i in range(k):
        ans *= q ** n - q ** i
    return ans


@lru_cache(maxsize=None)
def embedding_count(q, m, d, r):
    """E_m(d,2r), the formula being checked (r denotes half the rank)."""
    if r < 0 or r > m or d < 2 * r or d - r > m:
        return 0
    ans = 1
    for i in range(r):
        ans *= (q ** (2 * (m - i)) - 1) * q ** (2 * (m - i) - 1)
    for i in range(d - 2 * r):
        ans *= q ** (2 * (m - r) - i) - q ** i
    return ans


@lru_cache(maxsize=None)
def transverse_count(q, z, p, t, d):
    """Positive Gaussian-binomial formula for the possible relation kernels."""
    w = z - p - t
    if min(z, p, t, d, w) < 0:
        return 0
    ans = 0
    for k in range(min(p, t, d) + 1):
        ell = d - k
        if ell > w:
            continue
        ans += (gaussian(q, t, k) * gaussian(q, w, ell)
                * q ** ((t - k + p) * ell) * independent_frames(q, p, k))
    return ans


@lru_cache(maxsize=None)
def probability_numerator(q, m, a, b, h, s, r, p, t):
    z = a + b - 2 * r
    assert z >= 0 and p + t <= z
    numerator = sum(transverse_count(q, z, p, t, d)
                    * embedding_count(q, m, a + b - d, r)
                    for d in range(z + 1))
    denominator = embedding_count(q, m, a, h) * embedding_count(q, m, b, s)
    assert denominator > 0
    return numerator, denominator


def invariants(q, a, b, h, s, c):
    H, S = gram_form(a, h, q), gram_form(b, s, q)
    mixed_gram = [S[i] + list(c[i * a:(i + 1) * a]) for i in range(b)]
    mixed_gram.extend([[-c[i * a + j] % q for i in range(b)] + H[j]
                       for j in range(a)])
    grank = rank(mixed_gram, q, a + b)
    assert grank % 2 == 0
    ct = [[c[i * a + j] for i in range(b)] for j in range(a)]
    cm = [list(c[i * a:(i + 1) * a]) for i in range(b)]
    p = b - rank(S + ct, q, b)
    t = a - rank(H + cm, q, a)
    return grank // 2, p, t


def observed_distribution(group, q, m, a, b, h, s):
    source = canonical_indices(m, a, h)
    target = canonical_indices(m, b, s)
    rows = [(m + i, 1) if i < m else (i - m, -1) for i in target]
    counts = Counter()
    for columns in group:
        c = tuple((sign * columns[j][row]) % q for row, sign in rows for j in source)
        counts[c] += 1
    return counts


def article_probability(q, m, h, c):
    """Independent special formula from Article spn:thm:lagrangian."""
    H = gram_form(m, h, q)
    cm = [list(c[i * m:(i + 1) * m]) for i in range(m)]
    K = kernel_basis(cm, q, m)
    k = len(K)
    t = m - rank(H + cm, q, m)
    for x in K:
        for y in K:
            if sum(x[i] * H[i][j] * y[j] for i in range(m) for j in range(m)) % q:
                return Fraction(0)
    constant = Fraction(1)
    for j in range(h + 1, m + 1):
        constant *= 1 - Fraction(1, q ** (2 * j))
    likelihood = Fraction(q ** (k * (k - 1) // 2), 1) / constant
    for j in range(k - t + 1, k + 1):
        likelihood *= 1 - Fraction(1, q ** j)
    return likelihood / q ** (m * m)


def rational_string(value):
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def verify_gram_boundary(q, a, c, boundary_calculator=None):
    """Count Y^T J_c Y directly, with no independence/rank assumptions on Y."""
    observed = Counter()
    for entries in product(range(q), repeat=2 * c * a):
        columns = [tuple(entries[i * a + j] for i in range(2 * c)) for j in range(a)]
        gram = tuple(pairing(columns[i], columns[j], q, c) for i in range(a) for j in range(a))
        observed[gram] += 1
    maps_count = q ** (2 * c * a)
    assert sum(observed.values()) == maps_count
    positions = [(i, j) for i in range(a) for j in range(i + 1, a)]
    all_forms = q ** len(positions)
    form_rank_counts = Counter()
    gram_mass_by_rank = {}
    empirical_twice_tv = Fraction(0)
    calculator_checks = 0
    for upper in product(range(q), repeat=len(positions)):
        G = [[0] * a for _ in range(a)]
        for (i, j), value in zip(positions, upper):
            G[i][j], G[j][i] = value, (-value) % q
        key = tuple(x for row in G for x in row)
        grank = rank(G, q, a)
        assert grank % 2 == 0
        r = grank // 2
        form_rank_counts[r] += 1
        F = sum(gaussian(q, a - 2 * r, k) * embedding_count(q, c, a - k, r)
                for k in range(a - 2 * r + 1))
        count = observed.get(key, 0)
        assert F == count, ("Gram-map count disagreement", q, a, c, G, F, count)
        gram_mass_by_rank[r] = Fraction(F, maps_count)
        empirical_twice_tv += abs(Fraction(count, maps_count) - Fraction(1, all_forms))
        if boundary_calculator is not None:
            assert boundary_calculator["count"](q, c, a, r) == count, (
                "Separate Gram calculator disagreement", q, a, c, G)
            calculator_checks += 1
    formula_twice_tv = Fraction(0)
    strata = []
    for r in range(a // 2 + 1):
        symplectic_order = q ** (r * r)
        for j in range(1, r + 1):
            symplectic_order *= q ** (2 * j) - 1
        form_count, remainder = divmod(gaussian(q, a, 2 * r)
                                       * independent_frames(q, 2 * r, 2 * r), symplectic_order)
        assert remainder == 0
        assert form_count == form_rank_counts[r], ("Alternating form count disagreement", q, a, r)
        formula_twice_tv += form_count * abs(gram_mass_by_rank[r] - Fraction(1, all_forms))
        if boundary_calculator is not None:
            assert boundary_calculator["form_count"](q, a, r) == form_count
        strata.append({"half_rank": r, "alternating_forms": form_count,
                       "probability_per_form": rational_string(gram_mass_by_rank[r])})
    assert formula_twice_tv == empirical_twice_tv
    delta = empirical_twice_tv / 2
    if boundary_calculator is not None:
        assert boundary_calculator["delta"](q, a, c) == delta, (
            "Separate boundary TV disagreement", q, a, c)
    return {"q": q, "source_dimension_a": a, "complement_half_dimension_c": c,
            "maps_enumerated": maps_count, "gram_matrices_checked": all_forms,
            "supported_gram_matrices": len(observed),
            "alternating_rank_strata_checked": len(strata),
            "calculator_comparisons": calculator_checks,
            "delta": rational_string(delta), "rank_strata": strata,
            "all_exact_checks_passed": True}


def verify_case(group, q, m, a, b, h, s, calculator=None):
    observed = observed_distribution(group, q, m, a, b, h, s)
    group_size = len(group)
    outcome_count = q ** (a * b)
    normalization_numerator = 0
    distinct_invariants = set()
    rank_law = Counter()
    total_variation_twice = Fraction(0)
    article_checks = 0
    plane_case = a == 2 and h == 1 and b == 2 * s and s >= 1
    uniform_rank_counts = Counter()
    plane_checks = 0
    calculator_checks = 0
    calculator_H = gram_form(a, h, q)
    calculator_S = gram_form(b, s, q)
    for c in product(range(q), repeat=a * b):
        r, p, t = invariants(q, a, b, h, s, c)
        distinct_invariants.add((r, p, t))
        numerator, denominator = probability_numerator(q, m, a, b, h, s, r, p, t)
        count = observed.get(c, 0)
        assert count * denominator == numerator * group_size, (
            "Probability disagreement", q, m, a, b, h, s, c,
            (r, p, t), count, group_size, numerator, denominator)
        assert (count > 0) == (r + max(p, t) <= m), (
            "Support disagreement", q, m, a, b, h, s, c, (r, p, t))
        if calculator is not None:
            calculator_C = [list(c[i * a:(i + 1) * a]) for i in range(b)]
            assert calculator(q, m, calculator_S, calculator_H, calculator_C) == Fraction(count, group_size), (
                "Separate calculator disagreement", q, m, a, b, h, s, c)
            calculator_checks += 1
        normalization_numerator += numerator
        total_variation_twice += abs(Fraction(count, group_size) - Fraction(1, outcome_count))
        if count:
            cm = [list(c[i * a:(i + 1) * a]) for i in range(b)]
            rank_law[rank(cm, q, a)] += count
        if plane_case:
            cm = [list(c[i * a:(i + 1) * a]) for i in range(b)]
            uniform_rank_counts[rank(cm, q, a)] += 1
            x, y = Fraction(1, q ** (2 * s)), Fraction(1, q ** (2 * (m - s)))
            alpha = sum(c[(2 * i) * 2] * c[(2 * i + 1) * 2 + 1]
                        - c[(2 * i) * 2 + 1] * c[(2 * i + 1) * 2]
                        for i in range(s)) % q
            likelihood = ((1 + (q - 1) * y) if alpha == 1 else (1 - y)) / (1 - x * y)
            assert Fraction(count, group_size) == likelihood / outcome_count, (
                "Plane likelihood disagreement", q, m, s, c, alpha)
            plane_checks += 1
        if a == b == m and s == 0:
            assert Fraction(numerator, denominator) == article_probability(q, m, h, c), (
                "Article Lagrangian reduction disagreement", q, m, h, c)
            article_checks += 1
    assert normalization_numerator == denominator, "Normalization failure"
    assert sum(observed.values()) == group_size
    assert sum(rank_law.values()) == group_size
    answer = {
        "q": q, "ambient_half_dimension": m, "a": a, "b": b,
        "source_form_half_rank_h": h, "target_form_half_rank_s": s,
        "matrices_checked": outcome_count,
        "supported_matrices": len(observed),
        "zero_probability_matrices_checked": outcome_count - len(observed),
        "distinct_invariant_triples": len(distinct_invariants),
        "article_lagrangian_comparisons": article_checks,
        "plane_likelihood_comparisons": plane_checks,
        "calculator_comparisons": calculator_checks,
        "rank_probabilities": {str(k): rational_string(Fraction(v, group_size))
                               for k, v in sorted(rank_law.items())},
        "total_variation_from_uniform": rational_string(total_variation_twice / 2),
        "all_exact_checks_passed": True,
    }
    if plane_case:
        full_tv = y * (1 - x) * (q - 1 + x) / (q * (1 - x * y))
        rank_tv = y * (1 - x) * x * (q + 1 - q * x) / (1 - x * y)
        measured_rank_tv = sum(abs(Fraction(rank_law.get(k, 0), group_size)
                                   - Fraction(uniform_rank_counts.get(k, 0), outcome_count))
                               for k in range(3)) / 2
        assert total_variation_twice / 2 == full_tv, "Plane full-distance disagreement"
        assert measured_rank_tv == rank_tv, "Plane rank-distance disagreement"
        answer["plane_specialization"] = {
            "target_half_dimension_s": s,
            "complement_half_dimension_c": m - s,
            "full_total_variation": rational_string(full_tv),
            "rank_total_variation": rational_string(rank_tv),
            "all_exact_checks_passed": True,
        }
    return answer


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "results.json")
    parser.add_argument("--quick", action="store_true",
                        help="omit the 51,840-element Sp_4(F_3) experiment")
    parser.add_argument("--check-calculator", action="store_true",
                        help="also compare the separate compression_law.py calculator with observed group counts")
    args = parser.parse_args()
    calculator = None
    boundary_calculator = None
    if args.check_calculator:
        from compression_law import (compression_probability, alternating_form_count,
                                     gram_map_count, gram_boundary_delta)
        calculator = compression_probability
        boundary_calculator = {"count": gram_map_count, "form_count": alternating_form_count,
                               "delta": gram_boundary_delta}
    started = time.monotonic()
    settings = [(2, 1, None), (2, 2, None), (3, 1, None)]
    if not args.quick:
        settings.append((3, 2, 9))
    group_summaries, cases = [], []
    for q, m, maximum_entries in settings:
        group = symplectic_group(q, m)
        expected_order = q ** (m * m)
        for i in range(1, m + 1):
            expected_order *= q ** (2 * i) - 1
        assert len(group) == expected_order
        print(f"Enumerated Sp_{2*m}(F_{q}): {len(group)} distinct defining-relation matrices", flush=True)
        selected = [(a, b, h, s) for a, h in feasible_types(m)
                    for b, s in feasible_types(m)
                    if maximum_entries is None or a * b <= maximum_entries]
        current = [verify_case(group, q, m, a, b, h, s, calculator) for a, b, h, s in selected]
        cases.extend(current)
        group_summaries.append({
            "q": q, "ambient_half_dimension": m, "enumerated_group_order": len(group),
            "cases": len(current), "maximum_matrix_entries": maximum_entries,
            "matrices_checked": sum(x["matrices_checked"] for x in current),
            "zero_probability_matrices_checked": sum(x["zero_probability_matrices_checked"] for x in current),
            "all_exact_checks_passed": True,
        })
        print(f"  Passed {len(current)} form/dimension cases and "
              f"{sum(x['matrices_checked'] for x in current)} complete outcome comparisons", flush=True)
    boundary_results = [verify_gram_boundary(q, a, c, boundary_calculator)
                        for q, a, c in [(2, 2, 1), (2, 3, 1), (2, 4, 1),
                                        (3, 2, 1), (2, 3, 0)]]
    print(f"  Passed {len(boundary_results)} unrestricted Gram-map boundary cases", flush=True)
    result = {
        "verification": "Exact exhaustive enumeration over prime fields F_2 and F_3",
        "arithmetic": "Python integers and fractions.Fraction; no floating-point probability comparisons",
        "scope": "Canonical representatives of every feasible form type in the stated dimensions; every matrix outcome in each selected case",
        "not_claimed": "Computational checks are finite evidence, not a proof for general dimensions or extension fields",
        "summary": {
            "all_exact_checks_passed": True,
            "groups_enumerated": len(group_summaries),
            "total_group_elements_enumerated": sum(x["enumerated_group_order"] for x in group_summaries),
            "form_dimension_cases": len(cases),
            "matrix_outcome_comparisons": sum(x["matrices_checked"] for x in cases),
            "zero_probability_outcome_comparisons": sum(x["zero_probability_matrices_checked"] for x in cases),
            "article_lagrangian_comparisons": sum(x["article_lagrangian_comparisons"] for x in cases),
            "plane_likelihood_comparisons": sum(x["plane_likelihood_comparisons"] for x in cases),
            "plane_distance_comparisons": 2 * sum("plane_specialization" in x for x in cases),
            "calculator_comparisons": sum(x["calculator_comparisons"] for x in cases),
            "boundary_cases": len(boundary_results),
            "boundary_maps_enumerated": sum(x["maps_enumerated"] for x in boundary_results),
            "boundary_gram_matrix_comparisons": sum(x["gram_matrices_checked"] for x in boundary_results),
            "boundary_rank_strata_comparisons": sum(x["alternating_rank_strata_checked"] for x in boundary_results),
            "boundary_calculator_comparisons": sum(x["calculator_comparisons"] for x in boundary_results),
            "boundary_delta_comparisons": len(boundary_results),
            "elapsed_seconds": round(time.monotonic() - started, 3),
        },
        "groups": group_summaries,
        "cases": cases,
        "boundary_cases": boundary_results,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result["summary"], indent=2), flush=True)
    print(f"Saved {args.output}", flush=True)


if __name__ == "__main__":
    main()
