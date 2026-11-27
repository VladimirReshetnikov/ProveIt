#!/usr/bin/env python3
"""Independent exhaustive checks for arbitrary symplectic compressions.

Standard-library only.  Run:
    python3 code/verify_exhaustive.py

The experiment enumerates actual independent vector frames in finite symplectic
spaces, groups them by their alternating Gram matrix, and observes every cross
Gram matrix against a fixed frame.  It then compares the observed counts with
the theorem's separate combined-Gram counting formula.  The intersection
dimension is checked jointly, including outcomes having probability zero.

The nonprime field F_4 is implemented as F_2[x]/(x^2+x+1), with 0,1,x,x+1
encoded by 0,1,2,3.  No integer-modulo-4 arithmetic is used.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from fractions import Fraction
from functools import lru_cache
from itertools import product
import json
from pathlib import Path
import time


class Field:
    def __init__(self, q: int):
        if q not in (2, 3, 4):
            raise ValueError("The exhaustive checker implements q=2,3,4.")
        self.q = q
        if q == 4:
            self.add = [[x ^ y for y in range(q)] for x in range(q)]

            def mul4(x, y):
                z = 0
                while y:
                    if y & 1:
                        z ^= x
                    x <<= 1
                    if x & 4:
                        x ^= 7
                    y >>= 1
                return z

            self.mul = [[mul4(x, y) for y in range(q)] for x in range(q)]
        else:
            self.add = [[(x + y) % q for y in range(q)] for x in range(q)]
            self.mul = [[(x * y) % q for y in range(q)] for x in range(q)]
        self.neg = [next(y for y in range(q) if self.add[x][y] == 0)
                    for x in range(q)]
        self.inv = [0] + [next(y for y in range(1, q)
                              if self.mul[x][y] == 1)
                         for x in range(1, q)]

    def rank(self, rows):
        if not rows:
            return 0
        a = [list(row) for row in rows]
        n, m = len(a), len(a[0])
        r = 0
        for j in range(m):
            pivot = next((i for i in range(r, n) if a[i][j]), None)
            if pivot is None:
                continue
            a[r], a[pivot] = a[pivot], a[r]
            c = self.inv[a[r][j]]
            a[r] = [self.mul[c][v] for v in a[r]]
            for i in range(r + 1, n):
                c = self.neg[a[i][j]]
                if c:
                    a[i] = [self.add[v][self.mul[c][w]]
                            for v, w in zip(a[i], a[r])]
            r += 1
            if r == n:
                break
        return r

    def pairing(self, x, y):
        z = 0
        for i in range(0, len(x), 2):
            z = self.add[z][self.mul[x[i]][y[i + 1]]]
            z = self.add[z][self.neg[self.mul[x[i + 1]][y[i]]]]
        return z

    def gram(self, frame):
        return tuple(tuple(self.pairing(x, y) for y in frame) for x in frame)

    def cross(self, x, y):
        return tuple(tuple(self.pairing(v, w) for w in y) for v in x)


@lru_cache(None)
def qbin(q, n, k):
    if n < 0 or k < 0 or k > n:
        return 0
    k = min(k, n - k)
    z = 1
    for i in range(k):
        z = z * (q ** (n - i) - 1) // (q ** (i + 1) - 1)
    return z


@lru_cache(None)
def gl(q, d):
    z = 1
    for i in range(d):
        z *= q ** d - q ** i
    return z


@lru_cache(None)
def embeddings(q, N, d, s):
    """Injective maps of a fixed d-form of rank 2s into dimension 2N."""
    if min(N, d, s) < 0 or 2 * s > d or d - s > N:
        return 0
    z = 1
    for i in range(s):
        z *= (q ** (2 * (N - i)) - 1) * q ** (2 * (N - i) - 1)
    for i in range(d - 2 * s):
        z *= q ** (2 * (N - s) - i) - q ** i
    return z


@lru_cache(None)
def avoiding_subspaces(q, u, v, c, d):
    z = 0
    for j in range(min(u, v, d) + 1):
        z += (qbin(q, u, j) * qbin(q, v, j) * gl(q, j)
              * qbin(q, c, d - j) * q ** ((d - j) * (u + v - j)))
    return z


def predicted_joint(field, N, F, H, M):
    """Counts of pairs (X,Y), indexed by dim(im X intersect im Y)."""
    q, a, b = field.q, len(F), len(H)
    mt = tuple(zip(*M)) if a else tuple(() for _ in range(b))
    G = [list(F[i]) + list(M[i]) for i in range(a)]
    G += [[field.neg[M[j][i]] for j in range(a)] + list(H[i])
          for i in range(b)]
    rg = field.rank(G)
    assert rg % 2 == 0
    s, r = rg // 2, a + b - rg
    u = a - field.rank(list(F) + list(mt))
    v = b - field.rank(list(H) + list(M))
    c = r - u - v
    assert c >= 0
    counts = {d: avoiding_subspaces(q, u, v, c, d)
                 * embeddings(q, N, a + b - d, s)
              for d in range(r + 1)}
    return counts, (s, u, v, c)


def enumerate_frames(field, N, d):
    """Enumerate actual independent frames, without using any count formula."""
    q, dimension = field.q, 2 * N
    vectors = list(product(range(q), repeat=dimension))
    zero = (0,) * dimension
    groups = defaultdict(list)

    def visit(frame, span):
        if len(frame) == d:
            groups[field.gram(frame)].append(frame)
            return
        for vector in vectors:
            if vector in span:
                continue
            new_span = {
                tuple(field.add[x][field.mul[t][y]]
                      for x, y in zip(w, vector))
                for w in span for t in range(q)
            }
            visit(frame + (vector,), new_span)

    visit((), {zero})
    return groups


def all_matrices(q, a, b):
    for values in product(range(q), repeat=a * b):
        yield tuple(tuple(values[i * b:(i + 1) * b]) for i in range(a))


def frac(z):
    return {"numerator": z.numerator, "denominator": z.denominator,
            "decimal": float(z)}


def canonical_frame(N, d):
    """First d vectors in the paired symplectic basis, for even d."""
    return tuple(tuple(int(i == j) for i in range(2 * N)) for j in range(d))


@lru_cache(None)
def B(q, h):
    z = Fraction(1)
    for j in range(1, h + 1):
        z *= 1 - Fraction(1, q ** (2 * j))
    return z


def balanced_likelihood(q, a, b, ell):
    h = b // 2
    C = B(q, (a + b) // 2) / B(q, a // 2)
    S = sum((Fraction(qbin(q, 2 * ell, d), q ** (d * (d + 1) // 2))
             / B(q, d - ell) for d in range(ell, 2 * ell + 1)), Fraction(0))
    return B(q, h) / C * S


def residual_form(field, F, H, M):
    """H + M^t F^-1 M for a paired canonical nonsingular F (F^-1=-F)."""
    a, b = len(F), len(H)
    columns = [tuple(M[i][j] for i in range(a)) for j in range(b)]
    return tuple(tuple(field.add[H[i][j]][field.neg[field.pairing(columns[i], columns[j])]]
                       for j in range(b)) for i in range(b))


def check_case(q, N, a, b, cache, *, canonical_only=False):
    field = Field(q)
    for d in ({b} if canonical_only else {a, b}):
        key = (q, N, d)
        if key not in cache:
            cache[key] = enumerate_frames(field, N, d)
    b_groups = cache[(q, N, b)]
    if canonical_only:
        x = canonical_frame(N, a)
        a_groups = {field.gram(x): [x]}
        h0 = field.gram(canonical_frame(N, b))
        b_groups = {h0: b_groups[h0]}
    else:
        a_groups = cache[(q, N, a)]

    outcome_checks = joint_checks = observed_frames = support_zeros = 0
    balanced_results = []
    same_rank_witness = None
    for F, xs in a_groups.items():
        sF = field.rank(F) // 2
        eF = embeddings(q, N, a, sF)
        if not canonical_only:
            assert eF == len(xs)
        X = xs[0]
        for H, ys in b_groups.items():
            sH = field.rank(H) // 2
            eH = embeddings(q, N, b, sH)
            assert eH == len(ys)
            observed = Counter()
            observed_joint = Counter()
            observed_ranks = Counter()
            for Y in ys:
                M = field.cross(X, Y)
                intersection = a + b - field.rank(X + Y)
                observed[M] += 1
                observed_joint[(M, intersection)] += 1
                observed_ranks[field.rank(M)] += 1
            observed_frames += len(ys)
            uniform_ranks = Counter()
            discrepancy = 0
            residual_nonsingular = 0
            residual_nonzero_radical_vectors = 0
            rank_representatives = {}
            balanced = (a % 2 == b % 2 == 0 and a + b == 2 * N
                        and sF * 2 == a and sH * 2 == b
                        and F == field.gram(canonical_frame(N, a)))
            for M in all_matrices(q, a, b):
                joint, (s, u, v, c) = predicted_joint(field, N, F, H, M)
                assert sum(joint.values()) == observed[M] * eF, (q, N, F, H, M)
                for d in range(min(a, b) + 1):
                    assert joint.get(d, 0) == observed_joint[(M, d)] * eF
                    joint_checks += 1
                assert bool(observed[M]) == (s + max(u, v) <= N)
                support_zeros += not bool(observed[M])
                outcome_checks += 1
                rankM = field.rank(M)
                uniform_ranks[rankM] += 1
                discrepancy += abs(observed[M] * q ** (a * b) - eH)
                old = rank_representatives.get(rankM)
                if old is None:
                    rank_representatives[rankM] = (M, observed[M])
                elif same_rank_witness is None and old[1] != observed[M]:
                    same_rank_witness = {
                        "F": F, "H": H, "rank": rankM,
                        "first_matrix": old[0], "first_count": old[1],
                        "second_matrix": M, "second_count": observed[M],
                        "total_frames": eH,
                    }
                if balanced:
                    K = residual_form(field, F, H, M)
                    ell = (b - field.rank(K)) // 2
                    actual_likelihood = Fraction(observed[M] * q ** (a * b), eH)
                    assert actual_likelihood == balanced_likelihood(q, a, b, ell)
                    assert (actual_likelihood < 1) == (ell == 0)
                    residual_nonsingular += ell == 0
                    residual_nonzero_radical_vectors += q ** (2 * ell) - 1
            if balanced:
                tv = Fraction(discrepancy, 2 * eH * q ** (a * b))
                L0 = balanced_likelihood(q, a, b, 0)
                event_tv = Fraction(residual_nonsingular, q ** (a * b)) * (1 - L0)
                assert tv == event_tv
                radical_moment = Fraction(residual_nonzero_radical_vectors, q ** (a * b))
                assert radical_moment == q * (1 - Fraction(1, q ** a)) * (1 - Fraction(1, q ** b))
                rank_tv = sum((abs(Fraction(observed_ranks[r], eH)
                                   - Fraction(uniform_ranks[r], q ** (a * b)))
                               for r in range(min(a, b) + 1)), Fraction(0)) / 2
                balanced_results.append({"F": F, "H": H,
                    "matrix_total_variation": frac(tv),
                    "rank_total_variation": frac(rank_tv),
                    "uniform_residual_nonsingular_probability": frac(Fraction(residual_nonsingular, q ** (a * b))),
                    "nonsingular_likelihood": frac(L0),
                    "uniform_residual_nonzero_radical_vector_moment": frac(radical_moment),
                    "optimal_test_verified": True})
    return {"q": q, "ambient_dimension": 2 * N, "a": a, "b": b,
            "field": "GF(4), x^2+x+1" if q == 4 else f"GF({q})",
            "canonical_nondegenerate_forms_only": canonical_only,
            "first_form_count": len(a_groups), "second_form_count": len(b_groups),
            "actual_frames_observed": observed_frames,
            "matrix_outcomes_checked": outcome_checks,
            "joint_intersection_outcomes_checked": joint_checks,
            "zero_probability_outcomes": support_zeros,
            "balanced_checks": balanced_results,
            "same_rank_different_likelihood_example": same_rank_witness,
            "status": "passed"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "results" / "exhaustive_checks.json")
    args = parser.parse_args()
    started = time.time()
    cache = {}
    cases = [(2, 1, 1, 1, False), (3, 1, 1, 1, False),
             (2, 2, 2, 2, False), (2, 2, 3, 2, False),
             (2, 2, 3, 3, False), (3, 2, 2, 2, False),
             (4, 2, 2, 2, False), (2, 3, 4, 2, True),
             (2, 4, 6, 2, True)]
    results = []
    for q, N, a, b, canonical in cases:
        result = check_case(q, N, a, b, cache, canonical_only=canonical)
        results.append(result)
        print(f"PASS q={q}, dim={2*N}, a={a}, b={b}: "
              f"{result['matrix_outcomes_checked']} matrices", flush=True)
    payload = {
        "method": "Actual independent-frame enumeration, compared with combined-Gram quotient counts",
        "status": "all checks passed",
        "cases": results,
        "totals": {key: sum(r[key] for r in results) for key in
                   ("actual_frames_observed", "matrix_outcomes_checked",
                    "joint_intersection_outcomes_checked", "zero_probability_outcomes")},
        "elapsed_seconds": round(time.time() - started, 3),
        "limitations": "Finite exhaustive checks support the formulas; the general proof is in the report. No RH/GRH proof is rebuilt by this script.",
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n")
    print(json.dumps(payload["totals"], sort_keys=True), flush=True)
    print(f"Saved {args.output}", flush=True)


if __name__ == "__main__":
    main()
