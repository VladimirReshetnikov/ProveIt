#!/usr/bin/env python3
"""Independent exhaustive checks of the symplectic block law.

No external packages are needed. Every matrix A and every matrix B are
enumerated separately, their alternating Gram matrices are counted, and
matching Gram fibres are combined. This is an exact count, not a Monte
Carlo experiment and not enumeration from the proposed likelihood law.

Examples:
    python3 verify_exhaustive.py --output ../results/exhaustive.json
    python3 verify_exhaustive.py --case 2,4 --output /tmp/one.json

The implemented fields are prime fields and F_4=F_2[x]/(x^2+x+1), with
elements encoded by 0,1,x,x+1. The F_4 implementation is used only for a
small extension-field cross-check.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import product
import json
from math import prod
from pathlib import Path
import time


class Field:
    def __init__(self, q: int):
        self.q = q
        if q != 4 and (q < 2 or any(q % p == 0 for p in range(2, int(q**0.5) + 1))):
            raise ValueError("The checker implements prime fields and F_4 only")
        self.extension = q == 4
        self.add_table = [[self._add(a, b) for b in range(q)] for a in range(q)]
        self.mul_table = [[self._mul(a, b) for b in range(q)] for a in range(q)]
        self.neg_table = [a if self.extension else (-a) % q for a in range(q)]
        self.inv_table = [0] + [next(b for b in range(1, q) if self._mul(a, b) == 1)
                                    for a in range(1, q)]

    def _add(self, a: int, b: int) -> int:
        return a ^ b if self.extension else (a + b) % self.q

    def _mul(self, a: int, b: int) -> int:
        if not self.extension:
            return a * b % self.q
        v = 0
        for i in range(2):
            if (b >> i) & 1:
                v ^= a << i
        if v & 4:
            v ^= 7  # x^2=x+1
        return v

    def add(self, a: int, b: int) -> int:
        return self.add_table[a][b]

    def sub(self, a: int, b: int) -> int:
        return self.add_table[a][self.neg_table[b]]

    def mul(self, a: int, b: int) -> int:
        return self.mul_table[a][b]


def matrix_rank(flat: tuple[int, ...], n: int, field: Field) -> int:
    rows = [list(flat[i*n:(i+1)*n]) for i in range(n)]
    r = 0
    for col in range(n):
        pivot = next((i for i in range(r, n) if rows[i][col]), None)
        if pivot is None:
            continue
        rows[r], rows[pivot] = rows[pivot], rows[r]
        inv = field.inv_table[rows[r][col]]
        rows[r] = [field.mul(x, inv) for x in rows[r]]
        for i in range(r + 1, n):
            a = rows[i][col]
            if a:
                rows[i] = [field.sub(x, field.mul(a, y))
                           for x, y in zip(rows[i], rows[r])]
        r += 1
        if r == n:
            break
    return r


def upper_pairs(n: int) -> list[tuple[int, int]]:
    return [(i, j) for i in range(n) for j in range(i + 1, n)]


def gram_upper(a: tuple[int, ...], n: int, field: Field,
               pairs: list[tuple[int, int]]) -> tuple[int, ...]:
    """Return upper entries of A^T J A, J=[0 I; -I 0]."""
    m = n // 2
    answer = []
    for i, j in pairs:
        entry = 0
        for h in range(m):
            term = field.sub(field.mul(a[h*n+i], a[(h+m)*n+j]),
                             field.mul(a[(h+m)*n+i], a[h*n+j]))
            entry = field.add(entry, term)
        answer.append(entry)
    return tuple(answer)


def full_alternating(upper: tuple[int, ...], n: int, field: Field,
                     pairs: list[tuple[int, int]]) -> tuple[int, ...]:
    a = [0] * (n*n)
    for (i, j), x in zip(pairs, upper):
        a[i*n+j] = x
        a[j*n+i] = field.neg_table[x]
    return tuple(a)


def sp_order(m: int, q: int) -> int:
    """Order of Sp_(2m)(F_q)."""
    return q**(m*m) * prod(q**(2*i) - 1 for i in range(1, m + 1))


def gaussian(n: int, k: int, q: int) -> int:
    if k < 0 or k > n:
        return 0
    numerator = prod(q**(n-i) - 1 for i in range(k))
    denominator = prod(q**(k-i) - 1 for i in range(k))
    value, remainder = divmod(numerator, denominator)
    assert remainder == 0
    return value


def proposed_completion_count(m: int, k: int, q: int) -> int:
    """Formula to be compared against the independently counted fibres."""
    total = sum(gaussian(2*k, d, q) *
                prod(q**(2*k-i) - q**i for i in range(d))
                for d in range(k + 1))
    count = Fraction(sp_order(m, q) * total, sp_order(k, q))
    assert count.denominator == 1
    return count.numerator


def fraction_json(x: Fraction | int) -> dict[str, int | float]:
    x = Fraction(x)
    return {"numerator": x.numerator, "denominator": x.denominator,
            "decimal": float(x)}


def verify_case(q: int, n: int) -> dict:
    assert n > 0 and n % 2 == 0
    started = time.perf_counter()
    field = Field(q)
    m = n // 2
    pairs = upper_pairs(n)
    j_upper = tuple(1 if v == u + m else 0 for u, v in pairs)
    # This loop is the independent source of all probabilities below.
    by_gram_and_rank: dict[tuple[int, ...], Counter] = defaultdict(Counter)
    for a in product(range(q), repeat=n*n):
        by_gram_and_rank[gram_upper(a, n, field, pairs)][matrix_rank(a, n, field)] += 1
    gram_count = {g: sum(ranks.values()) for g, ranks in by_gram_and_rank.items()}
    matrix_total = q**(n*n)
    assert sum(gram_count.values()) == matrix_total

    corank = {g: n - matrix_rank(full_alternating(g, n, field, pairs), n, field)
              for g in gram_count}
    assert all(k % 2 == 0 for k in corank.values())
    assert len(gram_count) == q**(n*(n-1)//2)

    # Count B directly: B^T J B must equal J-A^T J A. Each A has exactly
    # gram_count[J-gram(A)] completions. No pair of matrices is sampled.
    total_frames = 0
    iid_rank = Counter()
    model_rank = Counter()
    iid_defect = Counter()
    model_defect = Counter()
    joint = Counter()
    likelihoods = {}
    for g, counts in by_gram_and_rank.items():
        defect = tuple(field.sub(x, y) for x, y in zip(j_upper, g))
        k = corank[defect] // 2
        completions = gram_count[defect]
        assert completions == proposed_completion_count(m, k, q)
        likelihoods.setdefault(k, completions)
        assert likelihoods[k] == completions
        for rank_a, number_a in counts.items():
            frames = number_a * completions
            total_frames += frames
            iid_rank[rank_a] += number_a
            model_rank[rank_a] += frames
            iid_defect[k] += number_a
            model_defect[k] += frames
            joint[rank_a, k] += number_a

    # Any frame with Gram J is injective, and Sp_(2n) acts transitively.
    expected_frames = Fraction(sp_order(2*m, q), sp_order(m, q))
    assert expected_frames.denominator == 1
    assert total_frames == expected_frames.numerator

    alpha = Fraction(matrix_total * sp_order(m, q), total_frames)
    b_m = prod((Fraction(q**(2*i)-1, q**(2*i)) for i in range(1, m+1)), start=Fraction(1))
    b_2m = prod((Fraction(q**(2*i)-1, q**(2*i)) for i in range(1, 2*m+1)), start=Fraction(1))
    assert alpha == b_m*b_m/b_2m
    assert alpha < 1
    assert all(Fraction(matrix_total*c, total_frames) > 1
               for k, c in likelihoods.items() if k > 0)
    tv = sum((abs(Fraction(model_defect[k], total_frames) - Fraction(iid_defect[k], matrix_total))
              for k in iid_defect), start=Fraction(0)) / 2
    defect_test_advantage = (1-alpha) * Fraction(iid_defect[0], matrix_total)
    assert tv == defect_test_advantage
    rank_tv = sum((abs(Fraction(model_rank[r], total_frames)-Fraction(iid_rank[r], matrix_total))
                   for r in range(n+1)), start=Fraction(0)) / 2
    assert rank_tv <= tv

    # Equal likelihood on every Gram fibre means that summing by defect
    # corank above is exactly the full-matrix total variation distance.
    exact_full_tv = sum((gram_count[g] *
                        abs(Fraction(gram_count[tuple(field.sub(x, y) for x, y in zip(j_upper, g))], total_frames)
                            - Fraction(1, matrix_total))
                        for g in gram_count), start=Fraction(0)) / 2
    assert exact_full_tv == tv

    return {
        "q": q, "block_dimension_N": n, "ambient_dimension": 2*n,
        "field_model": "F_2[x]/(x^2+x+1)" if q == 4 else f"F_{q}",
        "enumerated_matrices_each_side": matrix_total,
        "distinct_alternating_Gram_matrices": len(gram_count),
        "admissible_frames_count": total_frames,
        "expected_frames_Sp_2N_over_Sp_N": expected_frames.numerator,
        "alpha": fraction_json(alpha),
        "full_matrix_total_variation": fraction_json(tv),
        "rank_total_variation": fraction_json(rank_tv),
        "iid_probability_defect_invertible": fraction_json(Fraction(iid_defect[0], matrix_total)),
        "model_probability_defect_invertible": fraction_json(Fraction(model_defect[0], total_frames)),
        "completion_counts_by_half_defect_nullity": {str(k): likelihoods[k] for k in sorted(likelihoods)},
        "likelihoods_by_half_defect_nullity": {
            str(k): fraction_json(Fraction(matrix_total*likelihoods[k], total_frames)) for k in sorted(likelihoods)},
        "rank_distribution": [{"rank": r, "iid_count": iid_rank[r], "model_frame_count": model_rank[r],
                               "iid_probability": fraction_json(Fraction(iid_rank[r], matrix_total)),
                               "model_probability": fraction_json(Fraction(model_rank[r], total_frames))}
                              for r in range(n+1)],
        "defect_distribution": [{"half_nullity": k, "iid_count": iid_defect[k],
                                 "model_frame_count": model_defect[k],
                                 "iid_probability": fraction_json(Fraction(iid_defect[k], matrix_total)),
                                 "model_probability": fraction_json(Fraction(model_defect[k], total_frames))}
                                for k in sorted(iid_defect)],
        "conditional_defect_given_block_rank": [
            {"block_rank": r,
             "half_defect_nullity": k,
             "iid_joint_count": joint[r, k],
             "iid_conditional_probability": fraction_json(Fraction(joint[r, k], iid_rank[r])),
             "model_conditional_probability": fraction_json(Fraction(joint[r, k] * likelihoods[k], model_rank[r]))}
            for r in range(n+1) for k in sorted(iid_defect) if joint[r, k]],
        "all_exact_assertions_passed": True,
        "elapsed_seconds": round(time.perf_counter()-started, 3),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", action="append", help="One case q,N; may be repeated")
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "results" / "exhaustive.json")
    args = parser.parse_args()
    cases = [(int(q), int(n)) for q, n in (s.split(",") for s in args.case)] if args.case else [(2, 2), (2, 4), (3, 2), (4, 2), (5, 2)]
    result = {
        "description": "Exhaustive Gram-fibre verification of nondegenerate symplectic block probabilities",
        "method": "Enumerate all square A and B matrices separately; aggregate their exact Gram fibres; match A^T J A+B^T J B=J.",
        "cases": [],
    }
    for q, n in cases:
        one = verify_case(q, n)
        result["cases"].append(one)
        print(f"q={q}, N={n}: {one['enumerated_matrices_each_side']} matrices per side, "
              f"TV={Fraction(**{'numerator': one['full_matrix_total_variation']['numerator'], 'denominator': one['full_matrix_total_variation']['denominator']})}, "
              f"rank TV={Fraction(one['rank_total_variation']['numerator'], one['rank_total_variation']['denominator'])}", flush=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(f"Saved {args.output}")


if __name__ == "__main__":
    main()
