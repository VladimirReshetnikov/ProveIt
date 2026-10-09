#!/usr/bin/env python3
"""Exact audit of the weight-six, three-letter-occurrence shuffle quotient.

This is formal word algebra.  It proves no numerical-period independence.
In particular, rank seven of product relations does not mean that seven
individual Gaussian triples are products.
"""
from collections import Counter
from fractions import Fraction
from functools import lru_cache
import json
from pathlib import Path


@lru_cache(None)
def shuffle(u, v):
    if not u:
        return {v: 1}
    if not v:
        return {u: 1}
    answer = Counter()
    for w, coefficient in shuffle(u[1:], v).items():
        answer[(u[0],) + w] += coefficient
    for w, coefficient in shuffle(u, v[1:]).items():
        answer[(v[0],) + w] += coefficient
    return dict(answer)


def word(indices):
    return sum(((0,) * (p - 1) + (1,) for p in indices), ())


def exact_rank(rows):
    matrix = [[Fraction(x) for x in row] for row in rows]
    pivot = 0
    for column in range(len(matrix[0])):
        selected = next((r for r in range(pivot, len(matrix)) if matrix[r][column]), None)
        if selected is None:
            continue
        matrix[pivot], matrix[selected] = matrix[selected], matrix[pivot]
        factor = matrix[pivot][column]
        matrix[pivot] = [entry / factor for entry in matrix[pivot]]
        for r in range(pivot + 1, len(matrix)):
            factor = matrix[r][column]
            matrix[r] = [x - factor * y for x, y in zip(matrix[r], matrix[pivot])]
        pivot += 1
        if pivot == len(matrix):
            break
    return pivot


def main():
    triples = [(a, b, 6 - a - b) for a in range(1, 5)
               for b in range(1, 6 - a) if 6 - a - b >= 1]
    words = [word(t) for t in triples]
    rows = []
    for p, q, r in triples:
        expansion = shuffle(word((p,)), word((q, r)))
        rows.append([expansion.get(w, 0) for w in words])
    for p, q, r in triples:
        if not p <= q <= r:
            continue
        expansion = Counter()
        for u, c in shuffle(word((p,)), word((q,))).items():
            for w, d in shuffle(u, word((r,))).items():
                expansion[w] += c * d
        rows.append([expansion.get(w, 0) for w in words])
    rank = exact_rank(rows)
    assert len(rows) == 13 and rank == 7
    witnesses = [[-1, 2, -2, 1, 0, 0, -1, 1, 0, 0],
                 [-3, 6, -6, 3, -1, 4, -4, 0, 1, 0],
                 [-6, 12, -12, 6, -3, 12, -9, 0, 0, 1]]
    assert exact_rank(witnesses) == 3
    assert all(sum(a * b for a, b in zip(row, witness)) == 0
               for row in rows for witness in witnesses)
    assert all(any(witness[i] for witness in witnesses) for i in range(10))
    result = {"status": "exact formal shuffle algebra; no numerical-period independence claim",
              "triples_in_column_order": triples, "shuffle_product_matrix": rows,
              "exact_rank": rank, "formal_quotient_dimension": 10 - rank,
              "annihilating_linear_functionals": witnesses,
              "individual_words_in_formal_product_rowspace": [],
              "interpretation": "Seven independent combinations are products; no individual word is forced to be a product by these shuffle relations."}
    output = Path(__file__).resolve().parents[1] / "data" / "gaussian_shuffle_audit.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print("Exact rank 7 of 13 shuffle-product rows on 10 triples; quotient dimension 3.")
    print("All three integer annihilator witnesses verified; no individual word in product rowspace.")
    print(output)


if __name__ == "__main__":
    main()
