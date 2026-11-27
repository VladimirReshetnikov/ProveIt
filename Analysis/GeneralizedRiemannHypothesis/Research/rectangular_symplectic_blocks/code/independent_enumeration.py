#!/usr/bin/env python3
"""Independent exhaustive counts of rectangular symplectic blocks.

No embedding counts, q-binomial moments, or limiting formulas are used.
For each U enumerate its residual Gram matrix and count all hidden C directly.
"""
from collections import Counter
from fractions import Fraction
from itertools import product
from pathlib import Path
import json
import time


def mat_rank(rows, p):
    a = [list(row) for row in rows]
    nr, nc = len(a), len(a[0])
    r = 0
    for c in range(nc):
        pivot = next((i for i in range(r, nr) if a[i][c] % p), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        inv = pow(a[r][c] % p, -1, p)
        a[r] = [(v * inv) % p for v in a[r]]
        for i in range(r + 1, nr):
            if a[i][c]:
                t = a[i][c]
                a[i] = [(v - t * w) % p for v, w in zip(a[i], a[r])]
        r += 1
        if r == nr:
            break
    return r


def bit_rank(rows):
    pivots = {}
    for x in rows:
        while x:
            c = x.bit_length() - 1
            if c in pivots:
                x ^= pivots[c]
            else:
                pivots[c] = x
                break
    return len(pivots)


def entries(p, a, b):
    if p == 2:
        for x in range(1 << (a * b)):
            rows = [(x >> (i * b)) & ((1 << b) - 1) for i in range(a)]
            gram = tuple(
                sum(((rows[k] >> i) & 1) * ((rows[k + 1] >> j) & 1)
                    + ((rows[k + 1] >> i) & 1) * ((rows[k] >> j) & 1)
                    for k in range(0, a, 2)) % 2
                for i in range(b) for j in range(i + 1, b))
            yield gram, bit_rank(rows)
    else:
        for x in product(range(p), repeat=a * b):
            rows = [x[i * b:(i + 1) * b] for i in range(a)]
            gram = tuple(
                sum(rows[k][i] * rows[k + 1][j] - rows[k + 1][i] * rows[k][j]
                    for k in range(0, a, 2)) % p
                for i in range(b) for j in range(i + 1, b))
            yield gram, mat_rank(rows, p)


def alt_nullity(v, p, b):
    rows = [[0] * b for _ in range(b)]
    k = 0
    for i in range(b):
        for j in range(i + 1, b):
            rows[i][j] = v[k]
            rows[j][i] = (-v[k]) % p
            k += 1
    return b - mat_rank(rows, p)


def frac(v):
    return {"numerator": v.numerator, "denominator": v.denominator,
            "exact": str(v), "decimal": float(v)}


def tv(h1, n1, h2, n2):
    return sum((abs(Fraction(h1.get(k, 0), n1) - Fraction(h2.get(k, 0), n2))
                for k in h1.keys() | h2.keys()), Fraction(0)) / 2


def one_case(p, a, b):
    start = time.monotonic()
    hidden = Counter(gram for gram, _ in entries(p, b, b))
    jgram = tuple(int(i % 2 == 0 and j == i + 1)
                  for i in range(b) for j in range(i + 1, b))
    alt_rank = {key: alt_nullity(key, p, b)
                for key in product(range(p), repeat=b * (b - 1) // 2)}
    iid_nullity, symp_nullity = Counter(), Counter()
    iid_defect, symp_defect = Counter(), Counter()
    iid_joint, symp_joint = Counter(), Counter()
    weights = Counter()
    n = p ** (a * b)
    for gram, rank in entries(p, a, b):
        residual = tuple((j - g) % p for j, g in zip(jgram, gram))
        w = hidden.get(residual, 0)
        defect = alt_rank[residual]
        iid_nullity[b - rank] += 1
        symp_nullity[b - rank] += w
        iid_defect[defect] += 1
        symp_defect[defect] += w
        iid_joint[(b - rank, defect)] += 1
        symp_joint[(b - rank, defect)] += w
        weights[w] += 1
    total = sum(symp_nullity.values())
    full_tv = sum((count * abs(Fraction(w, total) - Fraction(1, n))
                   for w, count in weights.items()), Fraction(0)) / 2
    alt_counts = Counter(alt_rank.values())
    nullity_tv = tv(iid_nullity, n, symp_nullity, total)
    defect_tv = tv(iid_defect, n, alt_counts, p ** (b * (b - 1) // 2))
    singular_gap = Fraction(sum(v for k, v in symp_defect.items() if k), total)
    singular_gap -= Fraction(sum(v for k, v in iid_defect.items() if k), n)
    assert singular_gap == full_tv
    joint_product_tv = sum((abs(Fraction(iid_joint.get((k, l), 0), n)
                                - Fraction(ck * cl, n * n))
                            for k, ck in iid_nullity.items()
                            for l, cl in iid_defect.items()), Fraction(0)) / 2
    return {"q": p, "a": a, "b": b, "iid_total": n,
            "symplectic_frame_total": total,
            "hidden_gram_counts": {str(k): v for k, v in hidden.items()},
            "iid_nullity_counts": dict(sorted(iid_nullity.items())),
            "symp_nullity_weights": dict(sorted(symp_nullity.items())),
            "iid_defect_nullity_counts": dict(sorted(iid_defect.items())),
            "symp_defect_nullity_weights": dict(sorted(symp_defect.items())),
            "iid_joint_nullity_counts": {f"{k},{l}": c for (k, l), c in sorted(iid_joint.items())},
            "symp_joint_nullity_weights": {f"{k},{l}": c for (k, l), c in sorted(symp_joint.items())},
            "uniform_alt_nullity_counts": dict(sorted(alt_counts.items())),
            "full_matrix_tv": frac(full_tv), "rank_tv": frac(nullity_tv),
            "defect_vs_alt_tv": frac(defect_tv),
            "iid_joint_vs_product_tv": frac(joint_product_tv),
            "residual_singularity_exactly_optimal": True,
            "elapsed_seconds": time.monotonic() - start}


def main():
    cases = [(2, 2, 2), (2, 4, 2), (2, 4, 4), (2, 6, 2),
             (3, 2, 2), (3, 4, 2)]
    data = []
    for p, a, b in cases:
        r = one_case(p, a, b)
        data.append(r)
        print(p, a, b, "frames", r["symplectic_frame_total"],
              "full TV", r["full_matrix_tv"]["exact"],
              "rank TV", r["rank_tv"]["exact"], flush=True)
    path = Path(__file__).resolve().parents[1] / "results" / "independent_enumeration.json"
    path.write_text(json.dumps({"method": "Direct enumeration of U and hidden C Gram counts",
                                "cases": data}, indent=2) + "\n")


if __name__ == "__main__":
    main()
