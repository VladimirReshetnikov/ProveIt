#!/usr/bin/env python3
"""Exact independent checks for complete bipartite symplectic observations.

Run beside verify.py: python3 verify_anchors.py
Every observed law and its full-anchor-rank conditional law are obtained
from exhaustive assignments of actual nonzero vectors. The predictions
are used only afterwards. Requires Python standard library only.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as F
from itertools import product
import json
from math import prod
from pathlib import Path
import platform
import time

from verify import Field, frac_json, independent_probability, vector_model


def rank_over_field(rows, field: Field) -> int:
    work = [list(row) for row in rows]
    if not work:
        return 0
    q, pivot_row = field.q, 0
    add, mul, neg = field.add_table, field.mul_table, field.neg_table
    for col in range(len(work[0])):
        row = next((r for r in range(pivot_row, len(work)) if work[r][col]), None)
        if row is None:
            continue
        work[pivot_row], work[row] = work[row], work[pivot_row]
        pivot = work[pivot_row][col]
        inverse = next(b for b in range(1, q) if mul[pivot][b] == 1)
        work[pivot_row] = [mul[inverse][x] for x in work[pivot_row]]
        for r in range(pivot_row+1, len(work)):
            coeff = work[r][col]
            if coeff:
                work[r] = [add[x][neg[mul[coeff][y]]]
                           for x, y in zip(work[r], work[pivot_row])]
        pivot_row += 1
        if pivot_row == len(work):
            break
    return pivot_row


def rho(q: int, N: int, column) -> F:
    a = len(column)
    return F(N-q**a if not any(column) else N, q**a*(N-1))


def rho_product(q: int, N: int, a: int, labels) -> F:
    return prod(rho(q, N, labels[j:j+a]) for j in range(0, len(labels), a))


def conditional_chi_squared(q: int, N: int, a: int) -> F:
    term = (F(N)**(2-a)*(N-q+1)**a + q**a - 2*N)
    return F((N-1)**(a-2), (N-q)**a)*term-1


def enumerate_actual(q: int, n: int, a: int, m: int, model):
    field, vectors, pairings = model
    size = len(vectors)
    counts, full_counts = Counter(), Counter()
    anchor_total, full_anchor_total = size**a, 0
    for anchors in product(range(size), repeat=a):
        full_rank = rank_over_field([vectors[i] for i in anchors], field) == a
        full_anchor_total += full_rank
        columns = [tuple(pairings[i][z] for i in anchors) for z in range(size)]
        for leaves in product(range(size), repeat=m):
            labels = tuple(value for j in leaves for value in columns[j])
            counts[labels] += 1
            if full_rank:
                full_counts[labels] += 1
    total = size**(a+m)
    full_total = full_anchor_total*size**m
    assert sum(counts.values()) == total
    assert sum(full_counts.values()) == full_total
    return counts, full_counts, total, full_total, full_anchor_total, anchor_total


def verify_case(q: int, n: int, a: int, m: int, model) -> dict:
    N = q**(2*n)
    assert 2 <= a <= 2*n
    counts, fc, total, ft, fac, at = enumerate_actual(q, n, a, m, model)
    alpha = prod(F(N-q**i, N-1) for i in range(a))
    assert F(fac, at) == alpha
    delta = 1-alpha
    delta_bound = F(sum(q**i-1 for i in range(a)), N-1)
    assert delta <= delta_bound
    tv_pq, tv_pr, tv_rq = F(0), F(0), F(0)
    chi_pq, chi_rq = F(0), F(0)
    event_mass_p, event_mass_q = F(0), F(0)
    for labels in product(range(q), repeat=a*m):
        p = F(counts[labels], total)
        r = F(fc[labels], ft)
        predicted_r = rho_product(q, N, a, labels)
        assert r == predicted_r, (q, n, a, m, labels, r, predicted_r)
        independent = independent_probability(q, N, labels)
        tv_pq += abs(p-independent)/2
        tv_pr += abs(p-r)/2
        tv_rq += abs(r-independent)/2
        chi_pq += (p-independent)**2/independent
        chi_rq += (r-independent)**2/independent
        if a == 2 and all(labels[2*j+1] == labels[2*j] for j in range(m)):
            event_mass_p += p
            event_mass_q += independent
    assert tv_pr <= delta
    assert abs(tv_pq-tv_rq) <= delta
    v = conditional_chi_squared(q, N, a)
    assert chi_rq == (1+v)**m-1
    if m == 1:
        assert tv_pq == 0  # K_(a,1) is a star, hence has independent edges.
    extra = {}
    if a == 2:
        assert v == F((q-1)**2, (N-q)**2)
        s = F(1, q)+F(q-1, q*(N-1)**2)
        assert event_mass_q == s**m
        assert event_mass_p >= F(1, N-1)
        lower = F(1, (N-1)**2)/s**m
        assert 1+chi_pq >= lower
        extra = {"rare_event_actual_mass": frac_json(event_mass_p),
                 "rare_event_reference_mass": frac_json(event_mass_q),
                 "one_plus_actual_chi2_lower_bound": frac_json(lower)}
    return {"q": q, "n": n, "anchors": a, "leaves": m,
            "vector_assignments": total,
            "anchor_assignments": at, "independent_anchor_assignments": fac,
            "label_outcomes_checked": q**(a*m),
            "anchor_independence_probability": frac_json(alpha),
            "anchor_failure_probability": frac_json(delta),
            "anchor_failure_upper_bound": frac_json(delta_bound),
            "actual_vs_reference_tv": frac_json(tv_pq),
            "actual_vs_conditional_tv": frac_json(tv_pr),
            "conditional_vs_reference_tv": frac_json(tv_rq),
            "actual_chi2": frac_json(chi_pq),
            "conditional_product_chi2": frac_json(chi_rq),
            "conditional_one_column_chi2": frac_json(v),
            "rare_event_checks": extra, "passed": True}


def verify_score(q: int, a: int) -> dict:
    scores = []
    for y in product(range(q), repeat=a):
        score = sum(q-1 if v == 0 else -1 for v in y) - (q**a*(not any(y))-1)
        scores.append(score)
    assert sum(scores) == 0
    information = q**a-1-a*(q-1)
    assert F(sum(x*x for x in scores), q**a) == information
    assert information > 0
    return {"q": q, "anchors": a, "labels": q**a,
            "limiting_information": information, "passed": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parent / "anchor_verification.json")
    args = parser.parse_args()
    start = time.perf_counter()
    cases = ([(2, 1, 2, m) for m in range(1, 6)] +
             [(2, 2, 2, m) for m in range(1, 4)] +
             [(3, 1, 2, m) for m in range(1, 4)] +
             [(3, 2, 2, 1)] +
             [(4, 1, 2, m) for m in range(1, 4)] +
             [(5, 1, 2, m) for m in range(1, 3)] +
             [(2, 2, 3, 1), (2, 2, 3, 2), (2, 2, 4, 1)])
    models = {(q, n): vector_model(q, n) for q, n in sorted({(q, n) for q, n, _, _ in cases})}
    results = {"description": "Actual nonzero-vector enumeration for complete bipartite masks",
               "python": platform.python_version(), "arithmetic": "exact integers and Fraction",
               "cases": [], "score_checks": []}
    for q, n, a, m in cases:
        result = verify_case(q, n, a, m, models[q, n])
        results["cases"].append(result)
        print(f"PASS K_({a},{m}) q={q}, n={n}, assignments={result['vector_assignments']}", flush=True)
    for q in (2, 3, 4, 5):
        for a in range(2, 6):
            results["score_checks"].append(verify_score(q, a))
    results["summary"] = {
        "all_passed": True,
        "complete_bipartite_cases": len(cases),
        "actual_vector_assignments_enumerated": sum(r["vector_assignments"] for r in results["cases"]),
        "label_outcomes_checked": sum(r["label_outcomes_checked"] for r in results["cases"]),
        "score_cases": len(results["score_checks"]),
        "score_labels_checked": sum(r["labels"] for r in results["score_checks"]),
        "elapsed_seconds": round(time.perf_counter()-start, 6),
        "scope": "Finite cases test the conditional product law, rank probabilities, TV bound, chi-square identities and rare-event lower bound. Universal results rely on the proof."
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results, indent=2)+"\n", encoding="utf-8")
    print(json.dumps(results["summary"], indent=2), flush=True)


if __name__ == "__main__":
    main()
