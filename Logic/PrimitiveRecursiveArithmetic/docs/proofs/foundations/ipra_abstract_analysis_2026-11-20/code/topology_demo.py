#!/usr/bin/env python3
"""Exact-rational demonstrations for the function-space topology section.

These finite checks exercise the explicit construction, including clipping
outside the range and guarded gluing. They are not a substitute for the
universal mathematical proofs or for a Prf PRAAx derivation.

Run from the package directory:
    python3 code/topology_demo.py --output evidence/topology_checks.json
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction as Q
from pathlib import Path


def dyad(k: int) -> Q:
    return Q(1, 1 << k)


def clipped_floor(e: Q, bound: int, delta: Q) -> Q:
    """Round down to delta*Z and project to [-bound,bound]."""
    j = e // delta
    return min(Q(bound), max(Q(-bound), delta * j))


def weights(centres: list[Q], radius: Q, x: Q) -> list[Q]:
    return [max(Q(0), radius - abs(x - c)) for c in centres]


def reconstruct(centres: list[Q], radius: Q, coeff: list[Q], x: Q) -> Q:
    w = weights(centres, radius, x)
    denom = sum(w, Q(0))
    assert denom >= radius / 2
    return sum((u * h for u, h in zip(w, coeff)), Q(0)) / denom


def grid_code(coeff: list[Q], bound: int, delta: Q) -> tuple[int, int]:
    base = int(2 * bound / delta) + 1
    code, place = 0, 1
    for h in coeff:
        j = (h + bound) / delta
        assert j.denominator == 1 and 0 <= j < base
        code += int(j) * place
        place *= base
    assert 0 <= code < place
    return code, place


def ascoli_checks() -> list[dict[str, object]]:
    # Each displayed function maps [0,1] into [-1,1] and is 1-Lipschitz.
    examples = [
        ("identity", lambda x: x),
        ("negative_identity", lambda x: -x),
        ("absolute_corner", lambda x: abs(x - Q(1, 3))),
        ("quadratic", lambda x: x * x / 2),
        ("constant_upper_endpoint", lambda x: Q(1)),
        ("constant_lower_endpoint", lambda x: Q(-1)),
    ]
    query = [Q(j, 193) for j in range(194)]
    records = []
    for k in range(4):
        radius, delta = dyad(k + 2), dyad(k + 3)
        s = k + 4  # mu(j)=j; use rational mesh r/4.
        centres = [Q(i, 1 << s) for i in range((1 << s) + 1)]
        for name, f in examples:
            # Deliberately perturb both signs, including beyond +/-B.
            observed = [f(c) + (delta if i % 2 else -delta)
                        for i, c in enumerate(centres)]
            coeff = [clipped_floor(e, 1, delta) for e in observed]
            for e, h in zip(observed, coeff):
                assert abs(h - e) <= delta
            code, count = grid_code(coeff, 1, delta)
            values = [reconstruct(centres, radius, coeff, x) for x in query]
            errors = [abs(v - f(x)) for x, v in zip(query, values)]
            assert max(errors) <= dyad(k + 1)
            lip = 4 * len(centres) / radius
            for x, y, u, v in zip(query, query[1:], values, values[1:]):
                assert abs(u - v) <= lip * abs(x - y)
                assert abs(u) <= 1
            # Direct rational target using independently perturbed observations.
            p = k + 5
            for j, (x, v) in enumerate(zip(query, values)):
                e = f(x) + (dyad(p) if j % 2 else -dyad(p))
                assert abs(v - e) <= dyad(k + 1) + dyad(p)
            records.append({
                "function": name,
                "precision_k": k,
                "source_scale": s,
                "net_points": len(centres),
                "cover_count_decimal_digits": len(str(count)),
                "selected_code_below_cover_count": code < count,
                "observed_max_error": str(max(errors)),
                "proved_uniform_error_bound": str(dyad(k + 1)),
                "query_count": len(query),
            })
    return records


def gluing_checks() -> dict[str, object]:
    centres = [Q(i, 4) for i in range(5)]
    radius, bound, local_lip = Q(1, 2), Q(2), Q(1)
    offsets = [Q(-1, 8), Q(1, 8), Q(0), Q(-1, 8), Q(1, 8)]
    alpha = Q(1, 4)
    query = [Q(j, 256) for j in range(257)]
    out, largest_local_discrepancy = [], Q(0)
    for x in query:
        w = weights(centres, radius, x)
        assert sum(w) >= radius / 2
        terms = []
        for c, t, offset in zip(centres, w, offsets):
            if t > 0:
                assert abs(x - c) < radius < 2 * radius
                terms.append(t * (x + offset))
            else:
                terms.append(Q(0))
        g = sum(terms) / sum(w)
        assert abs(g) <= bound
        out.append(g)
        for t, offset in zip(w, offsets):
            if t > 0:
                discrepancy = abs(g - (x + offset))
                largest_local_discrepancy = max(largest_local_discrepancy, discrepancy)
                assert discrepancy <= alpha
        # Averaging local name errors introduces no amplification.
        delta = dyad(7)
        approximate = sum(t * (x + offset + (delta if i % 2 else -delta))
                          for i, (t, offset) in enumerate(zip(w, offsets))) / sum(w)
        assert abs(approximate - g) <= delta
    lip = 2 * len(centres) * local_lip + 4 * len(centres) * bound / radius
    for x, y, u, v in zip(query, query[1:], out, out[1:]):
        assert abs(u - v) <= lip * abs(x - y)
    return {"net_points": len(centres), "query_count": len(query),
            "proved_lipschitz_bound": str(lip),
            "overlap_bound": str(alpha),
            "observed_max_local_discrepancy": str(largest_local_discrepancy)}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = {
        "status": "passed",
        "arithmetic": "Python Fraction; no floating point",
        "scope": "finite executable demonstrations, not universal proof or Lean compilation",
        "ascoli": ascoli_checks(),
        "gluing": gluing_checks(),
    }
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    print(text)


if __name__ == "__main__":
    main()
