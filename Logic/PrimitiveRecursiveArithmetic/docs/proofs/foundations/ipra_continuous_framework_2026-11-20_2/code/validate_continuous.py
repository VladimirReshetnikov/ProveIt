#!/usr/bin/env python3
"""Exact-rational checks for the continuous-interface chapter.

These are executable checks and examples, not proofs of universal theorems
and not deep iPRA derivations. Only the Python standard library is used.
"""
from __future__ import annotations

import json
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path


def eps(n: int) -> Q:
    return Q(1, 2**n)


def clip(q: Q) -> Q:
    return max(Q(-1), min(Q(1), q))


def cubic_approx(name, n: int) -> tuple[Q, dict]:
    """Bounded bisection computes exactly the finite maximum in the paper."""
    J = 2 ** (n + 5)
    sample = clip(name(n + 4))
    lo, hi = 0, J
    for _ in range(n + 6):
        mid = (lo + hi + 1) // 2
        q = Q(-1) + Q(2 * mid, J)
        if q**3 <= sample:
            lo = mid
        else:
            hi = mid - 1
    assert lo == hi
    result = Q(-1) + Q(2 * lo, J)
    assert result**3 <= sample
    assert lo == J or (Q(-1) + Q(2 * (lo + 1), J))**3 > sample
    return result, {"grid_size": J, "index": lo, "sample": sample}


def weights(x: Q) -> list[Q]:
    return [max(Q(0), Q(3, 4) - abs(x - c)) for c in (Q(0), Q(1))]


def inner_weights(x: Q, t: int) -> list[Q]:
    result = []
    for i, center in enumerate((Q(0), Q(1))):
        approximation = abs(x - center) + (-1) ** (t + i) * eps(t)
        result.append(max(Q(0), Q(3, 4) - approximation - eps(t)))
    return result


def local(i: int, p: int, x: Q, offset: Q) -> Q:
    return x + i * offset + (-1) ** p * eps(p) / 4


def glue(p: int, x: Q, offset: Q, ws=None) -> Q:
    ws = weights(x) if ws is None else ws
    S = sum(ws)
    assert S > 0
    # The conditional is essential: correctness outside the active guard
    # is not a requirement of the local routine.
    A = sum(w * local(i, p, x, offset) if w > 0 else Q(0)
            for i, w in enumerate(ws))
    return A / S


def run_checks() -> dict:
    counts = Counter()
    cube_grid = [Q(i, 8) for i in range(-16, 17)]
    for u in cube_grid:
        for v in cube_grid:
            assert abs(u - v) ** 3 <= 4 * abs(u**3 - v**3)
            counts["global_cubic_separation"] += 1

    targets = [Q(-1), Q(-27, 64), Q(-1, 64), Q(0),
               Q(1, 10), Q(1, 64), Q(27, 64), Q(1)]
    examples = []
    for target in targets:
        for pattern in (0, 1, 2):
            def name(p, target=target, pattern=pattern):
                if pattern == 0:
                    return target
                if pattern == 1:
                    return target + (-1) ** p * eps(p)
                return target - eps(p)

            for n in range(11):
                result, _ = cubic_approx(name, n)
                assert -1 <= result <= 1
                assert abs(result**3 - target) <= eps(n + 2)
                for t in (0, 3, 9, 20):
                    assert abs(result**3 - name(t)) <= eps(n + 2) + eps(t)
                    counts["cubic_cross_sample_residual"] += 1
                counts["cubic_grid_residual"] += 1
            zs = [cubic_approx(name, 3 * k + 9)[0] for k in range(7)]
            for m in range(7):
                for n in range(7):
                    assert abs(zs[m] - zs[n]) <= eps(m) + eps(n)
                    counts["cubic_name_coherence"] += 1
            if pattern == 1:
                result, data = cubic_approx(name, 8)
                examples.append({
                    "input": str(target), "residual_index": 8,
                    "sample_output": str(result),
                    "actual_residual": str(abs(result**3 - target)),
                    "proved_residual_bound": str(eps(10)),
                    "grid_size": data["grid_size"], "grid_index": data["index"]
                })

    points = [Q(j, 16) for j in range(17)]
    M, L, delta, N = Q(2), Q(1), Q(1, 2), 2
    C = L + 2 * N * M / delta
    for x in points:
        assert sum(weights(x)) >= delta
        counts["cover_denominator"] += 1
        for y in points:
            for p in range(4):
                for q in range(4):
                    for offset in (Q(0), Q(1, 4)):
                        up, uq = glue(p, x, offset), glue(q, y, offset)
                        assert abs(up) <= M
                        assert abs(up - uq) <= C * abs(x - y) + eps(p) + eps(q)
                        counts["weighted_gluing_bound"] += 1
        for p in range(4):
            for q in range(4):
                offset = Q(1, 4)
                value = glue(p, x, offset)
                for i, w in enumerate(weights(x)):
                    if w > 0:
                        assert abs(value-local(i, q, x, offset)) <= offset+eps(p)+eps(q)
                        counts["approximate_overlap_restriction"] += 1
            for t in range(4, 11):
                inner = inner_weights(x, t)
                exact = weights(x)
                assert all(0 <= a <= b and b-a <= 2*eps(t)
                           for a, b in zip(inner, exact))
                assert sum(inner) >= delta / 2
                a = glue(p, x, Q(1, 4), inner)
                b = glue(p, x, Q(1, 4), exact)
                assert abs(a-b) <= 8*M*N*eps(t)/delta
                counts["safe_named_metric_weights"] += 1

    return {
        "status": "all exact-rational checks passed",
        "scope": "finite implementation validation, not formal or universal proof",
        "total_checks": sum(counts.values()),
        "counts": dict(sorted(counts.items())),
        "gluing_parameters": {"charts": N, "bound_M": str(M),
                               "local_L": str(L), "delta": str(delta),
                               "proved_global_L": str(C)},
        "cubic_examples": examples,
    }


if __name__ == "__main__":
    result = run_checks()
    destination = Path(__file__).resolve().parents[1] / "validation" / "continuous_validation.json"
    destination.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
