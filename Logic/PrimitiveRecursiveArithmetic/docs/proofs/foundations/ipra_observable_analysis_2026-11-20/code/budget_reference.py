#!/usr/bin/env python3
"""Exact finite producers and verifiers for the report's error budgets.

These examples check implementation consistency. Universal implications are
proved separately in the paper and the Lean finite kernel.
"""
from fractions import Fraction as Q
from pathlib import Path
import json


def dot(a, b):
    if len(a) != len(b):
        raise ValueError("dimension mismatch")
    return sum((x * y for x, y in zip(a, b)), Q(0))


def reverse_weights(matrix, sinks):
    n = len(sinks)
    if len(matrix) != n or any(len(row) != n for row in matrix):
        raise ValueError("not a square matrix")
    if any(s < 0 for s in sinks):
        raise ValueError("negative sink weight")
    for v, row in enumerate(matrix):
        if any(c < 0 for c in row) or any(row[u] != 0 for u in range(v, n)):
            raise ValueError("nonnegative strictly lower-triangular coefficients required")
    weights = [Q(0)] * n
    for u in reversed(range(n)):
        weights[u] = sinks[u] + sum((weights[v] * matrix[v][u]
                                    for v in range(u + 1, n)), Q(0))
    return weights


def forward_envelope(matrix, delta):
    n = len(delta)
    if any(d < 0 for d in delta):
        raise ValueError("negative local budget")
    reverse_weights(matrix, [Q(0)] * n)  # Validate the graph convention.
    errors = [Q(0)] * n
    for v in range(n):
        errors[v] = delta[v] + dot(matrix[v], errors)
    return errors


def certify(matrix, sinks, weights, errors, delta):
    n = len(sinks)
    if len(matrix) != n or any(len(row) != n for row in matrix):
        return False
    if any(len(x) != n for x in [weights, errors, delta]):
        return False
    if any(w < 0 for w in weights) or any(e < 0 for e in errors):
        return False
    if any(errors[v] > delta[v] + dot(matrix[v], errors) for v in range(n)):
        return False
    if any(sinks[u] + sum((weights[v] * matrix[v][u] for v in range(n)), Q(0))
           > weights[u] for u in range(n)):
        return False
    return dot(sinks, errors) <= dot(weights, delta)


def checks():
    records = []
    for n in range(1, 10):
        matrix = [[Q(((v + 2) * (u + 3)) % 7, 4) if u < v else Q(0)
                   for u in range(n)] for v in range(n)]
        sinks = [Q(int(v == n - 1)) for v in range(n)]
        weights = reverse_weights(matrix, sinks)
        epsilon = Q(1, 1024)
        delta = [epsilon / (n * max(Q(1), w)) for w in weights]
        errors = forward_envelope(matrix, delta)
        assert certify(matrix, sinks, weights, errors, delta)
        assert dot(sinks, errors) == dot(weights, delta) <= epsilon
        assert certify(matrix, sinks, [2 * w for w in weights], errors, delta)
        records.append({"nodes": n, "output_error": str(dot(sinks, errors)),
                        "target": str(epsilon), "exact_balance": True})

    matrix = [[Q(0), Q(2)], [Q(1, 8), Q(0)]]
    delta = [Q(3, 250), Q(9, 4000)]
    errors = [Q(11, 500), Q(1, 200)]
    sinks = [Q(0), Q(1)]
    weights = [Q(1, 6), Q(4, 3)]
    assert certify(matrix, sinks, weights, errors, delta)
    assert dot(weights, delta) == Q(1, 200)
    assert not certify(matrix, sinks, [Q(0), Q(1)], errors, delta)
    try:
        reverse_weights(matrix, sinks)
    except ValueError:
        pass
    else:
        raise AssertionError("cyclic graph accepted by acyclic producer")
    return {"status": "passed", "arithmetic": "fractions.Fraction",
            "acyclic_cases": records,
            "cyclic_observable": {"weights": list(map(str, weights)),
                                  "bound": str(dot(weights, delta)),
                                  "invalid_weights_rejected": True},
            "scope": "finite example validation; theorem proved separately"}


if __name__ == "__main__":
    result = checks()
    target = Path(__file__).resolve().parents[1] / "evidence" / "budget_checks.json"
    target.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "cases": len(result["acyclic_cases"]),
                      "cyclic_bound": result["cyclic_observable"]["bound"]}))
