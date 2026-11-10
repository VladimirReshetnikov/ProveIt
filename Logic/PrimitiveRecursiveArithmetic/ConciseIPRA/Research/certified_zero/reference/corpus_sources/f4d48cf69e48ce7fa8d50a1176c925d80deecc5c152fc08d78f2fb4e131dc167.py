"""Finite intended-model diagnostics, not a proof about all models."""
import json
from pathlib import Path


def G(a, b):
    return b + 1 if a == 0 else a - 1


def J(n, update):
    value = 0
    for _ in range(n):
        value = update(value)
    return value


def W(a):
    return G(a, 0)


def M(n, a):
    return J(n, lambda _: a)


def Z(n):
    return W(M(n, 1))


def C(n, a, b):
    return W(G(M(Z(n), a + 2), b))


def I(n, a, update):
    return W(J(n + 1, lambda u: G(M(Z(u), a + 2), update(W(u)))))


def L(n, a):
    return I(n, a, W)


def E(a, b):
    return Z(W(G(L(b, a + 2), 1)))


def run():
    counts = {}

    def check(group, condition):
        if not condition:
            raise RuntimeError("failed diagnostic: " + group)
        counts[group] = counts.get(group, 0) + 1

    for n in range(9):
        for a in range(9):
            for b in range(9):
                check("selector", C(n, a, b) == (a if n == 0 else b))
    updates = [lambda u: u, lambda u: u + 1, W, Z,
               lambda u: 3, lambda u: G(u, 4)]
    for update in updates:
        for a in range(8):
            expected = a
            for n in range(7):
                check("initializer", I(n, a, update) == expected)
                expected = update(expected)
    for n in range(25):
        for a in range(25):
            check("rotation", L(n, W(a)) == W(L(n, a)))
    for n in range(33):
        for k in range(7):
            check("fixed_diagonal", L(n, n + k) == k)
    for a in range(21):
        for b in range(21):
            check("actual_equality_characteristic", E(a, b) == int(a == b))
            reference = L(b, a + 2) == 2
            for k in range(2, 8):
                check("equivalent_faithful_levels", (L(b, a + k) == k) == reference)
    counterexamples = []
    for k in (0, 1):
        a, b = 0, 2
        value = L(b, a + k)
        check("cycle_level_counterexamples", value == k and a != b)
        counterexamples.append({"level": k, "a": a, "b": b, "observed": value})
    result = {
        "scope": "Finite intended-model checks; the report supplies the universal internal proofs.",
        "checks": counts, "total": sum(counts.values()),
        "cycle_level_counterexamples": counterexamples,
        "bounds": {"selector_arguments": 8, "initializer_counter": 6,
                   "rotation_arguments": 24, "diagonal_counter": 32,
                   "equality_arguments": 20, "largest_faithful_level": 7},
    }
    destination = Path(__file__).resolve().parents[1] / "evidence" / "observation_checks.json"
    destination.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    return result


if __name__ == "__main__":
    run()
