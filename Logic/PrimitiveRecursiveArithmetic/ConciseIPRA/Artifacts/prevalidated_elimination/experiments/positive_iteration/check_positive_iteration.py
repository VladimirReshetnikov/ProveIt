"""Finite transcription checks for theory_positive_iteration.tex.

No proof checker imports this script. The theorems rest on their written
structural proofs. Evaluation caps deliberately skip huge sample values.
"""

import itertools
import json
import random


def classify(term, arity):
    tag, *fields = term
    if tag == "zero":
        return "constant", frozenset()
    if tag == "var":
        assert 0 <= fields[0] < arity
        return "projection", frozenset(fields)
    if tag == "succ":
        kind, deps = classify(fields[0], arity)
        return ("growth", deps) if deps else ("constant", deps)
    assert tag == "iterate"
    count, seed, body = fields
    body_kind, body_deps = classify(body, arity + 1)
    if body_kind == "constant":
        return body_kind, body_deps
    if body_kind == "projection":
        return classify(seed, arity) if arity in body_deps else (body_kind, body_deps)
    if arity not in body_deps:
        return body_kind, body_deps
    deps = (body_deps - {arity}) | classify(count, arity)[1] | classify(seed, arity)[1]
    return ("growth", deps) if deps else ("constant", deps)


class EvaluationCap(Exception):
    pass


def evaluate(term, env, budget):
    budget[0] -= 1
    if budget[0] < 0:
        raise EvaluationCap
    tag, *fields = term
    if tag == "zero":
        value = 0
    elif tag == "var":
        value = env[fields[0]]
    elif tag == "succ":
        value = evaluate(fields[0], env, budget) + 1
    else:
        assert tag == "iterate"
        count = evaluate(fields[0], env, budget)
        value = evaluate(fields[1], env, budget)
        for _ in range(count + 1):
            value = evaluate(fields[2], env + (value,), budget)
    if value > 100_000:
        raise EvaluationCap
    return value


def random_term(rng, depth, arity):
    if depth == 0:
        return ("zero",) if rng.randrange(arity + 1) == arity else ("var", rng.randrange(arity))
    kind = rng.randrange(5)
    if kind == 0:
        return ("zero",)
    if kind == 1:
        return ("var", rng.randrange(arity))
    if kind == 2:
        return ("succ", random_term(rng, depth - 1, arity))
    return (
        "iterate",
        random_term(rng, depth - 1, arity),
        random_term(rng, depth - 1, arity),
        random_term(rng, depth - 1, arity + 1),
    )


def positive_iterate(n, a, update):
    for _ in range(n + 1):
        a = update(a)
    return a


def q(a, b):
    return positive_iterate(a, b, lambda u: u + 1)


def m(a, b):
    return positive_iterate(a, 0, lambda u: q(u, b))


def pair(a, b):
    return positive_iterate(a, q(b, b) + 1, lambda u: q(u, u))


def main():
    rng = random.Random(20261110)
    terms = [random_term(rng, rng.randrange(1, 5), 2) for _ in range(1000)]
    grid = list(itertools.product(range(4), repeat=2))
    counts = {"constant": 0, "projection": 0, "growth": 0}
    evaluations = skipped = comparisons = 0
    for term in terms:
        kind, deps = classify(term, 2)
        counts[kind] += 1
        values = {}
        for env in grid:
            try:
                value = evaluate(term, env, [10_000])
            except EvaluationCap:
                skipped += 1
                continue
            values[env] = value
            evaluations += 1
            if kind == "projection":
                assert value == env[next(iter(deps))]
            elif kind == "growth":
                assert deps and all(value >= env[j] + 1 for j in deps)
        if kind == "constant":
            assert len(set(values.values())) <= 1
        for env, value in values.items():
            for j in range(2):
                successor = tuple(x + (i == j) for i, x in enumerate(env))
                if successor not in values:
                    continue
                next_value = values[successor]
                comparisons += 1
                assert next_value > value if j in deps else next_value == value

    paired = {(a, b): pair(a, b) for a, b in itertools.product(range(12), repeat=2)}
    assert len(set(paired.values())) == len(paired)
    for (a, b), value in paired.items():
        assert value + 1 == 2 ** (a + 1) * (2 * b + 3)

    ring_checks = 0
    for a, b, c, d in itertools.product(range(5), repeat=4):
        assert (q(a, d) == q(c, b)) == (a - b == c - d)
        add = q(a, c), q(b, d)
        multiply = q(m(a, c), m(b, d)), q(m(a, d), m(b, c))
        assert add[0] - add[1] == (a - b) + (c - d)
        assert multiply[0] - multiply[1] == (a - b) * (c - d)
        ring_checks += 1

    print(json.dumps({
        "status": "PASS",
        "scope": "finite standard-N transcription checks, not formal proof verification",
        "sample_seed": 20261110,
        "sample_terms": len(terms),
        "class_counts": counts,
        "completed_evaluations": evaluations,
        "capped_evaluations_skipped": skipped,
        "coordinate_comparisons": comparisons,
        "pairing_inputs": len(paired),
        "ring_input_quadruples": ring_checks,
    }, indent=2))


if __name__ == "__main__":
    main()
