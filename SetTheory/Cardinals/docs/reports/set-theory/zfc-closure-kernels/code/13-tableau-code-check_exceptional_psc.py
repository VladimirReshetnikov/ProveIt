#!/usr/bin/env python3
"""Audit variable capture in the two exceptional ungated raw PSC instances.

Truth at code0 and relative falsity Rel(0,0) at code1 are interpreted exactly.
The finite cases check the symbolic claims proved in psc_compiler_notes.md.
"""
import argparse
from itertools import product
import json
from pathlib import Path


def imp(a, b): return ("imp", a, b)
def rel(a, b): return ("rel", a, b)
def eq(a, b): return ("eq", a, b)
def all_(a, b): return ("all", a, b)
def not_(a): return imp(a, 1)
def ex(a, b): return not_(all_(a, not_(b)))
def and_(a, b): return not_(imp(a, not_(b)))
def or_(a, b): return imp(not_(a), b)


def formula(kind):
    c = "c"
    sb = all_(0, ex(c, all_(1, imp(c, all_(0, imp(rel(0, 1), rel(0, c)))))))
    seed = eq(0, 1) if kind == "point" else all_(c, imp(rel(c, 0), rel(c, 1)))
    closed = all_(0, imp(or_(seed, rel(0, c)), all_(1, imp(c, rel(1, c)))))
    support = all_(1, imp(rel(1, c), ex(0, c)))
    return imp(sb, all_(1, ex(c, and_(closed, support))))


def evaluate(f, domain, relation, c, env):
    if f == "c":
        return True if c == 0 else (env[0], env[0]) in relation
    if f == 1:
        return (env[0], env[0]) in relation
    kind, a, b = f
    index = lambda x: c if x == "c" else x
    if kind == "rel":
        return (env[index(a)], env[index(b)]) in relation
    if kind == "eq":
        return env[index(a)] == env[index(b)]
    if kind == "imp":
        return not evaluate(a, domain, relation, c, env) or evaluate(b, domain, relation, c, env)
    if kind == "all":
        return all(evaluate(b, domain, relation, c, env | {index(a): x}) for x in domain)
    raise ValueError(f)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    counts = {"point": [0, 0], "subset": [0, 0]}
    for size in (1, 2, 3):
        domain = range(size)
        edges = [(a, b) for a in domain for b in domain if a != b]
        for bits in range(1 << len(edges)):
            relation = {e for i, e in enumerate(edges) if bits >> i & 1}
            for kind, c in product(counts, (0, 1)):
                value = evaluate(formula(kind), domain, relation, c, {0: 0, 1: 0})
                # The c0 exceptional row is precisely the existence of a
                # membership edge in this irreflexive finite semantics.
                assert value == (bool(relation) if c == 0 else True)
                counts[kind][c] += 1
    result = {"status": "passed", "cases_by_seed_and_c": counts,
              "total_cases": sum(sum(x) for x in counts.values()),
              "expected_c0": "true exactly when the irreflexive relation has at least one edge",
              "expected_c1": "always true in a nonempty irreflexive model",
              "scope": "Finite binder-sensitive semantic diagnostics; the universal justification is the elementary symbolic proof in psc_compiler_notes.md."}
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
