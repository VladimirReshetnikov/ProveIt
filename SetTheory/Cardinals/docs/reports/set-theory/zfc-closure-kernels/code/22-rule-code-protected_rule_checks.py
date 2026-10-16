#!/usr/bin/env python3
"""Independent finite semantics for the protected-witness closure rule.

This checks its pure logical boundedness lemma and its precise de Bruijn
environment map, not theory consistency or any literal machine.
"""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

import closure_rule_checks as base


def beta_value(code, n, x, b, y):
    return bool(code & (1 << (x * n * n + b * n + y)))


def premise(n, prof, code):
    return all(any(all(not beta_value(code, n, x, b, y) or
                       prof[y] & ~prof[b] == 0
                       for y in range(n)) for b in range(n)) for x in range(n))


def protect(n, code):
    return [sum(all(beta_value(code, n, x, b, y) for b in range(n)) << y
                for y in range(n)) for x in range(n)]


def db_eval(f, n, membership, env):
    kind = f[0]
    if kind == "B":
        return False
    if kind == "E":
        return bool(membership & (1 << (env[f[1]] * n + env[f[2]])))
    if kind == "I":
        return not db_eval(f[1], n, membership, env) or db_eval(f[2], n, membership, env)
    if kind == "A":
        return all(db_eval(f[1], n, membership, [z, *env]) for z in range(n))
    raise ValueError(kind)


def protected_map(f, depth=0):
    """Old free context [y,b,x,p...] -> new [b,x,y,C,p...]."""
    def index(i):
        if i < depth:
            return i
        j = i - depth
        target = (2, 0, 1)[j] if j < 3 else j + 1
        return depth + target
    kind = f[0]
    if kind == "E":
        return ("E", index(f[1]), index(f[2]))
    if kind == "B":
        return f
    if kind == "I":
        return ("I", protected_map(f[1], depth), protected_map(f[2], depth))
    if kind == "A":
        return ("A", protected_map(f[1], depth + 1))
    raise ValueError(kind)


def check():
    boundedness_cases = 0
    independent_bound_specializations = 0
    for n in (1, 2):
        for membership in range(1 << (n * n)):
            prof = base.profiles(n, membership)
            for beta in range(1 << (n * n * n)):
                t = premise(n, prof, beta)
                rows = protect(n, beta)
                assert not t or base.direct_bound(n, prof, rows)
                boundedness_cases += 1
            for rho in range(1 << (n * n)):
                rows = base.fibers(n, rho)
                beta = sum(bool(rows[x] & (1 << y)) << (x * n * n + b * n + y)
                           for x in range(n) for b in range(n) for y in range(n))
                assert premise(n, prof, beta) == base.direct_bound(n, prof, rows)
                assert protect(n, beta) == rows
                independent_bound_specializations += 1

    # Unprotected projection is not justified. In the diagonal 2-object
    # graph, beta(x,b,y;p)=E(b,p) with p=1 has a vacuous local bound b=0.
    # Substituting p for b instead produces every output and has no bound.
    n, membership = 2, 9
    prof = base.profiles(n, membership)
    beta = sum((b == 1) << (x * n * n + b * n + y)
               for x in range(n) for b in range(n) for y in range(n))
    assert premise(n, prof, beta)
    assert base.direct_bound(n, prof, protect(n, beta))
    assert not base.direct_bound(n, prof, [3, 3])

    # The rule remains a nonlogical rule. T_false is logically valid;
    # H_false fails in the one-object universal membership structure.
    assert premise(1, [1], 0)
    assert not base.direct_hull(1, [1], protect(1, 0))

    examples = [
        ("B",), ("E", 0, 1), ("E", 1, 2), ("E", 3, 1), ("E", 4, 0),
        ("I", ("E", 0, 1), ("E", 2, 3)),
        ("A", ("E", 0, 2)),
        ("A", ("I", ("E", 0, 2), ("A", ("E", 1, 5)))),
        ("I", ("A", ("E", 1, 0)), ("A", ("E", 0, 5))),
    ]
    environment_cases = 0
    closed_protection_cases = 0
    for n in (1, 2):
        for membership in range(1 << (n * n)):
            for f in examples:
                mapped = protected_map(f)
                for x, y, b, hull, p0, p1 in itertools.product(range(n), repeat=6):
                    assert db_eval(f, n, membership, [y, b, x, p0, p1]) == \
                           db_eval(mapped, n, membership, [b, x, y, hull, p0, p1])
                    environment_cases += 1
                for x, y, hull, p0, p1 in itertools.product(range(n), repeat=5):
                    expected = all(db_eval(f, n, membership, [y, b, x, p0, p1])
                                   for b in range(n))
                    assert db_eval(("A", mapped), n, membership,
                                   [x, y, hull, p0, p1]) == expected
                    closed_protection_cases += 1

    return {
        "status": "PASS",
        "scope": "Pure logical boundedness and de Bruijn environment regression checks; not consistency or a machine endpoint.",
        "all_graph_ternary_beta_cases_domains_1_2": boundedness_cases,
        "bound_independent_specializations": independent_bound_specializations,
        "debruijn_environment_cases": environment_cases,
        "debruijn_closed_protection_cases": closed_protection_cases,
        "debruijn_examples": len(examples),
        "free_index_map": {"0": 2, "1": 0, "2": 1, "j>=3": "j+1"},
        "unprotected_projection_counterexample": {
            "domain": [0, 1], "membership_edges": [[0, 0], [1, 1]],
            "matrix": "beta(x,b,y;p)=E(b,p), p=1",
            "T_beta": True, "B_protected": True, "B_projection_b_equals_p": False,
        },
        "rule_genuinely_nonlogical": {
            "model": "one-object universal membership; beta=false",
            "T_beta": True, "H_protected": False,
        },
    }


def main():
    if not __debug__:
        raise SystemExit("Assertions must be enabled.")
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output", type=Path)
    args = p.parse_args()
    result = check()
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    print(text)


if __name__ == "__main__":
    main()
