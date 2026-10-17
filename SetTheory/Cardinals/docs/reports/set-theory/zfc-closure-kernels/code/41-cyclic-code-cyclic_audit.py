#!/usr/bin/env python3
"""Independent finite diagnostics for the cyclic presentation.

This is not a proof of the infinite algebraic theorem.  It exhausts the
specified finite Boolean set-algebra constructions and checks independent
evaluations of term translations.  No ZFC-refutation target is supplied.
"""
from __future__ import annotations

import itertools
import json
import random
from pathlib import Path


def partitions(n):
    """All equivalence partitions, each represented by a tuple of masks."""
    def rec(i, blocks):
        if i == n:
            yield tuple(blocks)
            return
        for j in range(len(blocks)):
            out = list(blocks)
            out[j] |= 1 << i
            yield from rec(i + 1, out)
        yield from rec(i + 1, blocks + [1 << i])
    yield from rec(0, [])


def closure_table(n, partition):
    return tuple(sum(b for b in partition if b & x) for x in range(1 << n))


def permutation_table(n, perm):
    return tuple(sum(1 << perm[i] for i in range(n) if x & (1 << i))
                 for x in range(1 << n))


def compose(f, g):
    return tuple(f[g[x]] for x in range(len(g)))


def commute(f, g):
    return compose(f, g) == compose(g, f)


def eval_source(t, p, ops, top):
    if t == "p":
        return p
    op = t[0]
    if op == "+":
        return eval_source(t[1], p, ops, top) | eval_source(t[2], p, ops, top)
    x = eval_source(t[1], p, ops, top)
    return (top ^ x) if op == "-" else ops["fgh".index(op)][x]


def translate(t):
    if t == "p":
        return t
    op = t[0]
    if op == "+":
        return ("+", translate(t[1]), translate(t[2]))
    x = translate(t[1])
    if op == "-":
        return ("-", x)
    if op == "f":
        return ("c", x)
    if op == "g":
        return ("r", ("c", ("r", ("r", x))))
    if op == "h":
        return ("r", ("r", ("c", ("r", x))))
    raise ValueError(op)


def eval_lift(t, p, ops, top):
    if t == "p":
        return p
    op = t[0]
    if op == "+":
        x, y = eval_lift(t[1], p, ops, top), eval_lift(t[2], p, ops, top)
        return tuple(a | b for a, b in zip(x, y))
    x = eval_lift(t[1], p, ops, top)
    if op == "-":
        return tuple(top ^ a for a in x)
    if op == "r":
        return (x[1], x[2], x[0])
    if op == "c":
        return tuple(ops[i][x[i]] for i in range(3))
    raise ValueError(op)


def random_term(rng, depth):
    if depth == 0 or rng.randrange(5) == 0:
        return "p"
    op = rng.choice(("+", "-", "f", "g", "h"))
    x = random_term(rng, depth - 1)
    return (op, x, random_term(rng, depth - 1)) if op == "+" else (op, x)


def run():
    out = {"scope": "finite regression, not an infinite proof or machine calibration"}
    sizes = []
    for n in range(1, 6):
        top = (1 << n) - 1
        ident = tuple(range(1 << n))
        cs = [closure_table(n, b) for b in partitions(n)]
        rotations = []
        for perm in itertools.permutations(range(n)):
            if all(perm[perm[perm[i]]] == i for i in range(n)):
                r = permutation_table(n, perm)
                assert compose(compose(r, r), r) == ident
                assert all(r[x | y] == (r[x] | r[y])
                           for x in ident for y in ident)
                assert all(r[top ^ x] == (top ^ r[x]) for x in ident)
                rotations.append(r)
        accepted = 0
        for c in cs:
            assert all((x | c[x]) == c[x] for x in ident)
            assert all(c[x | y] == (c[x] | c[y]) for x in ident for y in ident)
            assert all(c[top ^ c[x]] == (top ^ c[x]) for x in ident)
            assert all(c[c[x]] == c[x] for x in ident)
            for r in rotations:
                rr = compose(r, r)
                c1 = compose(r, compose(c, rr))
                c2 = compose(rr, compose(c, r))
                if commute(c, c1):
                    accepted += 1
                    assert commute(c, c2) and commute(c1, c2)
        sizes.append({"atoms": n, "partitions": len(cs),
                      "order_divides_3_permutations": len(rotations),
                      "single_commutator_models": accepted})
    out["finite_cyclic_models"] = sizes

    # Exhaustive check: on a four-element Boolean algebra, the three closure
    # equations imply idempotence.  All unary maps, not only partition maps.
    closure_models = []
    for c in itertools.product(range(4), repeat=4):
        if not all((x | c[x]) == c[x] for x in range(4)):
            continue
        if not all(c[x | y] == (c[x] | c[y]) for x in range(4) for y in range(4)):
            continue
        if not all(c[3 ^ c[x]] == (3 ^ c[x]) for x in range(4)):
            continue
        assert all(c[c[x]] == c[x] for x in range(4))
        closure_models.append(c)
    out["closure_axiom_exhaustion"] = {
        "boolean_elements": 4, "unary_maps_tested": 4**4,
        "models": len(closure_models), "idempotence_failures": 0}

    # Source generators may be arbitrary; countermodel transfer is checked
    # at diagonal lifts.  The diagonal is not assumed closed under c.
    n, top = 3, 7
    cs = [closure_table(n, b) for b in partitions(n)]
    rng = random.Random(20261017)
    terms = ["p", ("f", "p"), ("g", "p"), ("h", "p")]
    terms += [random_term(rng, 6) for _ in range(300)]
    translated = [translate(t) for t in terms]
    triples, comparisons = 0, 0
    for ops in itertools.product(cs, repeat=3):
        if not all(commute(ops[i], ops[j]) for i in range(3) for j in range(i)):
            continue
        triples += 1
        for p in range(8):
            diag = (p, p, p)
            for t, tr in zip(terms, translated):
                actual = eval_lift(tr, diag, ops, top)
                expected = tuple(eval_source(t, p, ops[i:] + ops[:i], top)
                                 for i in range(3))
                assert actual == expected
                comparisons += 1
    out["product_lift"] = {"source_atoms": 3, "commuting_triples": triples,
                           "terms": len(terms), "valuations_each": 8,
                           "translation_comparisons": comparisons}

    # Ground r(p)=p does not collapse the conjugate closure operators.
    ident = tuple(range(4))
    universal = (0, 3, 3, 3)
    ops, diag = (ident, universal, ident), (1, 1, 1)
    fp = eval_lift(translate(("f", "p")), diag, ops, 3)
    gp = eval_lift(translate(("g", "p")), diag, ops, 3)
    assert eval_lift(("r", "p"), diag, ops, 3) == diag
    assert fp != gp and fp[0] == 1 and gp[0] == 3
    out["ground_generator_witness"] = {
        "p": diag, "rp": diag, "c0p": fp, "c1p": gp,
        "distinct_closures_despite_ground_invariance": True}
    return out


if __name__ == "__main__":
    result = run()
    target = Path(__file__).with_name("cyclic_audit_results.json")
    target.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
