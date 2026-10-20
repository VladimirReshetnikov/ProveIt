#!/usr/bin/env python3
"""Supplementary finite audit of the literal two-world K reduction.

This does not claim that a finite domain models K.  It compares the exact
native template to its reduced ordinary formula for every matrix truth table
on a two-element domain.  The unbounded HC model is proved in the companion
mathematical note.
"""
from functools import cache
from itertools import product
from pathlib import Path
import json

D = range(2)
I = lambda x, y: ("I", x, y)
Q = lambda i, x: ("Q", i, x)
R = lambda i, j: ("R", i, j)
E = lambda i, j: ("E", i, j)
F = R(0, 0)
N = lambda x: I(x, F)
X = lambda i, x: N(Q(i, N(x)))
CHI = ("chi",)


def template(a, b, c):
    r = R(b, c)
    s = Q(c, I(R(c, a), R(c, b)))
    w = Q(b, I(CHI, N(Q(b, I(CHI, N(r))))))
    u = Q(a, I(s, w))
    h = Q(b, I(r, N(Q(a, I(CHI, N(u))))))
    v = I(R(a, b), Q(c, R(a, b)))
    bundle = N(I(v, Q(c, I(h, N(w)))))
    return {"r": r, "s": s, "w": w, "u": u, "h": h,
            "v": v, "bundle": bundle}


def replace(v, i, d):
    return v[:i] + (d,) + v[i + 1:]


def audit_case(edges, a, b, chi0, chi1):
    c = 3
    terms = template(a, b, c)
    matrices = (chi0, chi1)

    def rel(x, y):
        return (x, y) in edges

    def matrix(t, v):
        # Rows are output values; columns are input values.
        return bool(matrices[t] & (1 << (2 * v[b] + v[a])))

    @cache
    def ev(term, t, v):
        op = term[0]
        if op == "chi":
            return matrix(t, v)
        if op == "I":
            return not ev(term[1], t, v) or ev(term[2], t, v)
        if op == "Q":
            return all(ev(term[2], s, replace(v, term[1], d))
                       for s in range(t, 2) for d in D)
        if op == "R":
            x, y = v[term[1]], v[term[2]]
            return rel(x, y) or (t == 1 and x == y)
        if op == "E":
            return v[term[1]] == v[term[2]]
        raise AssertionError(op)

    def sub(v):
        p, z = v[a], v[b]
        return all(not rel(x, p) or rel(x, z) for x in D) and (
            p == z or rel(p, z))

    def req(v):
        # Keep actual overwrite semantics, including a=b.
        return all(not matrix(0, replace(v, b, y)) or
                   any(matrix(0, replace(v, b, z)) and rel(z, v[c])
                       for z in D) for y in D)

    def requests(v):
        return all(not sub(replace(v, a, p)) or req(replace(v, a, p))
                   for p in D)

    def support_and_requests(v):
        return any(matrix(0, replace(v, a, p)) and
                   requests(replace(v, a, p)) for p in D)

    def closure(v):
        return all(not rel(z, v[c]) or
                   support_and_requests(replace(v, b, z)) for z in D)

    def reduced_bundle(v):
        return any(closure(replace(v, c, C)) and req(replace(v, c, C))
                   for C in D)

    count = 0
    for v in product(D, repeat=4):
        assert not ev(F, 0, v) and ev(F, 1, v)
        assert ev(terms["s"], 0, v) == sub(v)
        assert ev(terms["w"], 0, v) == req(v)
        assert ev(terms["u"], 0, v) == requests(v)
        assert ev(terms["h"], 0, v) == closure(v)
        assert ev(terms["bundle"], 0, v) == reduced_bundle(v)
        assert all(ev(terms[k], 1, v) for k in ("w", "u", "h", "v", "bundle"))
        assert ev(terms["v"], 0, v)
        for i in range(4):
            for t in (0, 1):
                assert ev(I(Q(i, CHI), CHI), t, v)
                assert ev(I(CHI, Q(i, X(i, CHI))), t, v)
        count += 1

    counter_assignment = (0, 0, 1, 0)
    counter_formula = E(1, 2)
    assert not ev(I(X(1, Q(1, counter_formula)), counter_formula),
                  1, counter_assignment)
    assert not ev(I(F, counter_formula), 1, counter_assignment)
    return count


def main():
    assignments = cases = 0
    # All irreflexive binary relations on the two-element domain.
    for e01, e10 in product((False, True), repeat=2):
        edges = set()
        if e01:
            edges.add((0, 1))
        if e10:
            edges.add((1, 0))
        for a, b in ((1, 2), (1, 1)):
            for chi0, chi1 in product(range(16), repeat=2):
                assignments += audit_case(edges, a, b, chi0, chi1)
                cases += 1
    result = {
        "status": "PASS",
        "scope": "Exact finite audit of formula reduction; HC closure proved mathematically",
        "irreflexive_membership_relations": 4,
        "role_patterns": ["a != b", "a = b"],
        "matrix_tables_per_time": 16,
        "cases": cases,
        "initial_assignments": assignments,
        "literal_template_reduction": True,
        "subset_reduction": "p subseteq u and (p=u or p in u)",
        "second_time_bundle_valid": True,
        "T_valid": True,
        "dual_B_valid": True,
        "old_rho6_refuted_at_second_time": True,
        "explosion_refuted_at_second_time": True,
    }
    output = Path(__file__).with_name("t_countermodel_reduction_audit.json")
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
