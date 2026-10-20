#!/usr/bin/env python3
"""Exact finite diagnostics; no solver or external package is required.

These structures refute particular modal proof steps. They are not models
of the full native seed-K theory, and do not settle its consistency strength.
"""
import itertools
import json


def verify_modal(H, top, bottom, le, meet, imp, Q):
    neg = lambda a: imp(a, bottom)
    assert Q[top] == top and Q[bottom] == bottom
    for a, b in itertools.product(H, repeat=2):
        assert Q[meet(a, b)] == meet(Q[a], Q[b])
        assert le(Q[imp(a, b)], imp(Q[a], Q[b]))
    for a in H:
        assert le(neg(Q[neg(Q[a])]), a)  # B6
        if neg(neg(imp(a, Q[a]))) == top:
            assert neg(neg(a)) == a     # proved persistence lemma
    return neg


def product_chains():
    H = list(itertools.product(range(3), repeat=2))  # 0, m=1, top=2
    top, bottom = (2, 2), (0, 0)
    le = lambda a, b: all(x <= y for x, y in zip(a, b))
    meet = lambda a, b: tuple(min(x, y) for x, y in zip(a, b))
    imp = lambda a, b: tuple(2 if x <= y else y for x, y in zip(a, b))
    f = lambda x, y: 0 if x < 2 else 1 if y < 2 else 2
    Q = {(x, y): (f(x, y), f(y, x)) for x, y in H}
    neg = verify_modal(H, top, bottom, le, meet, imp, Q)
    A = (2, 0)
    assert neg(neg(imp(A, Q[A]))) == top
    assert imp(A, Q[A]) != top
    assert neg(neg(A)) == A
    assert neg(neg(Q[A])) != Q[A]
    return {
        "algebra": "H3 x H3; m represented by 1 and chain top by 2",
        "elements": len(H),
        "A": A, "Q_A": Q[A], "NN_Q_A": neg(neg(Q[A])),
        "NN_persistence": neg(neg(imp(A, Q[A]))),
        "persistence": imp(A, Q[A]),
        "Q": [[a, Q[a]] for a in H],
    }


def commuting_quantifiers():
    # Upsets of the poset with upper cones encoded by these bit masks.
    above = [9, 6, 4, 8]
    H = [a for a in range(16)
         if all(not (a >> i & 1) or above[i] & a == above[i]
                for i in range(4))]
    assert H == [0, 4, 6, 8, 9, 12, 13, 14, 15]
    Q = dict(zip(H, [0, 0, 9, 0, 4, 0, 4, 9, 15]))
    R = dict(zip(H, [0, 0, 8, 0, 0, 0, 0, 8, 15]))
    le = lambda a, b: a & ~b == 0
    meet = lambda a, b: a & b
    imp = lambda a, b: sum(1 << i for i in range(4)
                           if above[i] & a & ~b == 0)
    neg = verify_modal(H, 15, 0, le, meet, imp, Q)
    verify_modal(H, 15, 0, le, meet, imp, R)
    assert all(Q[R[a]] == R[Q[a]] for a in H)
    nn = lambda a: neg(neg(a))
    qb, rb = lambda a: nn(Q[a]), lambda a: nn(R[a])
    witnesses = [{"A": a, "Qbar_Rbar_A": qb(rb(a)),
                  "Rbar_Qbar_A": rb(qb(a))}
                 for a in H if nn(a) == a and qb(rb(a)) != rb(qb(a))]
    assert witnesses
    return {"above": above, "H": H, "Q": Q, "R": R,
            "regular_elements": [a for a in H if nn(a) == a],
            "booleanized_commutation_failures": witnesses}


if __name__ == "__main__":
    print(json.dumps({"status": "FINITE_MODAL_DIAGNOSTICS_PASS",
                      "scope": "Modal subtheory only; no full-K countermodel claim",
                      "product_chains": product_chains(),
                      "commuting_quantifiers": commuting_quantifiers()},
                     indent=2))
