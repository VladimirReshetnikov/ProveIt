"""Construct a genuine pure-bound/CLOSE certificate of an empty EPSC hull.

Temporary hypotheses exist only inside this offline proof-producing script.
The exported certificate contains exclusively the eight production tags of
rule_search.check_dag. Every hypothesis is eliminated by K/S deduction.
"""
from __future__ import annotations

from functools import lru_cache
import json
from pathlib import Path

import debruijn_kernel as k
import rule_search as r


def leaf(op, *args):
    return (op, *args)


def mp(p, q):
    return ("MP", p, q)


@lru_cache(None)
def conclusion(p):
    op = p[0]
    if op == "HYP":
        return p[1]
    if op in ("K", "S", "C", "UI", "UD"):
        return getattr(k, op)(*p[1:])
    if op == "GEN":
        return k.all_(conclusion(p[1]))
    if op == "CLOSE":
        assert conclusion(p[2]) == r.bound(p[1])
        return r.hull(p[1])
    if op == "UCLOSE":
        beta = r.extract_bound(conclusion(p[1]))
        assert beta is not None
        return r.protected_hull(beta)
    a = conclusion(p[1])
    arrow = conclusion(p[2])
    assert arrow and arrow % 3 == 2
    x, y = k.unpair((arrow - 2) // 3)
    assert x == a
    return y


def identity(a):
    x = leaf("K", a, k.imp(a, a))
    y = leaf("K", a, a)
    s = leaf("S", a, k.imp(a, a), a)
    return mp(y, mp(x, s))


@lru_cache(None)
def occurs(p, a):
    if p[0] == "HYP":
        return p[1] == a
    if p[0] == "MP":
        return occurs(p[1], a) or occurs(p[2], a)
    if p[0] in ("GEN", "UCLOSE"):
        return occurs(p[1], a)
    if p[0] == "CLOSE":
        return occurs(p[2], a)
    return False


@lru_cache(None)
def discharge(p, a):
    if not occurs(p, a):
        return mp(p, leaf("K", conclusion(p), a))
    if p[0] == "HYP":
        return identity(a)
    if p[0] != "MP":
        raise ValueError("deduction is only used on propositional proof steps")
    antecedent = conclusion(p[1])
    target = conclusion(p)
    return mp(discharge(p[1], a),
              mp(discharge(p[2], a), leaf("S", a, antecedent, target)))


def flip(a, b, c):
    """Pure K/S proof of (a->(b->c))->(b->(a->c))."""
    h = k.imp(a, k.imp(b, c))
    p = mp(leaf("HYP", b), mp(leaf("HYP", a), leaf("HYP", h)))
    for assumption in (a, b, h):
        p = discharge(p, assumption)
    assert conclusion(p) == k.imp(h, k.imp(b, k.imp(a, c)))
    return p


def explosion(a):
    # C(a,Bottom) consumes (not a -> not Bottom), derived from Bottom->Bottom.
    truth = k.imp(0, 0)
    antecedent = mp(identity(0), leaf("K", truth, k.neg(a)))
    result = mp(antecedent, leaf("C", a, 0))
    assert conclusion(result) == k.imp(0, a)
    return result


def existential_intro(body, j, instance_proof):
    expected = k.subst0(body, j)
    assert conclusion(instance_proof) == expected
    p = k.all_(k.neg(body))
    ui = leaf("UI", k.neg(body), j)
    arrow = mp(ui, flip(p, expected, 0))
    result = mp(instance_proof, arrow)
    assert conclusion(result) == k.ex(body)
    return result


def make(presentation="protected"):
    if presentation not in ("protected", "rule"):
        raise ValueError("certificate supports the two rule presentations")
    sub = r.subset(0, 1)
    inner = k.imp(0, sub)
    forall_y = leaf("GEN", explosion(sub))
    body_b = k.all_(inner)
    assert conclusion(forall_y) == body_b
    assert k.subst0(body_b, 0) == body_b
    exists_b = existential_intro(body_b, 0, forall_y)
    bound_proof = leaf("GEN", exists_b)
    assert conclusion(bound_proof) == r.bound(0)
    full = (leaf("UCLOSE", bound_proof) if presentation == "protected"
            else leaf("CLOSE", 0, bound_proof))

    rows = []
    indices = {}

    def export(p):
        if p in indices:
            return indices[p]
        op = p[0]
        if op == "HYP":
            raise AssertionError("undischarged hypothesis cannot be exported")
        if op in ("K", "S", "C", "UD"):
            row = [op, *(format(a, "x") for a in p[1:])]
        elif op == "UI":
            row = [op, format(p[1], "x"), p[2]]
        elif op == "GEN":
            row = [op, export(p[1])]
        elif op == "UCLOSE":
            row = ["CLOSE", export(p[1])]
        elif op == "MP":
            row = [op, export(p[1]), export(p[2])]
        else:
            row = [op, format(p[1], "x"), export(p[2])]
        index = len(rows)
        rows.append(row)
        indices[p] = index
        return index

    export(full)
    checked = r.check_dag(rows, logic_only=True, presentation=presentation)
    expected = r.protected_hull(0) if presentation == "protected" else r.hull(0)
    assert checked[-1] == expected != 0
    return {
        "description": "Pure first-order proof of B_false, followed by the selected closure rule; the conclusion is an empty-hull theorem, not a refutation. In protected mode its matrix is forall b false.",
        "presentation": presentation,
        "formula_encoding": "Lowercase hexadecimal numerals for the bijective Bottom0/positive-three-constructor codec.",
        "proof": rows,
    }


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--presentation", choices=("protected", "rule"), default="protected")
    args = parser.parse_args()
    result = make(args.presentation)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "proof_lines": len(result["proof"]),
                      "pure_bound_checked": True, "refutation": False}))
