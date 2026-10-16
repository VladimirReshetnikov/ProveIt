#!/usr/bin/env python3
"""Exact formula-tree counts for explicitly stated Boolean macro policies.

These counts are not Turing-machine state counts and exclude variable payloads,
proof inference, DAG sharing, codec tags, enumeration and all backend costs.
"""

import argparse
import json
from pathlib import Path


def rel(x, y):
    return ("R", x, y)


BOT = ("F",)
MATRIX = ("M",)


def imp(a, b):
    return ("imp", a, b)


def forall(v, a):
    return ("all", v, a)


def neg(a):
    return imp(a, BOT)


def conjunction(a, b):
    return neg(imp(a, neg(b)))


def disjunction(a, b):
    return imp(neg(a), b)


def exists(v, a):
    return neg(forall(v, neg(a)))


def iff(a, b, primitive=False):
    if primitive:
        return ("iff", a, b)
    return conjunction(imp(a, b), imp(b, a))


def empty(x):
    return forall("z", neg(rel("z", x)))


def sub(x, b):
    return forall("z", imp(rel("z", x), rel("z", b)))


def profile(x, y, full=True, primitive_iff=False):
    incoming = iff(rel("z", x), rel("z", y), primitive_iff)
    if not full:
        return forall("z", incoming)
    outgoing = iff(rel(x, "z"), rel(y, "z"), primitive_iff)
    return forall("z", conjunction(incoming, outgoing))


def outgoing(x, y):
    return forall("z", imp(rel(x, "z"), rel(y, "z")))


def pair_or_adjoin(eq, adjoin, primitive_iff=False):
    lhs = rel("y", "c")
    first = rel("y", "a") if adjoin else eq("y", "a")
    body = iff(lhs, disjunction(first, eq("y", "b")), primitive_iff)
    return forall("a", forall("b", exists("c", forall("y", body))))


def closure(parameter_slots, fixedpoint=False, primitive_iff=False):
    bounded = forall("x", exists("b", forall("y", imp(MATRIX, sub("y", "b")))))
    active = disjunction(empty("x"), rel("x", "c"))
    if fixedpoint:
        rhs = exists("x", conjunction(active, MATRIX))
        hull = forall("y", iff(rel("y", "c"), rhs, primitive_iff))
    else:
        recurrent = forall("x", forall("y", imp(conjunction(active, MATRIX), rel("y", "c"))))
        support = forall("y", imp(rel("y", "c"), exists("x", MATRIX)))
        hull = conjunction(recurrent, support)
    result = imp(bounded, exists("c", hull))
    for i in reversed(range(parameter_slots)):
        result = forall(f"p{i}", result)
    return result


def size(term):
    if term[0] in {"R", "F", "M"}:
        return 1
    if term[0] == "all":
        return 1 + size(term[2])
    return 1 + size(term[1]) + size(term[2])


def count_matrix(term):
    if term[0] == "M":
        return 1
    if term[0] in {"R", "F"}:
        return 0
    if term[0] == "all":
        return count_matrix(term[2])
    return count_matrix(term[1]) + count_matrix(term[2])


def metric(primitive_iff):
    o = lambda x, y: profile(x, y, full=True, primitive_iff=primitive_iff)
    d = lambda x, y: profile(x, y, full=False, primitive_iff=primitive_iff)
    terms = {
        "U": outgoing("a", "b"),
        "D": d("a", "b"),
        "O": o("a", "b"),
        "AU": pair_or_adjoin(outgoing, True, primitive_iff),
        "UPair": pair_or_adjoin(outgoing, False, primitive_iff),
        "OAdj": pair_or_adjoin(o, True, primitive_iff),
        "OPair": pair_or_adjoin(o, False, primitive_iff),
        "EPSC1": closure(1, False, primitive_iff),
        "EPSC2": closure(2, False, primitive_iff),
        "XFP1": closure(1, True, primitive_iff),
        "XFP2": closure(2, True, primitive_iff),
    }
    return {name: {"tree_nodes": size(term), "matrix_occurrences": count_matrix(term)}
            for name, term in terms.items()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = {
        "policy": {
            "neg": "A -> Bottom",
            "and": "not(A -> not B)",
            "or": "not A -> B",
            "exists": "not forall not",
            "iff_expanded": "(A -> B) and (B -> A)",
            "each_R_Bottom_matrix_leaf": 1,
            "each_connective_or_quantifier": 1,
        },
        "imp_bottom_all": metric(False),
        "optional_primitive_iff": metric(True),
        "scope": "Formula-tree nodes only, not machine states; adding iff requires its full codec and logic cost.",
    }
    assert result["imp_bottom_all"]["AU"]["tree_nodes"] == 33
    assert result["imp_bottom_all"]["OPair"]["tree_nodes"] == 135
    rendered = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
