#!/usr/bin/env python3
"""Pack a finite one-relation theory into a pure-membership sentence.

This is a reference syntax transformation, not an NBG-to-modal translator.
Input formulas are finite JSON trees with tags eq, rel, not, or, exists.
Labels are nonnegative integers, with ordinary named-variable shadowing.
All input axioms must be sentences.  The result says that a nonempty set d,
with a relation coded by Kuratowski pairs in e, satisfies those axioms.

This generic wrapper does not itself establish a source theory's consistency
strength. The small synthetic test example is not a ZFC-strength theory.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path


def natural(n):
    return type(n) is int and n >= 0


def tree(value):
    """Validate JSON syntax and convert to immutable tuples."""
    if not isinstance(value, (list, tuple)) or not value:
        raise ValueError("formula must be a nonempty array")
    tag = value[0]
    if tag in ("eq", "rel"):
        if len(value) != 3 or not all(natural(x) for x in value[1:]):
            raise ValueError("atomic formulas need two natural labels")
        return tuple(value)
    if tag == "not" and len(value) == 2:
        return (tag, tree(value[1]))
    if tag == "or" and len(value) == 3:
        return (tag, tree(value[1]), tree(value[2]))
    if tag == "exists" and len(value) == 3 and natural(value[1]):
        return (tag, value[1], tree(value[2]))
    raise ValueError("unknown tag, invalid arity, or invalid label")


def labels(f):
    if f[0] in ("eq", "rel"):
        return set(f[1:])
    if f[0] == "not":
        return labels(f[1])
    if f[0] == "or":
        return labels(f[1]) | labels(f[2])
    return {f[1]} | labels(f[2])


def free(f):
    if f[0] in ("eq", "rel"):
        return set(f[1:])
    if f[0] == "not":
        return free(f[1])
    if f[0] == "or":
        return free(f[1]) | free(f[2])
    return free(f[2]) - {f[1]}


def Eq(x, y): return ("eq", x, y)
def Rel(x, y): return ("rel", x, y)
def Not(f): return ("not", f)
def Or(f, g): return ("or", f, g)
def Ex(x, f): return ("exists", x, f)
def And(f, g): return Not(Or(Not(f), Not(g)))
def Imp(f, g): return Or(Not(f), g)
def Iff(f, g): return And(Imp(f, g), Imp(g, f))
def All(x, f): return Not(Ex(x, Not(f)))


class Fresh:
    def __init__(self, start):
        self.next = start

    def get(self):
        result = self.next
        self.next += 1
        return result


def pair_set(p, x, y, fresh):
    z = fresh.get()
    return All(z, Iff(Rel(z, p), Or(Eq(z, x), Eq(z, y))))


def singleton(p, x, fresh):
    z = fresh.get()
    return All(z, Iff(Rel(z, p), Eq(z, x)))


def kuratowski(p, x, y, fresh):
    s, t = fresh.get(), fresh.get()
    return Ex(s, Ex(t, And(singleton(s, x, fresh),
                          And(pair_set(t, x, y, fresh),
                              pair_set(p, s, t, fresh)))))


def relation_atom(x, y, e, fresh):
    p = fresh.get()
    return Ex(p, And(Rel(p, e), kuratowski(p, x, y, fresh)))


def relativize(f, d, e, fresh):
    tag = f[0]
    if tag == "eq":
        return f
    if tag == "rel":
        return relation_atom(f[1], f[2], e, fresh)
    if tag == "not":
        return Not(relativize(f[1], d, e, fresh))
    if tag == "or":
        return Or(relativize(f[1], d, e, fresh),
                  relativize(f[2], d, e, fresh))
    return Ex(f[1], And(Rel(f[1], d),
                        relativize(f[2], d, e, fresh)))


def pack(axioms):
    axioms = [tree(f) for f in axioms]
    if any(free(f) for f in axioms):
        raise ValueError("each input axiom must be a sentence")
    used = set().union(*(labels(f) for f in axioms))
    fresh = Fresh(max(used, default=-1) + 1)
    d, e, x = fresh.get(), fresh.get(), fresh.get()
    body = Ex(x, Rel(x, d))
    for f in axioms:
        body = And(body, relativize(f, d, e, fresh))
    packed = Ex(d, Ex(e, body))
    if free(packed):
        raise AssertionError("internal error: packing introduced a free label")
    return packed


def size(f):
    if f[0] in ("eq", "rel"):
        return 1
    if f[0] == "or":
        return 1 + size(f[1]) + size(f[2])
    return 1 + size(f[-1])


def evaluate(f, domain, relation, env=None):
    """Ordinary finite semantics, used only for regression tests."""
    env = {} if env is None else dict(env)
    tag = f[0]
    if tag == "eq":
        return env[f[1]] == env[f[2]]
    if tag == "rel":
        return (env[f[1]], env[f[2]]) in relation
    if tag == "not":
        return not evaluate(f[1], domain, relation, env)
    if tag == "or":
        return (evaluate(f[1], domain, relation, env)
                or evaluate(f[2], domain, relation, env))
    for value in domain:
        local = dict(env)
        local[f[1]] = value
        if evaluate(f[2], domain, relation, local):
            return True
    return False


def induced_relation(domain, ambient, relation, e):
    kp = kuratowski(0, 1, 2, Fresh(3))
    return {(x, y) for x in domain for y in domain
            if any((p, e) in relation and evaluate(
                kp, ambient, relation, {0: p, 1: x, 2: y})
                for p in ambient)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="JSON with an axioms array")
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    source = json.loads(args.input.read_text())
    axioms = source["axioms"]
    target = pack(axioms)
    result = {"source_name": source.get("name", "unnamed finite theory"),
              "status": "membership wrapper only; modal translation absent",
              "source_axiom_count": len(axioms),
              "source_formula_nodes": sum(size(tree(f)) for f in axioms),
              "packed_formula_nodes": size(target),
              "formula": target}
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "formula"}))


if __name__ == "__main__":
    main()
