#!/usr/bin/env python3
"""A complete reference search for equality-free EPSC refutations.

The schema is a fixed template with three matrix closures.  Its matrix is
never renamed or substituted by the verifier.  All quantifiers use the
same parameter domain, and negative universals choose fresh parameters.
This is a Python specification, not a small binary TM or a kernel proof.
Copyright 2026. Released under MIT-0; see ../LICENSE.txt.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from math import isqrt
import json
from pathlib import Path
from typing import Any

Formula = tuple
TRUTH: Formula = ("T",)
BOTTOM: Formula = ("B",)
HOLE: Formula = ("H",)  # private: the numeric parser cannot produce this


def nat(x: Any) -> int:
    if type(x) is not int or x < 0:
        raise ValueError("expected a natural number, not a Boolean")
    return x


def pair(x: int, y: int) -> int:
    x, y = nat(x), nat(y)
    return (x + y) * (x + y + 1) // 2 + y


def unpair(n: int) -> tuple[int, int]:
    n = nat(n)
    s = (isqrt(8 * n + 1) - 1) // 2
    y = n - s * (s + 1) // 2
    return s - y, y


def R(i: int, j: int) -> Formula:
    return ("R", nat(i), nat(j))


def I(a: Formula, b: Formula) -> Formula:
    return ("I", a, b)


def A(i: int, a: Formula) -> Formula:
    return ("A", nat(i), a)


def N(a: Formula) -> Formula:
    return I(a, BOTTOM)


def And(a: Formula, b: Formula) -> Formula:
    return N(I(a, N(b)))


def Or(a: Formula, b: Formula) -> Formula:
    return I(N(a), b)


def Ex(i: int, a: Formula) -> Formula:
    return N(A(i, N(a)))


def encode(f: Formula) -> int:
    """Exceptional-code Bottom: no extra residue class is required."""
    op = f[0]
    if f == TRUTH:
        return 0
    if f == BOTTOM:
        return 1
    if op == "R":
        return 3 * pair(f[1], f[2]) + 4
    if op == "I":
        return 3 * pair(encode(f[1]), encode(f[2]))
    if op == "A":
        return 3 * pair(f[1], encode(f[2])) + 2
    raise ValueError("schema holes and unknown constructors are not encodable")


def decode(n: int) -> Formula:
    """Total natural-code decoder, evaluated on an explicit work stack.

    Formula children are strictly smaller than their parent.  Numeric
    labels are data, not recursive formula children.  I(T,T) normalizes to T.
    """
    n = nat(n)
    pending = [(n, False)]
    done: dict[int, Formula] = {}
    while pending:
        k, finish = pending.pop()
        if k in done:
            continue
        if k == 0:
            done[k] = TRUTH
            continue
        if k == 1:
            done[k] = BOTTOM
            continue
        q, r = divmod(k, 3)
        if r == 1:
            done[k] = R(*unpair(q - 1))
            continue
        x, y = unpair(q)
        if finish:
            done[k] = I(done[x], done[y]) if r == 0 else A(x, done[y])
        else:
            pending.append((k, True))
            pending.append((y, False))
            if r == 0:
                pending.append((x, False))
    return done[n]


def parse_formula(obj: Any) -> Formula:
    """Human-facing syntax, separate from the total numeric decoder."""
    if not isinstance(obj, (list, tuple)) or not obj:
        raise ValueError("expected a formula array")
    op = obj[0]
    if op in ("T", "B") and len(obj) == 1:
        return (op,)
    if op == "R" and len(obj) == 3:
        return R(obj[1], obj[2])
    if op == "I" and len(obj) == 3:
        return I(parse_formula(obj[1]), parse_formula(obj[2]))
    if op == "A" and len(obj) == 3:
        return A(obj[1], parse_formula(obj[2]))
    raise ValueError("unknown constructor, private hole, or wrong arity")


def free_labels(f: Formula) -> set[int]:
    if f[0] == "R":
        return {f[1], f[2]}
    if f[0] == "I":
        return free_labels(f[1]) | free_labels(f[2])
    if f[0] == "A":
        return free_labels(f[2]) - {f[1]}
    return set()


def all_labels(f: Formula) -> set[int]:
    if f[0] == "R":
        return {f[1], f[2]}
    if f[0] == "I":
        return all_labels(f[1]) | all_labels(f[2])
    if f[0] == "A":
        return {f[1]} | all_labels(f[2])
    return set()


def epsc_template() -> Formula:
    """Private namespace: x=0, y=1, bound=2, hull=3, dummy=4.

    At each H, the current x/y parameters become matrix variables 0/1;
    all other matrix free parameters come from a separately captured map.
    """
    x, y, b, c, z = range(5)
    sub_y_b = A(z, I(R(z, y), R(z, b)))
    empty_x = A(z, N(R(z, x)))
    bound = A(x, Ex(b, A(y, I(HOLE, sub_y_b))))
    forward = A(x, I(Or(empty_x, R(x, c)), A(y, I(HOLE, R(y, c)))))
    support = A(y, I(R(y, c), Ex(x, HOLE)))
    return I(bound, Ex(c, And(forward, support)))


EPSC = epsc_template()
Env = tuple[tuple[int, int], ...]


def environment(pairs: Any, *, parameters: bool = False) -> Env:
    if not isinstance(pairs, (list, tuple)):
        raise ValueError("expected a finite environment list")
    result: dict[int, int] = {}
    for item in pairs:
        if not isinstance(item, (list, tuple)) or len(item) != 2:
            raise ValueError("environment entries must be pairs")
        k, v = nat(item[0]), nat(item[1])
        if k in result or (parameters and k < 2):
            raise ValueError("duplicate or reserved matrix parameter label")
        result[k] = v
    return tuple(sorted(result.items()))


def lookup(env: Env, label: int) -> int:
    return dict(env).get(label, 0)


def update(env: Env, label: int, value: int) -> Env:
    return tuple(sorted((dict(env) | {label: value}).items()))


@dataclass(frozen=True)
class Entry:
    positive: bool
    formula: Formula
    env: Env = ()
    matrix: Formula | None = None
    parameters: Env = ()

    def resolve(self) -> "Entry":
        if self.formula != HOLE:
            return self
        if self.matrix is None:
            raise ValueError("a private hole has no captured matrix")
        env = update(update(self.parameters, 0, lookup(self.env, 0)),
                     1, lookup(self.env, 1))
        return Entry(self.positive, self.matrix, env)

    def part(self, formula: Formula, positive: bool | None = None) -> "Entry":
        return Entry(self.positive if positive is None else positive,
                     formula, self.env, self.matrix, self.parameters)

    def instantiate(self, value: int) -> "Entry":
        e = self.resolve()
        if e.formula[0] != "A":
            raise ValueError("universal rule used on another constructor")
        return Entry(e.positive, e.formula[2], update(e.env, e.formula[1], value),
                     e.matrix, e.parameters)

    def atom(self) -> tuple[int, int] | None:
        e = self.resolve()
        if e.formula[0] != "R":
            return None
        return lookup(e.env, e.formula[1]), lookup(e.env, e.formula[2])


def schema_entry(matrix_code: int, parameters: Any = ()) -> Entry:
    return Entry(True, EPSC, (), decode(matrix_code),
                 environment(parameters, parameters=True))


def check_tree(roots: tuple[Entry, ...], proof: Any) -> dict[str, Any]:
    """Finite signed tableau; proof trees may add only genuine EPSC instances.

    The public refutation entry below fixes the only initial root to -Bottom.
    Freshness is per branch and tracks even unused explicit parameters.
    All inputs must be finite values; Python memory exhaustion is an error.
    """
    used = frozenset({0} | {v for e in roots for _, v in e.env + e.parameters})
    pending = [(roots, used, proof)]
    actions = leaves = axiom_steps = max_branch = 0
    while pending:
        branch, used, node = pending.pop()
        actions += 1
        max_branch = max(max_branch, len(branch))
        if not isinstance(node, (list, tuple)) or not node:
            raise ValueError("expected a finite proof node")
        tag = node[0]

        def previous(i: Any) -> Entry:
            i = nat(i)
            if i >= len(branch):
                raise ValueError("proof reference out of range")
            return branch[i].resolve()

        if tag == "close" and len(node) == 3:
            a, b = previous(node[1]), previous(node[2])
            if a.atom() is None or a.atom() != b.atom() or a.positive == b.positive:
                raise ValueError("atoms are not complementary at the same parameters")
            leaves += 1
        elif tag == "constant" and len(node) == 2:
            e = previous(node[1])
            if not ((e.positive and e.formula == BOTTOM)
                    or (not e.positive and e.formula == TRUTH)):
                raise ValueError("only +Bottom or -Truth closes")
            leaves += 1
        elif tag == "imp" and len(node) in (3, 4):
            e = previous(node[1])
            if e.formula[0] != "I":
                raise ValueError("implication rule used on another constructor")
            a, b = e.formula[1:]
            if e.positive and len(node) == 4:
                pending.append((branch + (e.part(b, True),), used, node[3]))
                pending.append((branch + (e.part(a, False),), used, node[2]))
            elif not e.positive and len(node) == 3:
                pending.append((branch + (e.part(a, True), e.part(b, False)), used, node[2]))
            else:
                raise ValueError("incorrect number of implication branches")
        elif tag == "all" and len(node) in (3, 4):
            e = previous(node[1])
            if e.positive and len(node) == 4:
                k, child = nat(node[2]), node[3]
            elif not e.positive and len(node) == 3:
                k, child = max(used) + 1, node[2]
            else:
                raise ValueError("negative universals must let the checker choose freshness")
            pending.append((branch + (e.instantiate(k),), used | {k}, child))
        elif tag == "axiom" and len(node) == 4:
            e = schema_entry(nat(node[1]), node[2])
            extra = {v for _, v in e.parameters}
            pending.append((branch + (e,), used | extra, node[3]))
            axiom_steps += 1
        else:
            raise ValueError("unknown proof operation or wrong arity")
    return {"valid": True, "actions": actions, "closed_branches": leaves,
            "schema_instances": axiom_steps, "maximum_branch_entries": max_branch}


def check_refutation(proof: Any) -> dict[str, Any]:
    """The only acceptance interface used by the consistency search."""
    result = check_tree((Entry(False, BOTTOM),), proof)
    return result | {"refutation": True}


def check_theorem(formula: Any, proof: Any) -> dict[str, Any]:
    """Separate demonstration interface; never called by search()."""
    f = parse_formula(formula)
    if free_labels(f):
        raise ValueError("the demonstration target must be closed")
    return check_tree((Entry(False, f),), proof) | {"refutation": False}


def list_decode(n: int) -> list[tuple[int, int]]:
    result = []
    while n:
        item, n = unpair(n - 1)
        label, value = unpair(item)
        result.append((label + 2, value))
    return result


def list_encode(values: list[tuple[int, int]]) -> int:
    result = 0
    for label, value in reversed(values):
        if label < 2:
            raise ValueError("reserved parameter label")
        result = 1 + pair(pair(label - 2, value), result)
    return result


def proof_decode(n: int) -> list:
    """Total finite proof-tree decoding. Every recursive child is < its parent.

    Quantifier/implication polarity is represented explicitly as a small field;
    ill-shaped combinations reject in check_tree, never loop or count as proof.
    """
    n = nat(n)
    pending = [(n, False)]
    done: dict[int, list] = {}
    while pending:
        code, finish = pending.pop()
        if code in done:
            continue
        q, tag = divmod(code, 7)
        if tag == 0:
            done[code] = ["close", *unpair(q)]
            continue
        if tag == 1:
            done[code] = ["constant", q]
            continue
        i, rest = unpair(q)
        if tag in (2, 4, 6):
            left, right = unpair(rest)
            children = (left, right) if tag == 2 else (right,)
        else:
            children = (rest,)
        if not finish:
            pending.append((code, True))
            pending.extend((child, False) for child in children)
            continue
        if tag == 2:
            done[code] = ["imp", i, done[left], done[right]]
        elif tag == 3:
            done[code] = ["imp", i, done[rest]]
        elif tag == 4:
            done[code] = ["all", i, left, done[right]]
        elif tag == 5:
            done[code] = ["all", i, done[rest]]
        else:
            done[code] = ["axiom", i, list_decode(left), done[right]]
    return done[n]


def proof_encode(p: list) -> int:
    tag = p[0]
    if tag == "close":
        return 7 * pair(p[1], p[2])
    if tag == "constant":
        return 7 * p[1] + 1
    if tag == "imp" and len(p) == 4:
        return 7 * pair(p[1], pair(proof_encode(p[2]), proof_encode(p[3]))) + 2
    if tag == "imp" and len(p) == 3:
        return 7 * pair(p[1], proof_encode(p[2])) + 3
    if tag == "all" and len(p) == 4:
        return 7 * pair(p[1], pair(p[2], proof_encode(p[3]))) + 4
    if tag == "all" and len(p) == 3:
        return 7 * pair(p[1], proof_encode(p[2])) + 5
    if tag == "axiom":
        return 7 * pair(p[1], pair(list_encode(p[2]), proof_encode(p[3]))) + 6
    raise ValueError("unknown proof production")


def search(limit: int | None = None) -> dict[str, Any]:
    n = 0
    while limit is None or n < limit:
        proof = proof_decode(n)
        try:
            result = check_refutation(proof)
        except ValueError:
            n += 1
            continue
        return {"halted": True, "certificate_code": n, "result": result}
    return {"halted": False, "candidates_checked": n,
            "scope": "bounded prefix only; not evidence of consistency"}


def evaluate(entry: Entry, relation: tuple[int, ...], assignment: dict[int, int]) -> bool:
    """Finite semantics used in independent regressions, not in proof checking.

    relation[y] is the bit set of members of y. Parameters may denote equal
    objects: syntactically fresh parameter names do not imply inequality.
    """
    e = entry.resolve()
    f = e.formula
    if f == TRUTH:
        return True
    if f == BOTTOM:
        return False
    if f[0] == "R":
        x, y = e.atom()
        return bool(relation[assignment[y]] & (1 << assignment[x]))
    if f[0] == "I":
        return not evaluate(e.part(f[1]), relation, assignment) or evaluate(e.part(f[2]), relation, assignment)
    if f[0] == "A":
        fresh = 1 + max({0} | set(assignment))
        body = e.instantiate(fresh)
        return all(evaluate(body, relation, assignment | {fresh: value}) for value in range(len(relation)))
    raise ValueError("unknown semantic constructor")


def identity_proof(positive: Entry, negative: Entry, pi: int, ni: int,
                   length: int, used: frozenset[int] = frozenset({0})) -> list:
    """Untrusted example generator. Supports alpha-equivalent closures."""
    p, n = positive.resolve(), negative.resolve()
    op = p.formula[0]
    if op != n.formula[0]:
        raise ValueError("different formula shapes")
    if op == "B":
        return ["constant", pi]
    if op == "T":
        return ["constant", ni]
    if op == "R":
        if p.atom() != n.atom():
            raise ValueError("different interpreted atoms")
        return ["close", pi, ni]
    if op == "A":
        k = max(used) + 1
        child = identity_proof(p.instantiate(k), n.instantiate(k), length + 1,
                               length, length + 2, used | {k})
        return ["all", ni, ["all", pi, k, child]]
    if op == "I":
        pa, pb = p.formula[1:]
        na, nb = n.formula[1:]
        left = identity_proof(n.part(na, True), p.part(pa, False),
                              length, length + 2, length + 3, used)
        right = identity_proof(p.part(pb, True), n.part(nb, False),
                               length + 2, length + 1, length + 3, used)
        return ["imp", ni, ["imp", pi, left, right]]
    raise ValueError("unknown identity constructor")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("certificate", nargs="?", type=Path)
    ap.add_argument("--prefix", type=int)
    args = ap.parse_args()
    if args.prefix is not None:
        print(json.dumps(search(nat(args.prefix)), indent=2))
    elif args.certificate:
        data = json.loads(args.certificate.read_text())
        if set(data) == {"proof"}:
            result = check_refutation(data["proof"])
        elif set(data) == {"theorem", "proof"}:
            result = check_theorem(data["theorem"], data["proof"])
        else:
            raise ValueError("expected exactly proof, or theorem and proof")
        print(json.dumps(result, indent=2))
    else:
        ap.error("provide a certificate file or --prefix")


if __name__ == "__main__":
    main()
