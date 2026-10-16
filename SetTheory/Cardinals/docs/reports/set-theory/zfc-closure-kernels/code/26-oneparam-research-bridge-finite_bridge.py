#!/usr/bin/env python3
"""Finite witness interface for the pinned public 253-state ZFC searcher.

This is a research reference implementation, not a proof of the machine's
consistency equivalence.  It makes both endpoint witness predicates explicit:
finite binary TM configurations and annotated finite natural-deduction proofs.

The formula/axiom interface is transcribed from jeff87654/busy-beaver at
0d544f2a2e3c18f12278441a74b7879f31cbe856:
  ZF/stdzf/vendor/undecidability/theories/FOL/{Deduction/FullND,Sets/minZF}.v
  ZF/stdzf/coq/Std_iface.v
  ZF/stdzf_r3/regcon/MinZF.v       (ax_reg')
  ZF/stdzf_r3/zfc/Z_wo.v          (ACmat, ax_ac)
  ZF/m254/coq/settheory/S_def.v   (S0, SIR)

All proof nodes contain their context and conclusion. Premise indices must
point backwards. Schema leaves carry their matrix and closure count; the
checker never searches an infinite axiom scheme or invokes a theorem prover.
This recursive Python program is for finite diagnostics, not an executable
total infinite search: sufficiently deep finite syntax may raise RecursionError.
Such failures are not caught and misreported as invalid proofs. The mathematical
primitive-recursion claim concerns ideal total finite-tree/number algorithms,
not the Python runtime or its recursion/resource limits.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence
import argparse
import hashlib
import json
from pathlib import Path
import random


# A term is a de Bruijn index. There are no function symbols.
# Formula tags: bot, mem, eq, imp, and, or, all, ex.
Form = tuple
BOT: Form = ("bot",)


def nat(x) -> bool:
    return type(x) is int and x >= 0


def Mem(x: int, y: int) -> Form: return ("mem", x, y)
def Eq(x: int, y: int) -> Form: return ("eq", x, y)
def Imp(p: Form, q: Form) -> Form: return ("imp", p, q)
def And(p: Form, q: Form) -> Form: return ("and", p, q)
def Or(p: Form, q: Form) -> Form: return ("or", p, q)
def All(p: Form) -> Form: return ("all", p)
def Ex(p: Form) -> Form: return ("ex", p)
def Neg(p: Form) -> Form: return Imp(p, BOT)
def Iff(p: Form, q: Form) -> Form: return And(Imp(p, q), Imp(q, p))


def form_ok(p) -> bool:
    if not isinstance(p, tuple) or not p:
        return False
    tag = p[0]
    if tag == "bot":
        return len(p) == 1
    if tag in ("mem", "eq"):
        return len(p) == 3 and nat(p[1]) and nat(p[2])
    if tag in ("imp", "and", "or"):
        return len(p) == 3 and form_ok(p[1]) and form_ok(p[2])
    if tag in ("all", "ex"):
        return len(p) == 2 and form_ok(p[1])
    return False


def subst(p: Form, sigma: Callable[[int], int]) -> Form:
    """Capture-avoiding simultaneous substitution; sigma maps free indices."""
    tag = p[0]
    if tag == "bot":
        return p
    if tag in ("mem", "eq"):
        return (tag, sigma(p[1]), sigma(p[2]))
    if tag in ("imp", "and", "or"):
        return (tag, subst(p[1], sigma), subst(p[2], sigma))
    if tag in ("all", "ex"):
        return (tag, subst(p[1], lambda k: 0 if k == 0 else sigma(k - 1) + 1))
    raise ValueError("invalid formula")


def shift(p: Form) -> Form:
    return subst(p, lambda k: k + 1)


def inst(p: Form, t: int) -> Form:
    """The library's phi[t..]: remove the outer binder, substituting t."""
    return subst(p, lambda k: t if k == 0 else k - 1)


def close(p: Form, n: int) -> Form:
    for _ in range(n):
        p = All(p)
    return p


def bounded(p: Form, depth: int = 0) -> bool:
    """Every free de Bruijn index is strictly below depth."""
    tag = p[0]
    if tag == "bot":
        return True
    if tag in ("mem", "eq"):
        return p[1] < depth and p[2] < depth
    if tag in ("imp", "and", "or"):
        return bounded(p[1], depth) and bounded(p[2], depth)
    return bounded(p[1], depth + 1)


def schema_sub(p: Form, prefix: Sequence[int], tail: int) -> Form:
    return subst(p, lambda k: prefix[k] if k < len(prefix) else tail + k - len(prefix))


def sub(x: int, y: int) -> Form:
    return All(Imp(Mem(0, x + 1), Mem(0, y + 1)))


def is_empty(t: int) -> Form:
    return All(Neg(Mem(0, t + 1)))


def is_pair(x: int, y: int, t: int) -> Form:
    return All(Iff(Mem(0, t + 1), Or(Eq(0, x + 1), Eq(0, y + 1))))


def is_union(x: int, t: int) -> Form:
    return All(Iff(Mem(0, t + 1), Ex(And(Mem(0, x + 2), Mem(1, 0)))))


def is_power(x: int, t: int) -> Form:
    return All(Iff(Mem(0, t + 1), sub(0, x + 1)))


def is_sigma(x: int, t: int) -> Form:
    return All(Iff(Mem(0, t + 1), Or(Mem(0, x + 1), Eq(0, x + 1))))


def is_inductive(t: int) -> Form:
    return And(Ex(And(is_empty(0), Mem(0, t + 1))),
               All(Imp(Mem(0, t + 1), Ex(And(is_sigma(1, 0), Mem(0, t + 2))))))


def is_omega(t: int) -> Form:
    return And(is_inductive(t), All(Imp(is_inductive(0), sub(t + 1, 0))))


def ax_separation(p: Form) -> Form:
    return All(Ex(All(Iff(Mem(0, 1), And(Mem(0, 2), schema_sub(p, [0], 3))))))


def ax_replacement(p: Form) -> Form:
    functional = All(All(All(Imp(schema_sub(p, [2, 1], 3),
        Imp(schema_sub(p, [2, 0], 3), Eq(1, 0))))))
    image = All(Ex(All(Iff(Mem(0, 1),
        Ex(And(Mem(0, 3), schema_sub(p, [0, 1], 4)))))))
    return Imp(functional, image)


def ax_gic(p: Form) -> Form:
    covers = All(Imp(Mem(0, 2), All(Imp(schema_sub(p, [1, 0], 4),
        Ex(And(schema_sub(p, [2, 0], 5), Mem(0, 3)))))))
    no_extra = All(Imp(Mem(0, 1), Ex(schema_sub(p, [0, 1], 4))))
    return All(Ex(And(covers, no_extra)))


def ac_matrix(x: int) -> Form:
    nonempty = All(Imp(Mem(0, x + 1), Ex(Mem(0, 1))))
    disjoint = All(Imp(Mem(0, x + 1), All(Imp(Mem(0, x + 2),
        Imp(Neg(Eq(1, 0)), Neg(Ex(And(Mem(0, 2), Mem(0, 1)))))))))
    chooses = Ex(All(Imp(Mem(0, x + 2), Ex(And(Mem(0, 1), And(Mem(0, 2),
        All(Imp(Mem(0, 2), Imp(Mem(0, 3), Eq(0, 1))))))))))
    return Imp(nonempty, Imp(disjoint, chooses))


AXIOMS = {
    "refl": All(Eq(0, 0)),
    "sym": All(All(Imp(Eq(1, 0), Eq(0, 1)))),
    "trans": All(All(All(Imp(Eq(2, 1), Imp(Eq(1, 0), Eq(2, 0)))))),
    "eq_elem": close(Imp(Eq(3, 1), Imp(Eq(2, 0), Imp(Mem(3, 2), Mem(1, 0)))), 4),
    "ext": All(All(Imp(sub(1, 0), Imp(sub(0, 1), Eq(1, 0))))),
    "empty": Ex(is_empty(0)),
    "pair": All(All(Ex(is_pair(2, 1, 0)))),
    "union": All(Ex(is_union(1, 0))),
    "power": All(Ex(is_power(1, 0))),
    "infinity": Ex(is_omega(0)),
    "reg": All(Imp(Ex(Mem(0, 1)), Ex(And(Mem(0, 1),
        All(Imp(Mem(0, 1), Neg(Mem(0, 2)))))))),
    "ac": All(ac_matrix(0)),
    "ir": All(Neg(Mem(0, 0))),
    "cp": All(Ex(And(Mem(1, 0), All(Imp(Mem(0, 1), And(
        All(Imp(Mem(0, 1), Mem(0, 2))),
        Ex(And(Mem(0, 2), All(Imp(All(Imp(Mem(0, 1), Mem(0, 3))), Mem(0, 1))))))))))),
}
EQUALITY = {"refl", "sym", "trans", "eq_elem"}
ZF_BASE = EQUALITY | {"ext", "empty", "pair", "union", "power", "infinity"}
THEORIES = {
    "ZFc": ZF_BASE | {"sep", "rep"},
    "ZFc+Reg": ZF_BASE | {"sep", "rep", "reg"},
    "ZFc+AC": ZF_BASE | {"sep", "rep", "ac"},
    "ZFc+Reg+AC": ZF_BASE | {"sep", "rep", "reg", "ac"},
    "S0": EQUALITY | {"cp", "gic"},
    "SIR": EQUALITY | {"cp", "gic", "ir"},
}


@dataclass(frozen=True)
class AxiomWitness:
    kind: str
    matrix: Form | None = None
    closure: int = 0


def axiom_formula(theory: str, witness: AxiomWitness) -> Form | None:
    if theory not in THEORIES or witness.kind not in THEORIES[theory]:
        return None
    if not nat(witness.closure):
        return None
    if witness.kind in ("sep", "rep", "gic"):
        if not form_ok(witness.matrix):
            return None
        constructor = {"sep": ax_separation, "rep": ax_replacement, "gic": ax_gic}[witness.kind]
        result = close(constructor(witness.matrix), witness.closure)
        return result if bounded(result) else None
    if witness.matrix is not None or witness.closure != 0:
        return None
    return AXIOMS[witness.kind]


@dataclass(frozen=True)
class Node:
    rule: str
    context: tuple[Form, ...]
    conclusion: Form
    premises: tuple[int, ...] = ()
    term: int | None = None


ARITIES = {"II": 1, "IE": 2, "AllI": 1, "AllE": 1, "ExI": 1,
           "ExE": 2, "Exp": 1, "Ctx": 0, "CI": 2, "CE1": 1,
           "CE2": 1, "DI1": 1, "DI2": 1, "DE": 3, "Pc": 0}


def check_nodes(nodes: Sequence[Node], classical: bool = True) -> bool:
    """Check all fifteen FullND constructors, including both shift conditions."""
    if not nodes:
        return False
    for i, n in enumerate(nodes):
        if not isinstance(n, Node) or n.rule not in ARITIES:
            return False
        if not isinstance(n.context, tuple) or not all(form_ok(p) for p in n.context):
            return False
        if not form_ok(n.conclusion) or len(n.premises) != ARITIES[n.rule]:
            return False
        if not all(nat(j) and j < i for j in n.premises):
            return False
        if n.rule in ("AllE", "ExI"):
            if not nat(n.term):
                return False
        elif n.term is not None:
            return False
        a, f, r = n.context, n.conclusion, n.rule
        ps = [nodes[j] for j in n.premises]

        def sequent(k, ctx, goal):
            return ps[k].context == ctx and ps[k].conclusion == goal

        def same_context():
            return all(p.context == a for p in ps)

        good = False
        if r == "Ctx":
            good = f in a
        elif r == "Pc":
            good = (classical and f[0] == "imp" and f[1][0] == "imp"
                and f[1][1][0] == "imp" and f[1][1][1] == f[2]
                and f[1][2] == f[2])
        elif r == "II":
            good = f[0] == "imp" and sequent(0, (f[1],) + a, f[2])
        elif r == "IE":
            pf = ps[0].conclusion
            good = same_context() and pf[0] == "imp" and pf[2] == f and ps[1].conclusion == pf[1]
        elif r == "AllI":
            good = f[0] == "all" and sequent(0, tuple(map(shift, a)), f[1])
        elif r == "AllE":
            pf = ps[0].conclusion
            good = same_context() and pf[0] == "all" and f == inst(pf[1], n.term)
        elif r == "ExI":
            good = f[0] == "ex" and sequent(0, a, inst(f[1], n.term))
        elif r == "ExE":
            pf = ps[0].conclusion
            good = (ps[0].context == a and pf[0] == "ex"
                and sequent(1, (pf[1],) + tuple(map(shift, a)), shift(f)))
        elif r == "Exp":
            good = sequent(0, a, BOT)
        elif r == "CI":
            good = f[0] == "and" and sequent(0, a, f[1]) and sequent(1, a, f[2])
        elif r in ("CE1", "CE2"):
            pf = ps[0].conclusion
            good = same_context() and pf[0] == "and" and f == pf[1 if r == "CE1" else 2]
        elif r in ("DI1", "DI2"):
            good = f[0] == "or" and sequent(0, a, f[1 if r == "DI1" else 2])
        elif r == "DE":
            pf = ps[0].conclusion
            good = (ps[0].context == a and pf[0] == "or"
                and sequent(1, (pf[1],) + a, f) and sequent(2, (pf[2],) + a, f))
        if not good:
            return False
    return True


def check_theorem(theory: str, axioms: Sequence[AxiomWitness], nodes: Sequence[Node],
                  conclusion: Form) -> bool:
    if theory not in THEORIES or not check_nodes(nodes):
        return False
    context = tuple(axiom_formula(theory, w) for w in axioms)
    return None not in context and nodes[-1].context == context and nodes[-1].conclusion == conclusion


def check_refutation(theory: str, axioms: Sequence[AxiomWitness], nodes: Sequence[Node]) -> bool:
    return check_theorem(theory, axioms, nodes, BOT)


def pair(x: int, y: int) -> int:
    return (x + y) * (x + y + 1) // 2 + y


def unpair(n: int) -> tuple[int, int]:
    # isqrt is an efficient implementation of a bounded primitive-recursive search.
    from math import isqrt
    diagonal = (isqrt(8 * n + 1) - 1) // 2
    y = n - diagonal * (diagonal + 1) // 2
    return diagonal - y, y


TAGS = ("bot", "mem", "eq", "imp", "and", "or", "all", "ex")


def form_code(p: Form) -> int:
    """New endpoint code, NOT the machine's self-referential four-tag code."""
    tag = p[0]
    if tag == "bot":
        payload = 0
    elif tag in ("mem", "eq"):
        payload = pair(p[1], p[2])
    elif tag in ("imp", "and", "or"):
        payload = pair(form_code(p[1]), form_code(p[2]))
    else:
        payload = form_code(p[1])
    return 1 + TAGS.index(tag) + 8 * payload


def decode_form(n: int) -> Form | None:
    if not nat(n) or n == 0:
        return None
    payload, tag_number = divmod(n - 1, 8)
    tag = TAGS[tag_number]
    if tag == "bot":
        return BOT if payload == 0 else None
    if tag in ("mem", "eq"):
        x, y = unpair(payload)
        return (tag, x, y)
    if tag in ("all", "ex"):
        p = decode_form(payload)
        return (tag, p) if p is not None else None
    x, y = unpair(payload)
    p, q = decode_form(x), decode_form(y)
    return (tag, p, q) if p is not None and q is not None else None


def list_code(values: Sequence[int]) -> int:
    result = 0
    for value in reversed(values):
        result = 1 + pair(value, result)
    return result


def decode_list(n: int) -> list[int] | None:
    if not nat(n):
        return None
    result = []
    while n:
        value, n = unpair(n - 1)
        result.append(value)
    return result


AXIOM_TAGS = tuple(AXIOMS) + ("sep", "rep", "gic")
RULE_TAGS = tuple(ARITIES)


def axiom_code(w: AxiomWitness) -> int:
    matrix_code = 0 if w.matrix is None else form_code(w.matrix)
    return pair(AXIOM_TAGS.index(w.kind), pair(matrix_code, w.closure))


def decode_axiom(n: int) -> AxiomWitness | None:
    kind, payload = unpair(n)
    if kind >= len(AXIOM_TAGS):
        return None
    matrix_code, closure = unpair(payload)
    matrix = decode_form(matrix_code) if matrix_code else None
    if matrix_code and matrix is None:
        return None
    return AxiomWitness(AXIOM_TAGS[kind], matrix, closure)


def node_code(n: Node) -> int:
    return pair(RULE_TAGS.index(n.rule), pair(list_code([form_code(p) for p in n.context]),
        pair(form_code(n.conclusion), pair(list_code(n.premises),
        0 if n.term is None else n.term + 1))))


def decode_node(n: int) -> Node | None:
    rule, payload = unpair(n)
    if rule >= len(RULE_TAGS):
        return None
    context_code, payload = unpair(payload)
    conclusion_code, payload = unpair(payload)
    premises_code, term_code = unpair(payload)
    context = tuple(decode_form(p) for p in decode_list(context_code))
    conclusion = decode_form(conclusion_code)
    if None in context or conclusion is None:
        return None
    return Node(RULE_TAGS[rule], context, conclusion, tuple(decode_list(premises_code)),
        None if term_code == 0 else term_code - 1)


def certificate_code(axioms: Sequence[AxiomWitness], nodes: Sequence[Node]) -> int:
    return pair(list_code([axiom_code(w) for w in axioms]),
                list_code([node_code(n) for n in nodes]))


def decode_certificate(n: int):
    if not nat(n):
        return None
    ax_code, nd_code = unpair(n)
    axioms = tuple(decode_axiom(w) for w in decode_list(ax_code))
    nodes = tuple(decode_node(p) for p in decode_list(nd_code))
    if None in axioms or None in nodes:
        return None
    return axioms, nodes


def refutation_predicate(theory: str, n: int) -> bool:
    """The explicit arithmetic endpoint R_T(n), with malformed codes rejected."""
    decoded = decode_certificate(n)
    return decoded is not None and check_refutation(theory, *decoded)


# A configuration is (q,left_bits,current_symbol,right_bits).
# In both bit stacks the nearest cell occupies the low bit.
Configuration = tuple[int, int, int, int]
Transition = tuple[int, str, int]


def tm_step(table: dict[tuple[int, int], Transition], c: Configuration) -> Configuration | None:
    q, left, symbol, right = c
    transition = table.get((q, symbol))
    if transition is None:
        return None
    write, direction, target = transition
    if direction == "R":
        return target, 2 * left + write, right % 2, right // 2
    return target, left // 2, left % 2, 2 * right + write


def tm_run(table, steps: int, start: Configuration = (0, 0, 0, 0)):
    """Returns reached configuration and # transitions; no transition executes at halt."""
    c, executed, head = start, 0, 0
    for _ in range(steps):
        nxt = tm_step(table, c)
        if nxt is None:
            break
        head += 1 if table[(c[0], c[2])][1] == "R" else -1
        c, executed = nxt, executed + 1
    return c, executed, head


def halted_within(table, steps: int) -> bool:
    c, _, _ = tm_run(table, steps)
    return (c[0], c[2]) not in table


def parse_table(path: str):
    """Read explicit q s write L/R target rows; no implicit deletion/renaming."""
    result = {}
    for line in Path(path).read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        q, s, write, direction, target = line.split()
        q, s, write, target = map(int, (q, s, write, target))
        if s not in (0, 1) or write not in (0, 1) or direction not in ("L", "R"):
            raise ValueError("invalid binary transition")
        if (q, s) in result or min(q, target) < 0:
            raise ValueError("duplicate or negative transition")
        result[(q, s)] = (write, direction, target)
    return result


def self_test() -> dict:
    p, q, r = Mem(0, 1), Eq(0, 1), Mem(1, 0)
    cases = {}

    def ctx(a, f): return Node("Ctx", tuple(a), f)
    def add(name, nodes):
        assert check_nodes(nodes), name
        cases[name] = True

    add("Ctx", [ctx([p], p)])
    add("II", [ctx([p], p), Node("II", (), Imp(p, p), (0,))])
    a = (Imp(p, q), p)
    add("IE", [ctx(a, Imp(p, q)), ctx(a, p), Node("IE", a, q, (0, 1))])
    add("AllI", [ctx([shift(p)], shift(p)), Node("AllI", (p,), All(shift(p)), (0,))])
    add("AllE", [ctx([All(p)], All(p)), Node("AllE", (All(p),), inst(p, 4), (0,), 4)])
    add("ExI", [ctx([inst(p, 4)], inst(p, 4)), Node("ExI", (inst(p, 4),), Ex(p), (0,), 4)])
    a = (Ex(p), q)
    add("ExE", [ctx(a, Ex(p)), ctx((p,) + tuple(map(shift, a)), shift(q)),
        Node("ExE", a, q, (0, 1))])
    add("Exp", [ctx([BOT], BOT), Node("Exp", (BOT,), p, (0,))])
    a = (p, q)
    add("CI", [ctx(a, p), ctx(a, q), Node("CI", a, And(p, q), (0, 1))])
    for name, goal in (("CE1", p), ("CE2", q)):
        add(name, [ctx([And(p, q)], And(p, q)), Node(name, (And(p, q),), goal, (0,))])
    for name, goal in (("DI1", p), ("DI2", q)):
        add(name, [ctx([goal], goal), Node(name, (goal,), Or(p, q), (0,))])
    a = (Or(p, q), r)
    add("DE", [ctx(a, Or(p, q)), ctx((p,) + a, r), ctx((q,) + a, r), Node("DE", a, r, (0, 1, 2))])
    peirce = Imp(Imp(Imp(p, q), p), p)
    add("Pc", [Node("Pc", (), peirce)])
    assert not check_nodes([Node("Pc", (), peirce)], classical=False)

    negative = {
        "unshifted_AllI_context": [ctx([p], p), Node("AllI", (p,), All(p), (0,))],
        "leaked_ExE_witness": [ctx([Ex(p)], Ex(p)), ctx((p, shift(Ex(p))), p),
            Node("ExE", (Ex(p),), p, (0, 1))],
        "cyclic_premise": [Node("II", (), Imp(p, p), (0,))],
        "invalid_Peirce": [Node("Pc", (), Imp(Imp(Imp(p, q), q), p))],
        "invented_context_leaf": [ctx([], BOT)],
    }
    for name, proof in negative.items():
        assert not check_nodes(proof), name

    assert all(form_ok(p) and bounded(p) for p in AXIOMS.values())
    for mode in THEORIES:
        for tag in THEORIES[mode] - {"sep", "rep", "gic"}:
            assert axiom_formula(mode, AxiomWitness(tag)) is not None
    for mode in ("ZFc", "ZFc+Reg", "ZFc+AC", "ZFc+Reg+AC"):
        assert axiom_formula(mode, AxiomWitness("sep", Mem(0, 1), 0)) is None
        assert axiom_formula(mode, AxiomWitness("sep", Mem(0, 1), 1)) is not None
        assert axiom_formula(mode, AxiomWitness("rep", Mem(0, 2), 0)) is None
        assert axiom_formula(mode, AxiomWitness("rep", Mem(0, 2), 1)) is not None
    assert axiom_formula("SIR", AxiomWitness("gic", Mem(0, 2), 0)) is None
    assert axiom_formula("SIR", AxiomWitness("gic", Mem(0, 2), 1)) is not None
    assert axiom_formula("ZFc", AxiomWitness("reg")) is None
    assert axiom_formula("ZFc+AC", AxiomWitness("reg")) is None
    assert axiom_formula("ZFc+Reg+AC", AxiomWitness("reg")) == AXIOMS["reg"]
    assert axiom_formula("S0", AxiomWitness("ir")) is None
    assert axiom_formula("SIR", AxiomWitness("ir")) == AXIOMS["ir"]
    assert axiom_formula("ZFc", AxiomWitness("refl", closure=1)) is None
    refl_proof = [ctx([AXIOMS["refl"]], AXIOMS["refl"])]
    assert check_theorem("ZFc+Reg+AC", [AxiomWitness("refl")], refl_proof, AXIOMS["refl"])
    assert not check_refutation("ZFc+Reg+AC", [AxiomWitness("refl")], refl_proof)
    assert not check_theorem("ZFc", [AxiomWitness("empty")], refl_proof, AXIOMS["refl"])
    ref_witnesses = (AxiomWitness("refl"),)
    ref_code = certificate_code(ref_witnesses, refl_proof)
    assert decode_certificate(ref_code) == (ref_witnesses, tuple(refl_proof))
    assert not refutation_predicate("ZFc+Reg+AC", ref_code)
    assert not refutation_predicate("ZFc+Reg+AC", 0)
    assert not refutation_predicate("ZFc+Reg+AC", -1)
    assert check_nodes([ctx([BOT], BOT)])
    assert not check_refutation("ZFc+Reg+AC", [AxiomWitness("refl")], [ctx([BOT], BOT)])

    samples = [BOT, p, q, All(p), Ex(Imp(p, q)), Imp(All(p), q),
        All(And(Mem(0, 1), Eq(1, 0)))]
    for f in samples:
        assert decode_form(form_code(f)) == f
        assert subst(f, lambda k: k) == f
    assert decode_form(0) is None
    assert decode_form(9) is None  # bot tag with nonzero payload

    # Independent finite tape implementation to test low-bit orientation.
    rng = random.Random(253)
    checks = 0
    for _ in range(100):
        states = rng.randrange(2, 8)
        table = {(i, s): (rng.randrange(2), rng.choice(("L", "R")), rng.randrange(states))
            for i in range(states) for s in (0, 1) if rng.randrange(8)}
        c, tape, state, head = (0, 0, 0, 0), {}, 0, 0
        for _ in range(100):
            packed = tm_step(table, c)
            transition = table.get((state, tape.get(head, 0)))
            assert (packed is None) == (transition is None)
            checks += 1
            if transition is None:
                break
            write, direction, state = transition
            if write:
                tape[head] = write
            else:
                tape.pop(head, None)
            head += 1 if direction == "R" else -1
            left = sum(1 << (head - k - 1) for k in tape if k < head)
            right = sum(1 << (k - head - 1) for k in tape if k > head)
            c = packed
            assert c == (state, left, tape.get(head, 0), right)
    assert halted_within({}, 0)
    assert not halted_within({(0, 0): (0, "R", 0)}, 100)
    assert halted_within({(0, 0): (1, "R", 1)}, 1)
    return {"FullND_rules_checked": sorted(cases), "negative_proof_cases": sorted(negative),
        "axiom_closedness_and_theory_boundary_checks": "pass",
        "schema_closure_checks": "pass", "formula_codec_roundtrips": len(samples),
        "certificate_codec_roundtrip": "pass",
        "packed_vs_sparse_transition_comparisons": checks,
        "scope": "finite witness interfaces only; no uniform machine/theory transports established",
        "implementation_scope": "recursive Python finite diagnostics for ideal total PR syntax algorithms; "
                                "not an executable total infinite search",
        "recursion_policy": "deep finite syntax may raise RecursionError; errors are not treated as invalid proofs"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--machine", help="optional explicit binary transition table")
    parser.add_argument("--steps", type=int, default=0)
    args = parser.parse_args()
    report = {"self_test": self_test()}
    if args.machine:
        if args.steps < 0:
            parser.error("steps must be nonnegative")
        table = parse_table(args.machine)
        c, executed, head = tm_run(table, args.steps)
        report["finite_run"] = {
            "file_sha256": hashlib.sha256(Path(args.machine).read_bytes()).hexdigest(),
            "requested_steps": args.steps, "executed_transitions": executed,
            "state": c[0], "head": head, "symbol": c[2],
            "left_bits": c[1], "right_bits": c[3],
            "halted": (c[0], c[2]) not in table,
        }
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
