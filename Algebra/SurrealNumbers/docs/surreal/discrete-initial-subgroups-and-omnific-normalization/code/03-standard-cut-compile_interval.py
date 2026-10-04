#!/usr/bin/env python3
"""An explicit single-infinite-bound, quadratic-atomic arithmetic compiler.

The input is a typed syntax tree, not an arbitrary Python expression or an
untrusted string. Build input trees with the public constructors below.
The output is a formula tree: this program does not evaluate infinite bounds.
Python 3.10+, standard library only.
"""
from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Mapping


@dataclass(frozen=True)
class Term:
    kind: str
    value: int | str | None = None
    args: tuple[Term, ...] = ()


@dataclass(frozen=True)
class Formula:
    kind: str
    args: tuple[Formula, ...] = ()
    left: Term | None = None
    right: Term | None = None
    variable: str | None = None
    bound: Term | None = None


def V(name: str) -> Term:
    if not name or not name.isidentifier():
        raise ValueError("A variable name must be a nonempty identifier")
    return Term("var", name)


def C(n: int) -> Term:
    if not isinstance(n, int) or n < 0:
        raise ValueError("Constants must be natural numbers")
    return Term("const", n)


def Add(a: Term, b: Term) -> Term:
    return Term("add", args=(a, b))


def Mul(a: Term, b: Term) -> Term:
    return Term("mul", args=(a, b))


def Atom(kind: str, a: Term, b: Term) -> Formula:
    if kind not in {"eq", "lt", "le"}:
        raise ValueError("Unknown atomic relation")
    return Formula(kind, left=a, right=b)


def Eq(a: Term, b: Term) -> Formula:
    return Atom("eq", a, b)


def Lt(a: Term, b: Term) -> Formula:
    return Atom("lt", a, b)


def Le(a: Term, b: Term) -> Formula:
    return Atom("le", a, b)


def Not(a: Formula) -> Formula:
    return Formula("not", args=(a,))


def And(*args: Formula) -> Formula:
    if not args:
        return Eq(C(0), C(0))
    return Formula("and", args=tuple(args))


def Or(*args: Formula) -> Formula:
    if not args:
        return Not(Eq(C(0), C(0)))
    return Formula("or", args=tuple(args))


def Imp(a: Formula, b: Formula) -> Formula:
    return Formula("imp", args=(a, b))


def Quant(kind: str, name: str, body: Formula, bound: Term | None = None) -> Formula:
    if kind not in {"exists", "forall"}:
        raise ValueError("Unknown quantifier")
    V(name)
    if bound is not None and name in term_vars(bound):
        raise ValueError("A quantifier bound cannot contain its own variable")
    return Formula(kind, args=(body,), variable=name, bound=bound)


def Ex(name: str, body: Formula) -> Formula:
    return Quant("exists", name, body)


def All(name: str, body: Formula) -> Formula:
    return Quant("forall", name, body)


def term_vars(t: Term) -> set[str]:
    if t.kind == "var":
        return {str(t.value)}
    return set().union(*(term_vars(a) for a in t.args))


def variables(f: Formula, free_only: bool = False) -> set[str]:
    out = set().union(*(variables(a, free_only) for a in f.args))
    for t in (f.left, f.right, f.bound):
        if t is not None:
            out |= term_vars(t)
    if f.variable is not None:
        if free_only:
            out.discard(f.variable)
        else:
            out.add(f.variable)
    return out


def degree(t: Term) -> int:
    if t.kind == "const":
        return 0
    if t.kind == "var":
        return 1
    d = [degree(a) for a in t.args]
    return max(d) if t.kind == "add" else sum(d)


def evaluate_term(t: Term, assignment: Mapping[str, int]) -> int:
    if t.kind == "const":
        return int(t.value)
    if t.kind == "var":
        return assignment[str(t.value)]
    a, b = (evaluate_term(x, assignment) for x in t.args)
    if t.kind == "add":
        return a + b
    if t.kind == "mul":
        return a * b
    raise ValueError(f"Unknown term kind: {t.kind}")


def evaluate_atom(f: Formula, assignment: Mapping[str, int]) -> bool:
    if f.left is None or f.right is None:
        raise ValueError("Expected an atomic formula")
    a, b = evaluate_term(f.left, assignment), evaluate_term(f.right, assignment)
    if f.kind == "eq":
        return a == b
    if f.kind == "lt":
        return a < b
    if f.kind == "le":
        return a <= b
    raise ValueError("Expected equality or order")


class Compiler:
    """Freshness is global, including variables in unreachable branches."""
    def __init__(self, source: Formula, bound: str = "H") -> None:
        if bound in variables(source):
            raise ValueError("The designated infinite-bound name occurs in the input")
        self.used = variables(source) | {bound}
        self.H = V(bound)
        self.counter = 0

    def fresh(self, prefix: str) -> str:
        while True:
            name = f"{prefix}{self.counter}"
            self.counter += 1
            if name not in self.used:
                self.used.add(name)
                return name

    def standard_guard(self, x: Term) -> Formula:
        y, u, v = (V(self.fresh(p)) for p in ("dy", "od", "co"))
        forbidden = Not(Eq(y, Mul(Add(Mul(C(2), u), C(3)), v)))
        restricted = Imp(And(Le(u, y), Le(v, y)), forbidden)
        ph = And(Lt(C(0), y),
                 Quant("forall", str(u.value),
                       Quant("forall", str(v.value), restricted, self.H), self.H))
        return Or(Eq(x, C(0)),
                  Quant("exists", str(y.value),
                        And(Le(y, x), Lt(x, Mul(C(2), y)), ph), self.H))

    def flatten_atom(self, source: Formula) -> Formula:
        if source.left is None or source.right is None:
            raise ValueError("Expected an atom")
        gates: list[tuple[str, Formula]] = []

        def visit(t: Term) -> Term:
            if t.kind in {"const", "var"}:
                return t
            a, b = (visit(x) for x in t.args)
            z = self.fresh("gate")
            rhs = Add(a, b) if t.kind == "add" else Mul(a, b)
            gates.append((z, Eq(V(z), rhs)))
            return V(z)

        a, b = visit(source.left), visit(source.right)
        out = And(*(equation for _, equation in gates), Atom(source.kind, a, b))
        for name, _ in reversed(gates):
            out = Quant("exists", name, out, self.H)
        return out

    def translate(self, f: Formula) -> Formula:
        if f.kind in {"eq", "lt", "le"}:
            return self.flatten_atom(f)
        if f.kind in {"exists", "forall"}:
            if f.bound is not None:
                raise ValueError("Input quantifiers must be unbounded; expand bounded abbreviations first")
            assert f.variable is not None
            guard = self.standard_guard(V(f.variable))
            body = self.translate(f.args[0])
            guarded = And(guard, body) if f.kind == "exists" else Imp(guard, body)
            return Quant(f.kind, f.variable, guarded, self.H)
        if f.kind in {"and", "or", "not", "imp"}:
            return Formula(f.kind, args=tuple(self.translate(a) for a in f.args))
        raise ValueError(f"Unknown formula kind: {f.kind}")


def audit(f: Formula, bound_name: str = "H") -> dict:
    counts = {"formula_nodes": 0, "quantifiers": 0, "atomic_relations": 0,
              "max_atomic_degree": 0, "quantifier_depth": 0}

    def visit(g: Formula, depth: int) -> None:
        counts["formula_nodes"] += 1
        if g.kind in {"exists", "forall"}:
            assert g.bound == V(bound_name), "Not all bounds are the designated H"
            counts["quantifiers"] += 1
            depth += 1
            counts["quantifier_depth"] = max(counts["quantifier_depth"], depth)
        if g.kind in {"eq", "lt", "le"}:
            assert g.left is not None and g.right is not None
            d = max(degree(g.left), degree(g.right))
            counts["max_atomic_degree"] = max(counts["max_atomic_degree"], d)
            counts["atomic_relations"] += 1
            assert d <= 2, "An atom is not quadratic"
        for child in g.args:
            visit(child, depth)

    visit(f, 0)
    free = variables(f, free_only=True)
    assert free <= {bound_name}, f"Unexpected free variables: {free}"
    counts["free_variables"] = sorted(free)
    counts["all_quantifiers_bounded_by_H"] = True
    return counts


def show_term(t: Term) -> str:
    if t.kind in {"var", "const"}:
        return str(t.value)
    symbol = "+" if t.kind == "add" else "*"
    return f"({show_term(t.args[0])} {symbol} {show_term(t.args[1])})"


def show(f: Formula) -> str:
    if f.kind in {"eq", "lt", "le"}:
        assert f.left is not None and f.right is not None
        symbol = {"eq": "=", "lt": "<", "le": "<="}[f.kind]
        return f"({show_term(f.left)} {symbol} {show_term(f.right)})"
    if f.kind in {"exists", "forall"}:
        b = "" if f.bound is None else " <= " + show_term(f.bound)
        return f"({f.kind} {f.variable}{b}: {show(f.args[0])})"
    if f.kind == "not":
        return f"(not {show(f.args[0])})"
    symbol = {"and": " and ", "or": " or ", "imp": " implies "}[f.kind]
    return "(" + symbol.join(show(a) for a in f.args) + ")"


def local_gate_checks() -> int:
    """Check deterministic local gate traces, not quantifier search."""
    x, y = V("x"), V("y")
    atoms = [Eq(Add(Mul(x, x), Mul(y, y)), Mul(Add(x, y), Add(x, y))),
             Lt(Mul(Mul(x, x), x), Add(Mul(y, y), C(17))),
             Le(Add(x, Mul(x, Add(y, C(1)))), Mul(Add(x, C(2)), y))]
    count = 0
    for source in atoms:
        c = Compiler(source)
        target = c.flatten_atom(source)
        g = target
        while g.kind == "exists":
            assert g.bound == V("H")
            g = g.args[0]
        assert g.kind == "and"
        equations, final = g.args[:-1], g.args[-1]
        for a in range(16):
            for b in range(16):
                env = {"x": a, "y": b, "H": 10**6}
                for equation in equations:
                    assert equation.left is not None and equation.right is not None
                    z = str(equation.left.value)
                    value = evaluate_term(equation.right, env)
                    assert 0 <= value <= env["H"]
                    env[z] = value
                    assert evaluate_atom(equation, env)
                assert evaluate_atom(final, env) == evaluate_atom(source, env)
                count += 1
    return count


def examples() -> list[tuple[str, Formula]]:
    x, y, z = V("x"), V("y"), V("z")
    cube = lambda a: Mul(Mul(a, a), a)
    return [
        ("successor", All("x", Ex("y", Eq(y, Add(x, C(1)))))),
        ("no_square_root_two", Not(Ex("x", Eq(Mul(x, x), C(2))))),
        ("cubic_equation", Ex("x", Ex("y", Ex("z", And(
            Lt(C(0), x), Lt(C(0), y), Lt(C(0), z),
            Eq(Add(cube(x), cube(y)), cube(z))))))),
        ("distributivity", All("x", All("y", All("z", Eq(
            Mul(x, Add(y, z)), Add(Mul(x, y), Mul(x, z))))))),
        ("shadowing_and_freshness", All("gate0", And(
            Eq(V("gate0"), V("gate0")),
            Ex("gate0", Eq(V("gate0"), C(0))))))]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("compiler_report.json"))
    args = parser.parse_args()
    outputs = []
    for name, source in examples():
        assert not variables(source, free_only=True), "Example is not a sentence"
        target = Compiler(source).translate(source)
        outputs.append({"name": name, "audit": audit(target),
                        "input": show(source), "output": show(target)})
    report = {"status": "PASS", "scope": "Syntactic invariants and finite local gate checks; not infinite-bound evaluation.",
              "compiled_sentence_examples": len(outputs),
              "local_gate_checks": local_gate_checks(), "examples": outputs}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in report.items() if k != "examples"}, indent=2))
    for ex in outputs:
        print(ex["name"], json.dumps(ex["audit"]))


if __name__ == "__main__":
    main()
