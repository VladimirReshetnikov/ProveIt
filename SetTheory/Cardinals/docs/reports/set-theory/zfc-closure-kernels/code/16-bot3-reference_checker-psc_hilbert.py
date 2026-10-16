#!/usr/bin/env python3
"""Constructive certificate checker for equality-free classical PSC.

Fresh implementation for the 2026-10-16 research report.  Python 3.10+,
standard library only.  See README.md for the exact calculus and theorem.

Formulae are FLAT prefix token tuples, not recursively nested Python trees:
    B                 falsity
    R x y             membership of variables x,y
    I F G             implication
    A x F             universal quantification
This avoids a fixed Python recursion-depth bound on well-formed formulae.
"""

from __future__ import annotations

import argparse
import itertools
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Iterator, Mapping


class CertificateError(ValueError):
    """An invalid formula, certificate, schema, or inference."""


_NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9]*\Z", re.ASCII)


def _name(value: object) -> str:
    if type(value) is not str or _NAME.fullmatch(value) is None:
        raise CertificateError("variable names must be ASCII identifiers")
    return value


@dataclass(frozen=True, slots=True)
class Var:
    name: str

    def __post_init__(self) -> None:
        _name(self.name)


@dataclass(frozen=True, slots=True)
class _Node:
    tag: str
    start: int
    head_end: int
    end: int
    children: tuple[int, ...]


def _parse(tokens: tuple[str, ...]) -> tuple[dict[int, _Node], tuple[int, ...]]:
    """Validate a flat formula and compute subtree intervals iteratively."""
    if type(tokens) is not tuple or any(type(t) is not str for t in tokens):
        raise CertificateError("formula tokens must be a tuple of strings")
    headers: list[tuple[int, str, int]] = []
    pending, position = 1, 0
    while pending:
        if position >= len(tokens):
            raise CertificateError("truncated formula")
        start, tag = position, tokens[position]
        position += 1
        pending -= 1
        if tag == "R":
            if position + 2 > len(tokens):
                raise CertificateError("membership needs two variable names")
            _name(tokens[position])
            _name(tokens[position + 1])
            position += 2
        elif tag == "I":
            pending += 2
        elif tag == "A":
            if position >= len(tokens):
                raise CertificateError("universal quantifier needs a variable")
            _name(tokens[position])
            position += 1
            pending += 1
        elif tag != "B":
            raise CertificateError(f"unknown formula token {tag!r}")
        headers.append((start, tag, position))
    if position != len(tokens):
        raise CertificateError("trailing tokens after formula")

    nodes: dict[int, _Node] = {}
    roots: list[int] = []
    for start, tag, head_end in reversed(headers):
        if tag == "A":
            child = roots.pop()
            children, end = (child,), nodes[child].end
        elif tag == "I":
            left, right = roots.pop(), roots.pop()
            children, end = (left, right), nodes[right].end
        else:
            children, end = (), head_end
        nodes[start] = _Node(tag, start, head_end, end, children)
        roots.append(start)
    if roots != [0]:
        raise CertificateError("malformed formula tree")
    return nodes, tuple(start for start, _, _ in headers)


@dataclass(frozen=True, slots=True)
class Formula:
    tokens: tuple[str, ...]

    def __post_init__(self) -> None:
        _parse(self.tokens)


BOTTOM = Formula(("B",))


def _formula(value: object) -> Formula:
    if type(value) is not Formula:
        raise CertificateError("expected a Formula")
    return value


def Rel(left: Var, right: Var) -> Formula:
    if type(left) is not Var or type(right) is not Var:
        raise CertificateError("membership arguments must be variables")
    return Formula(("R", left.name, right.name))


def Imp(left: Formula, right: Formula) -> Formula:
    return Formula(("I",) + _formula(left).tokens + _formula(right).tokens)


def All(variable: Var, body: Formula) -> Formula:
    if type(variable) is not Var:
        raise CertificateError("a quantifier must bind a variable")
    return Formula(("A", variable.name) + _formula(body).tokens)


def Not(body: Formula) -> Formula:
    return Imp(body, BOTTOM)


def And(left: Formula, right: Formula) -> Formula:
    return Not(Imp(left, Not(right)))


def Or(left: Formula, right: Formula) -> Formula:
    return Imp(Not(left), right)


def Exists(variable: Var, body: Formula) -> Formula:
    return Not(All(variable, Not(body)))


def _free_sets(formula: Formula, nodes: dict[int, _Node],
               order: tuple[int, ...]) -> dict[int, frozenset[str]]:
    result: dict[int, frozenset[str]] = {}
    for position in reversed(order):
        node = nodes[position]
        if node.tag == "B":
            free = frozenset()
        elif node.tag == "R":
            free = frozenset(formula.tokens[position + 1:position + 3])
        elif node.tag == "I":
            free = result[node.children[0]] | result[node.children[1]]
        else:
            free = result[node.children[0]] - {formula.tokens[position + 1]}
        result[position] = free
    return result


def free_variables(formula: Formula) -> frozenset[str]:
    nodes, order = _parse(_formula(formula).tokens)
    return _free_sets(formula, nodes, order)[0]


def variable_names(formula: Formula) -> frozenset[str]:
    nodes, order = _parse(_formula(formula).tokens)
    names: set[str] = set()
    for position in order:
        node = nodes[position]
        if node.tag == "R":
            names.update(formula.tokens[position + 1:position + 3])
        elif node.tag == "A":
            names.add(formula.tokens[position + 1])
    return frozenset(names)


def _fresh(occupied: set[str]) -> str:
    index = 0
    while f"_v{index}" in occupied:
        index += 1
    result = f"_v{index}"
    occupied.add(result)
    return result


def substitute_many(formula: Formula, replacements: Mapping[str, str]) -> Formula:
    """Simultaneously substitute FREE variables, alpha-renaming on capture.

    Substitution does not substitute again into its replacement variables.
    A stack for each original bound name handles shadowing.  Fresh names
    avoid every free and bound name already present and all replacements.
    """
    _formula(formula)
    if not isinstance(replacements, Mapping):
        raise CertificateError("substitutions must be a mapping")
    validated = {_name(k): _name(v) for k, v in replacements.items()}
    mapping = {k: v for k, v in validated.items() if k != v}
    nodes, order = _parse(formula.tokens)
    free = _free_sets(formula, nodes, order)
    mapping = {k: v for k, v in mapping.items() if k in free[0]}
    if not mapping:
        return formula
    occupied = set(variable_names(formula)) | set(mapping) | set(mapping.values())
    scopes: dict[str, list[str]] = {}
    events: list[tuple[str, int | str]] = [("visit", 0)]
    output: list[str] = []

    def variable(original: str) -> str:
        bound = scopes.get(original)
        return bound[-1] if bound else mapping.get(original, original)

    while events:
        event, value = events.pop()
        if event == "exit":
            scopes[value].pop()  # type: ignore[index]
            continue
        position = value
        node = nodes[position]  # type: ignore[index]
        if node.tag == "B":
            output.append("B")
        elif node.tag == "R":
            output.extend(("R", variable(formula.tokens[node.start + 1]),
                           variable(formula.tokens[node.start + 2])))
        elif node.tag == "I":
            output.append("I")
            events.extend((('visit', node.children[1]), ('visit', node.children[0])))
        else:
            original = formula.tokens[node.start + 1]
            child = node.children[0]
            capture = any(
                source != original and target == original
                and source in free[child] and not scopes.get(source)
                for source, target in mapping.items()
            )
            chosen = _fresh(occupied) if capture else original
            output.extend(("A", chosen))
            scopes.setdefault(original, []).append(chosen)
            events.extend((("exit", original), ("visit", child)))
    return Formula(tuple(output))


def substitute(formula: Formula, source: Var, target: Var) -> Formula:
    if type(source) is not Var or type(target) is not Var:
        raise CertificateError("substitution arguments must be variables")
    return substitute_many(formula, {source.name: target.name})


def Subset(left: Var, right: Var, witness: Var) -> Formula:
    if any(type(value) is not Var for value in (left, right, witness)):
        raise CertificateError("subset arguments must be variables")
    if witness.name in (left.name, right.name):
        raise CertificateError("subset witness must be fresh for its arguments")
    return All(witness, Imp(Rel(witness, left), Rel(witness, right)))


def psc_instance(matrix: Formula, input_variable: Var,
                 output_variable: Var) -> Formula:
    """Universally closed, equality-free SUBSET-seeded PSC, and nothing else.

    Every wrapper binder has a distinct name absent from ALL matrix names.
    All remaining free matrix names are universally closed in sorted order.
    The support clause has an unrestricted existential input.
    """
    _formula(matrix)
    if type(input_variable) is not Var or type(output_variable) is not Var:
        raise CertificateError("PSC slots must be variables")
    if input_variable == output_variable:
        raise CertificateError("PSC input and output slots must be distinct")
    occupied = set(variable_names(matrix)) | {
        input_variable.name, output_variable.name
    }
    sbx, sbb, sby, sbz, seed, hull, cx, cy, sz, sy, sx = (
        Var(_fresh(occupied)) for _ in range(11)
    )

    def rho(first: Var, second: Var) -> Formula:
        return substitute_many(matrix, {
            input_variable.name: first.name, output_variable.name: second.name
        })

    bound = All(sbx, Exists(sbb, All(sby,
        Imp(rho(sbx, sby), Subset(sby, sbb, sbz)))))
    closure = All(cx, All(cy, Imp(
        And(Or(Subset(cx, seed, sz), Rel(cx, hull)), rho(cx, cy)),
        Rel(cy, hull))))
    support = All(sy, Imp(Rel(sy, hull), Exists(sx, rho(sx, sy))))
    result = Imp(bound, All(seed, Exists(hull, And(closure, support))))
    parameters = sorted(free_variables(matrix) - {
        input_variable.name, output_variable.name
    })
    for parameter in reversed(parameters):
        result = All(Var(parameter), result)
    return result


def _read_formula(value: object) -> Formula:
    if type(value) is not list or any(type(token) is not str for token in value):
        raise CertificateError("a formula must be a flat JSON array of strings")
    return Formula(tuple(value))


def encode_formula(formula: Formula) -> list[str]:
    return list(_formula(formula).tokens)


def _keys(row: dict, required: set[str]) -> None:
    if set(row) != required:
        raise CertificateError(f"expected exactly the keys {sorted(required)!r}")


def _reference(value: object, lines: list[Formula]) -> Formula:
    # Python considers bool an int; certificates explicitly do not.
    if type(value) is not int or not 0 <= value < len(lines):
        raise CertificateError("references must be prior nonnegative integer indices")
    return lines[value]


def _imp_parts(formula: Formula) -> tuple[Formula, Formula]:
    nodes, _ = _parse(formula.tokens)
    root = nodes[0]
    if root.tag != "I":
        raise CertificateError("modus ponens needs an implication")
    left, right = (nodes[index] for index in root.children)
    return (Formula(formula.tokens[left.start:left.end]),
            Formula(formula.tokens[right.start:right.end]))


@dataclass(frozen=True, slots=True)
class CheckedProof:
    lines: tuple[Formula, ...]

    @property
    def conclusion(self) -> Formula | None:
        return self.lines[-1] if self.lines else None

    @property
    def is_refutation(self) -> bool:
        return self.conclusion == BOTTOM


def check_certificate(certificate: object) -> CheckedProof:
    """Check instructions and CONSTRUCT conclusions; no asserted lines exist."""
    if type(certificate) is not list:
        raise CertificateError("a certificate must be a JSON array")
    lines: list[Formula] = []
    for index, row in enumerate(certificate):
        try:
            if type(row) is not dict or type(row.get("op")) is not str:
                raise CertificateError("each line needs an operation object")
            op = row["op"]
            if op in {"K", "C"}:
                _keys(row, {"op", "A", "B"})
                a, b = _read_formula(row["A"]), _read_formula(row["B"])
                result = (Imp(a, Imp(b, a)) if op == "K" else
                          Imp(Imp(Not(a), Not(b)), Imp(b, a)))
            elif op == "S":
                _keys(row, {"op", "A", "B", "C"})
                a, b, c = (_read_formula(row[name]) for name in ("A", "B", "C"))
                result = Imp(Imp(a, Imp(b, c)), Imp(Imp(a, b), Imp(a, c)))
            elif op == "UI":
                _keys(row, {"op", "x", "A", "y"})
                x, y = Var(row["x"]), Var(row["y"])
                a = _read_formula(row["A"])
                result = Imp(All(x, a), substitute(a, x, y))
            elif op == "QD":
                _keys(row, {"op", "x", "A", "B"})
                x = Var(row["x"])
                a, b = _read_formula(row["A"]), _read_formula(row["B"])
                if x.name in free_variables(a):
                    raise CertificateError("QD requires x not free in A")
                result = Imp(All(x, Imp(a, b)), Imp(a, All(x, b)))
            elif op == "PSC":
                _keys(row, {"op", "rho", "x", "y"})
                result = psc_instance(_read_formula(row["rho"]),
                                      Var(row["x"]), Var(row["y"]))
            elif op == "MP":
                _keys(row, {"op", "premise", "implication"})
                premise = _reference(row["premise"], lines)
                implication = _reference(row["implication"], lines)
                antecedent, result = _imp_parts(implication)
                if premise != antecedent:
                    raise CertificateError("modus ponens antecedent does not match")
            elif op == "GEN":
                _keys(row, {"op", "line", "x"})
                result = All(Var(row["x"]), _reference(row["line"], lines))
            else:
                raise CertificateError(f"unknown operation {op!r}")
            lines.append(result)
        except CertificateError as error:
            raise CertificateError(f"line {index}: {error}") from error
    return CheckedProof(tuple(lines))


def _unique_object(pairs: list[tuple[str, object]]) -> dict:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise CertificateError(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def _decimal_integer(text: str) -> int:
    # Avoid a fixed decimal-digit bound: valid indices have arbitrary size.
    negative = text.startswith("-")
    value = 0
    for digit in text[1:] if negative else text:
        value = 10 * value + (ord(digit) - ord("0"))
    return -value if negative else value


def _reject_number(text: str) -> None:
    raise CertificateError(f"noninteger JSON number {text!r} is not allowed")


def decode_certificate(data: bytes) -> object:
    if type(data) is not bytes:
        raise CertificateError("serialized certificates must be bytes")
    try:
        return json.loads(data.decode("utf-8"), object_pairs_hook=_unique_object,
                          parse_int=_decimal_integer, parse_float=_reject_number,
                          parse_constant=_reject_number)
    except (UnicodeError, json.JSONDecodeError, RecursionError) as error:
        raise CertificateError("invalid JSON certificate") from error


def check_bytes(data: bytes) -> CheckedProof:
    return check_certificate(decode_certificate(data))


def refutes_bytes(data: bytes) -> bool:
    """Total rejection of syntactically invalid byte strings (finite resources aside)."""
    try:
        return check_bytes(data).is_refutation
    except CertificateError:
        return False


def length_lex_bytes() -> Iterator[bytes]:
    """Every finite byte string, once, by length then lexicographic order."""
    length = 0
    while True:
        for digits in itertools.product(range(256), repeat=length):
            yield bytes(digits)
        length += 1


def search_refutation() -> bytes:
    """Deliberately impractical fair semidecision procedure; never used by tests."""
    for candidate in length_lex_bytes():
        if refutes_bytes(candidate):
            return candidate
    raise AssertionError("the byte-string enumeration is infinite")


def render(formula: Formula) -> str:
    """Readable parenthesized ASCII, using no recursive calls."""
    nodes, _ = _parse(_formula(formula).tokens)
    events: list[tuple[str, int | str]] = [("visit", 0)]
    output: list[str] = []
    while events:
        event, value = events.pop()
        if event == "text":
            output.append(value)  # type: ignore[arg-type]
            continue
        node = nodes[value]  # type: ignore[index]
        if node.tag == "B":
            output.append("BOTTOM")
        elif node.tag == "R":
            output.append(f"{formula.tokens[node.start + 1]} in "
                          f"{formula.tokens[node.start + 2]}")
        elif node.tag == "I":
            output.append("(")
            events.extend((("text", ")"), ("visit", node.children[1]),
                           ("text", " -> "), ("visit", node.children[0])))
        else:
            output.append(f"(forall {formula.tokens[node.start + 1]}. ")
            events.extend((("text", ")"), ("visit", node.children[0])))
    return "".join(output)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", nargs="?", type=Path)
    parser.add_argument("--search", action="store_true",
                        help="run the unbounded, impractical refutation search")
    args = parser.parse_args()
    if args.search:
        print(search_refutation().decode("utf-8"))
        return 0
    if args.certificate is None:
        parser.error("give a JSON certificate path, or explicitly request --search")
    try:
        proof = check_bytes(args.certificate.read_bytes())
    except (OSError, CertificateError) as error:
        print(f"REJECTED: {error}")
        return 1
    print(f"ACCEPTED: {len(proof.lines)} theorem lines")
    print(f"Final line is primitive Bottom: {proof.is_refutation}")
    if proof.conclusion is not None:
        print(render(proof.conclusion))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
