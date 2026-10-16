#!/usr/bin/env python3
"""Reference binary derivation checker for equality-free subset PSC.

This is a transparent executable specification, not a verified compiler or a
Turing-machine state claim.  Bottom is a genuine primitive with false semantics.
The AST and syntax traversals are iterative, with no imposed depth/length cap.
Python/OS resource failures propagate: they are never classified as rejection.
See README.md for the complete grammar, theory, and trust boundary.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
from pathlib import Path
from typing import Mapping, Sequence


BOT, MEM, IMP, ALL = range(4)
K, S, C, UI, UD, PSC, MP, GEN = range(8)
OP_NAMES = ("K", "S", "C", "UI", "UD", "PSC", "MP", "GEN")


class CertificateError(ValueError):
    """A finite certificate violates its syntax or an inference side condition."""


def natural(n: object) -> int:
    if type(n) is not int or n < 0:
        raise CertificateError("a natural must be a nonnegative integer, not bool")
    return n


def unary(n: int) -> str:
    return "0" * natural(n) + "1"


class Arena:
    """Interned formula DAG; child references are integer IDs, never recursion.

    ID equality is exact named-variable syntax, not alpha-equivalence.
    Keeping free/all-variable sets is an implementation convenience, not a
    proposed minimal-machine representation.
    """

    def __init__(self) -> None:
        self.nodes: list[tuple[int, ...]] = []
        self._intern: dict[tuple[int, ...], int] = {}
        self.free: list[frozenset[int]] = []
        self.variables: list[frozenset[int]] = []
        self.bottom = self._add((BOT,), frozenset(), frozenset())

    def node_id(self, p: object) -> int:
        p = natural(p)
        if p >= len(self.nodes):
            raise CertificateError("formula node ID does not belong to this arena")
        return p

    def _add(self, node: tuple[int, ...], free: frozenset[int],
             variables: frozenset[int]) -> int:
        old = self._intern.get(node)
        if old is not None:
            return old
        out = len(self.nodes)
        self.nodes.append(node)
        self._intern[node] = out
        self.free.append(free)
        self.variables.append(variables)
        return out

    def mem(self, x: int, y: int) -> int:
        x, y = natural(x), natural(y)
        vs = frozenset((x, y))
        return self._add((MEM, x, y), vs, vs)

    def imp(self, a: int, b: int) -> int:
        a, b = self.node_id(a), self.node_id(b)
        return self._add((IMP, a, b), self.free[a] | self.free[b],
                         self.variables[a] | self.variables[b])

    def all(self, x: int, a: int) -> int:
        x, a = natural(x), self.node_id(a)
        return self._add((ALL, x, a), self.free[a] - {x},
                         self.variables[a] | {x})

    def neg(self, a: int) -> int:
        return self.imp(a, self.bottom)

    def exists(self, x: int, a: int) -> int:
        return self.neg(self.all(x, self.neg(a)))

    def conjunction(self, a: int, b: int) -> int:
        return self.neg(self.imp(a, self.neg(b)))

    def disjunction(self, a: int, b: int) -> int:
        return self.imp(self.neg(a), b)

    def alls(self, xs: Sequence[int], a: int) -> int:
        for x in reversed(xs):
            a = self.all(x, a)
        return a

    def subset(self, x: int, y: int, z: int) -> int:
        if z in (x, y):
            raise CertificateError("subset witness must be fresh")
        return self.all(z, self.imp(self.mem(z, x), self.mem(z, y)))

    def substitute(self, p: int, replacements: Mapping[int, int]) -> int:
        """Simultaneous capture-avoiding substitution of free variable names.

        An explicit stack simulates descent. At a binder, remove the shadowed
        substitution. If a still-active replacement would be captured, rename
        that binder and carry the renaming in the child environment. Fresh
        labels increase from above all names in the input and substitution.
        """
        p = self.node_id(p)
        validated = {natural(k): natural(v) for k, v in replacements.items()}
        replacements = {k: v for k, v in validated.items() if k != v}
        fresh = max(self.variables[p] | set(replacements) |
                    set(replacements.values()), default=-1) + 1
        tasks: list[tuple] = [("visit", p, replacements)]
        values: list[int] = []
        while tasks:
            task = tasks.pop()
            if task[0] == "imp":
                right = values.pop()
                left = values.pop()
                values.append(self.imp(left, right))
                continue
            if task[0] == "all":
                values.append(self.all(task[1], values.pop()))
                continue
            _, q, env = task
            if not self.free[q].intersection(env):
                values.append(q)
                continue
            node = self.nodes[q]
            if node[0] == BOT:
                values.append(q)
            elif node[0] == MEM:
                values.append(self.mem(env.get(node[1], node[1]),
                                       env.get(node[2], node[2])))
            elif node[0] == IMP:
                tasks.append(("imp",))
                tasks.append(("visit", node[2], env))
                tasks.append(("visit", node[1], env))
            elif node[0] == ALL:
                binder, body = node[1:]
                active = {k: v for k, v in env.items()
                          if k != binder and k in self.free[body]}
                target_binder = binder
                if binder in active.values():
                    target_binder = fresh
                    fresh += 1
                    active[binder] = target_binder
                tasks.append(("all", target_binder))
                tasks.append(("visit", body, active))
            else:
                raise AssertionError("internal arena invariant")
        if len(values) != 1:
            raise AssertionError("internal substitution stack invariant")
        return values[0]

    def psc(self, matrix: int) -> int:
        """Closed pure subset-seeded/subset-bounded PSC schema instance.

        Free names 0 and 1 designate input/output. Any other free names are
        parameters. Matrices are unrestricted equality-free formulas, including
        negative formulas; neither distinguished name need actually occur.
        """
        matrix = self.node_id(matrix)
        first = max(self.variables[matrix] | {0, 1}) + 1
        x, y, b, a, hull, z = range(first, first + 6)
        rho = self.substitute(matrix, {0: x, 1: y})
        local = self.all(x, self.exists(b, self.all(y, self.imp(
            rho, self.subset(y, b, z)))))
        start_or_member = self.disjunction(self.subset(x, a, z),
                                           self.mem(x, hull))
        closed = self.alls((x, y), self.imp(
            self.conjunction(start_or_member, rho), self.mem(y, hull)))
        support = self.all(y, self.imp(self.mem(y, hull),
                                      self.exists(x, rho)))
        schema = self.imp(local, self.all(a, self.exists(
            hull, self.conjunction(closed, support))))
        return self.alls(sorted(self.free[schema]), schema)


class Reader:
    def __init__(self, bits: str) -> None:
        if not isinstance(bits, str) or any(c not in "01" for c in bits):
            raise CertificateError("certificate must contain only ASCII 0 and 1")
        self.bits = bits
        self.pos = 0

    def tag(self, width: int) -> int:
        end = self.pos + width
        if end > len(self.bits):
            raise CertificateError("truncated tag")
        out = int(self.bits[self.pos:end], 2)
        self.pos = end
        return out

    def nat(self) -> int:
        end = self.bits.find("1", self.pos)
        if end < 0:
            raise CertificateError("unterminated unary natural")
        out = end - self.pos
        self.pos = end + 1
        return out

    def formula(self, arena: Arena) -> int:
        frames: list[tuple[int, int | None]] = []
        while True:
            tag = self.tag(2)
            if tag == BOT:
                value = arena.bottom
            elif tag == MEM:
                value = arena.mem(self.nat(), self.nat())
            elif tag == IMP:
                frames.append((IMP, None))
                continue
            else:
                frames.append((ALL, self.nat()))
                continue
            while frames:
                kind, saved = frames.pop()
                if kind == ALL:
                    value = arena.all(saved, value)
                elif saved is None:
                    frames.append((IMP, value))
                    break
                else:
                    value = arena.imp(saved, value)
            else:
                return value

    def finish(self) -> None:
        if self.pos != len(self.bits):
            raise CertificateError("trailing bits are not permitted")


def encode_formula(arena: Arena, p: int) -> str:
    pending = [arena.node_id(p)]
    out: list[str] = []
    while pending:
        node = arena.nodes[pending.pop()]
        tag = node[0]
        out.append(f"{tag:02b}")
        if tag == MEM:
            out.extend((unary(node[1]), unary(node[2])))
        elif tag == IMP:
            pending.extend((node[2], node[1]))
        elif tag == ALL:
            out.append(unary(node[1]))
            pending.append(node[2])
    return "".join(out)


def decode_formula(arena: Arena, bits: str) -> int:
    reader = Reader(bits)
    formula = reader.formula(arena)
    reader.finish()
    return formula


# f = formula; n = unary natural. A field's kind is determined by the opcode.
FIELDS = ("ff", "fff", "ff", "nnf", "nff", "f", "nn", "nn")


@dataclass(frozen=True)
class Line:
    opcode: int
    fields: tuple[int, ...]


def encode_certificate(arena: Arena, lines: Sequence[Line]) -> str:
    out = [unary(len(lines))]
    for line in lines:
        opcode = natural(line.opcode)
        if opcode >= 8 or len(line.fields) != len(FIELDS[opcode]):
            raise CertificateError("invalid opcode or number of fields")
        out.append(f"{opcode:03b}")
        for kind, value in zip(FIELDS[opcode], line.fields):
            out.append(encode_formula(arena, value) if kind == "f" else unary(value))
    return "".join(out)


@dataclass(frozen=True)
class CheckedDerivation:
    arena: Arena
    lines: tuple[int, ...]

    @property
    def conclusion(self) -> int | None:
        return self.lines[-1] if self.lines else None

    @property
    def is_refutation(self) -> bool:
        return self.conclusion == self.arena.bottom


def check_derivation(bits: str) -> CheckedDerivation:
    """Reconstruct every line; reject any parse/rule error and any suffix.

    There are no assumptions, equality axioms, external oracles, or supplied
    truth claims. A returned derivation may prove a harmless tautology. Only a
    returned derivation ending in the literal primitive Bottom is a refutation.
    """
    reader = Reader(bits)
    arena = Arena()
    lines: list[int] = []
    line_count = reader.nat()
    for index in range(line_count):
        opcode = reader.tag(3)
        fields = tuple(reader.formula(arena) if k == "f" else reader.nat()
                       for k in FIELDS[opcode])
        if opcode == K:
            a, b = fields
            formula = arena.imp(a, arena.imp(b, a))
        elif opcode == S:
            a, b, c = fields
            formula = arena.imp(arena.imp(a, arena.imp(b, c)),
                                arena.imp(arena.imp(a, b), arena.imp(a, c)))
        elif opcode == C:
            a, b = fields
            formula = arena.imp(arena.imp(arena.neg(a), arena.neg(b)),
                                arena.imp(b, a))
        elif opcode == UI:
            x, y, a = fields
            formula = arena.imp(arena.all(x, a), arena.substitute(a, {x: y}))
        elif opcode == UD:
            x, a, b = fields
            if x in arena.free[a]:
                raise CertificateError(f"line {index}: UD variable free in antecedent")
            formula = arena.imp(arena.all(x, arena.imp(a, b)),
                                arena.imp(a, arena.all(x, b)))
        elif opcode == PSC:
            formula = arena.psc(fields[0])
        elif opcode == MP:
            antecedent, implication = fields
            if antecedent >= index or implication >= index:
                raise CertificateError(f"line {index}: MP reference is not earlier")
            node = arena.nodes[lines[implication]]
            if node[0] != IMP or node[1] != lines[antecedent]:
                raise CertificateError(f"line {index}: MP antecedent mismatch")
            formula = node[2]
        else:
            previous, x = fields
            if previous >= index:
                raise CertificateError(f"line {index}: GEN reference is not earlier")
            formula = arena.all(x, lines[previous])
        lines.append(formula)
    reader.finish()
    return CheckedDerivation(arena, tuple(lines))


def accepts_refutation(bits: str) -> bool:
    """Total in the unbounded-resource mathematical algorithm.

    Only certificate errors become False. MemoryError, OS interruption, and
    other execution failures are deliberately not caught or treated as evidence.
    """
    try:
        return check_derivation(bits).is_refutation
    except CertificateError:
        return False


def identity_certificate() -> tuple[str, Arena, int]:
    """A real five-line proof of A -> A, A = Mem(0,1), never of Bottom."""
    arena = Arena()
    a = arena.mem(0, 1)
    aa = arena.imp(a, a)
    lines = (
        Line(K, (a, aa)),
        Line(K, (a, a)),
        Line(S, (a, aa, a)),
        Line(MP, (0, 2)),
        Line(MP, (1, 3)),
    )
    return encode_certificate(arena, lines), arena, aa


def enumerate_certificates(max_bits: int) -> dict[str, int]:
    """Finite regression census, not evidence of theory consistency."""
    max_bits = natural(max_bits)
    tested = valid = refutations = 0
    for size in range(max_bits + 1):
        for value in range(1 << size):
            bits = f"{value:0{size}b}" if size else ""
            tested += 1
            try:
                result = check_derivation(bits)
            except CertificateError:
                continue
            valid += 1
            refutations += result.is_refutation
    return {"max_bits": max_bits, "tested": tested,
            "valid_derivations": valid, "accepted_refutations": refutations}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    check = commands.add_parser("check", help="check exact ASCII-bit certificate")
    check.add_argument("path", type=Path)
    identity = commands.add_parser("identity", help="write valid non-refutation")
    identity.add_argument("path", type=Path)
    census = commands.add_parser("enumerate", help="bounded regression only")
    census.add_argument("max_bits", type=int)
    args = parser.parse_args()
    if args.command == "identity":
        bits, _, _ = identity_certificate()
        args.path.write_bytes(bits.encode("ascii"))
        print(json.dumps({"path": str(args.path), "bits": len(bits),
                          "conclusion": "Mem(0,1) -> Mem(0,1)",
                          "accepted_refutation": False}, indent=2))
    elif args.command == "enumerate":
        print(json.dumps(enumerate_certificates(args.max_bits), indent=2))
    else:
        try:
            bits = args.path.read_bytes().decode("ascii")
            result = check_derivation(bits)
        except (CertificateError, UnicodeDecodeError) as exc:
            print(json.dumps({"valid_derivation": False,
                              "accepted_refutation": False, "error": str(exc)},
                             indent=2))
            return 1
        print(json.dumps({"bits": len(bits), "lines": len(result.lines),
                          "valid_derivation": True,
                          "accepted_refutation": result.is_refutation,
                          "conclusion_bits": (encode_formula(result.arena,
                              result.conclusion) if result.conclusion is not None
                              else None)}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
