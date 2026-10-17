#!/usr/bin/env python3
"""EPSC2 reference with total matrix-variable lookup.

Adapted from the attributed incoming EPSC2 reference, retained byte for byte in
epsc2_original.py. An out-of-range matrix-variable index selects the last
environment value. The public boundary still constructs every axiom itself.
This interprets every raw matrix as a well-scoped EPSC2 matrix; it is not a
restriction of quantifiers or of variable values. No compiled-state saving or
formal proof-assistant verification is claimed.

The public check_refutation interface accepts only matrices and a finite tree;
it supplies all axioms itself. A Python resource failure is never acceptance.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
from pathlib import Path
from typing import Any

BOT = ('bot',)
Rel = lambda i, j: ('rel', i, j)
Imp = lambda a, b: ('imp', a, b)
All = lambda a: ('all', a)
Not = lambda a: Imp(a, BOT)
Ex = lambda a: Not(All(Not(a)))
And = lambda a, b: Not(Imp(a, Not(b)))
Or = lambda a, b: Imp(Not(a), b)
Hole = lambda *projection: ('hole',) + projection

# Matrix slots are [x, y, p, q]. Every displayed index is de Bruijn.
# Outer binders are forall p, forall q. Each matrix occurrence is at depth 5.
SB = All(Ex(All(Imp(Hole(2, 0, 4, 3),
                       All(Imp(Rel(0, 1), Rel(0, 2)))))))
EMPTY = All(Not(Rel(0, 1)))                 # inside the closure's forall x
GUARD = Or(EMPTY, Rel(0, 1))                # epsilon(x) or x in C
CLOSED = All(Imp(GUARD, All(Imp(Hole(1, 0, 4, 3), Rel(0, 2)))))
SUPPORT = All(Imp(Rel(0, 1), Ex(Hole(0, 1, 4, 3))))
TEMPLATE = All(All(Imp(SB, Ex(And(CLOSED, SUPPORT)))))


def nat(value: Any) -> int:
    if type(value) is not int or value < 0:
        raise ValueError('A nonnegative integer is required; Boolean is not a label')
    return value


def parse(raw: Any) -> tuple:
    if not isinstance(raw, (list, tuple)) or not raw:
        raise ValueError('A formula must be a nonempty array')
    tag = raw[0]
    if tag == 'bot' and len(raw) == 1:
        return BOT
    if tag == 'rel' and len(raw) == 3:
        return Rel(nat(raw[1]), nat(raw[2]))
    if tag == 'imp' and len(raw) == 3:
        return Imp(parse(raw[1]), parse(raw[2]))
    if tag == 'all' and len(raw) == 2:
        return All(parse(raw[1]))
    raise ValueError('Unknown formula constructor or incorrect arity')


def scoped(formula: tuple, depth: int) -> bool:
    tag = formula[0]
    if tag == 'bot':
        return True
    if tag == 'rel':
        return formula[1] < depth and formula[2] < depth
    if tag == 'imp':
        return scoped(formula[1], depth) and scoped(formula[2], depth)
    if tag == 'all':
        return scoped(formula[1], depth + 1)
    if tag == 'hole':
        return len(formula) == 5 and all(0 <= i < depth for i in formula[1:])
    return False


def normalize(formula: tuple, depth: int) -> tuple:
    """Mathematical reference normalizer; the running checker does not call it.

    EPSC2 matrices start at depth four. Quantifiers increase depth. Every
    finite input is mapped to legal scoped syntax, and legal syntax is fixed.
    """
    if type(depth) is not int or depth <= 0:
        raise ValueError('Normalization requires positive scope')
    tag = formula[0]
    if tag == 'bot':
        return BOT
    if tag == 'rel':
        return Rel(min(formula[1], depth - 1), min(formula[2], depth - 1))
    if tag == 'imp':
        return Imp(normalize(formula[1], depth), normalize(formula[2], depth))
    if tag == 'all':
        return All(normalize(formula[1], depth + 1))
    raise ValueError('Only ordinary matrix syntax is normalizable')


def select_last(environment: tuple[int, ...], index: int) -> int:
    """Total lookup on nonempty environments, with the last entry as default.

    This loop deliberately uses neither variable division nor an explicit
    length comparison. A linked-list implementation can stop at the final cell.
    It is not a binary TM implementation or a claim about its cost.
    """
    if not environment:
        raise ValueError('An atomic matrix environment must be nonempty')
    cursor = iter(environment)
    value = next(cursor)
    while index:
        try:
            value = next(cursor)
        except StopIteration:
            return value
        index -= 1
    return value


@dataclass(frozen=True)
class Entry:
    positive: bool
    formula: tuple
    environment: tuple[int, ...] = ()
    matrix: tuple | None = None

    def exposed(self) -> Entry:
        """The only template/matrix boundary: a fixed four-slot projection."""
        if self.formula[0] != 'hole':
            return self
        if self.matrix is None:
            raise ValueError('A template hole has no matrix')
        return Entry(self.positive, self.matrix,
                     tuple(self.environment[i] for i in self.formula[1:]))

    def child(self, formula: tuple, positive: bool | None = None,
              environment: tuple[int, ...] | None = None) -> Entry:
        return Entry(self.positive if positive is None else positive, formula,
                     self.environment if environment is None else environment,
                     self.matrix)

    def atom(self) -> tuple[int, int] | None:
        e = self.exposed()
        if e.formula[0] != 'rel':
            return None
        return tuple(select_last(e.environment, i) for i in e.formula[1:])


def axiom(matrix: Any) -> Entry:
    phi = parse(matrix)
    return Entry(True, TEMPLATE, (), phi)


def check_tree(roots: list[Entry], proof: Any) -> dict[str, int | bool]:
    """Generic test interface, not the public theory-refutation boundary."""
    highest = 0
    for root in roots:
        if type(root.positive) is not bool:
            raise ValueError('A sign must be Boolean')
        # Public roots are copies of the fixed, closed TEMPLATE. Generic
        # demonstration roots with nonempty environments use the same total
        # variable interpretation. A zero-environment root must remain closed.
        if not root.environment and not scoped(root.formula, 0):
            raise ValueError('An initial closure is not scoped')
        for name in root.environment:
            highest = max(highest, nat(name))
    pending = [(tuple(roots), highest + 1, proof)]
    actions = leaves = projections = max_branch = 0
    while pending:
        branch, next_parameter, node = pending.pop()
        actions += 1
        max_branch = max(max_branch, len(branch))
        if not isinstance(node, list) or not node or not isinstance(node[0], str):
            raise ValueError('Every proof node must be a tagged array')
        tag = node[0]

        def previous(index: Any) -> Entry:
            nonlocal projections
            i = nat(index)
            if i >= len(branch):
                raise ValueError('A proof reference is out of range')
            if branch[i].formula[0] == 'hole':
                projections += 1
            return branch[i].exposed()

        if tag == 'bottom' and len(node) == 2:
            e = previous(node[1])
            if not e.positive or e.formula != BOT:
                raise ValueError('Only positive bottom closes a branch')
            leaves += 1
        elif tag == 'close' and len(node) == 3:
            a, b = previous(node[1]), previous(node[2])
            if a.atom() is None or a.atom() != b.atom() or a.positive == b.positive:
                raise ValueError('Closing atoms must evaluate to opposite signs of one pair')
            leaves += 1
        elif tag == 'imp' and len(node) in (3, 4):
            e = previous(node[1])
            if e.formula[0] != 'imp':
                raise ValueError('Implication rule applied to a different constructor')
            a, b = e.formula[1:]
            if e.positive and len(node) == 4:
                pending.append((branch + (e.child(b, True),), next_parameter, node[3]))
                pending.append((branch + (e.child(a, False),), next_parameter, node[2]))
            elif not e.positive and len(node) == 3:
                pending.append((branch + (e.child(a, True), e.child(b, False)),
                                next_parameter, node[2]))
            else:
                raise ValueError('A positive implication requires two closed branches')
        elif tag == 'all' and len(node) in (3, 4):
            e = previous(node[1])
            if e.formula[0] != 'all':
                raise ValueError('Universal rule applied to a different constructor')
            if e.positive and len(node) == 4:
                parameter, child = nat(node[2]), node[3]
                if parameter > next_parameter:
                    raise ValueError('Use an allocated parameter or the next fresh one')
                following = next_parameter + (parameter == next_parameter)
            elif not e.positive and len(node) == 3:
                parameter, child = next_parameter, node[2]
                following = next_parameter + 1
            else:
                raise ValueError('A false universal must use the checker-chosen fresh name')
            body = e.child(e.formula[1], environment=(parameter,) + e.environment)
            pending.append((branch + (body,), following, child))
        else:
            raise ValueError('Unknown proof rule or incorrect arity')
    return {'valid': True, 'actions': actions, 'closed_branches': leaves,
            'template_projections': projections, 'maximum_branch_entries': max_branch}


def check_refutation(certificate: Any) -> dict:
    """Strict fixed-theory entry point. No supplied target or alleged axioms."""
    if (not isinstance(certificate, dict) or set(certificate) != {'matrices', 'proof'}
            or not isinstance(certificate['matrices'], list)):
        raise ValueError('A refutation must contain exactly matrices and proof')
    roots = [axiom(m) for m in certificate['matrices']]
    result = check_tree(roots, certificate['proof'])
    return result | {'refutation': True, 'schema_instances': len(roots)}


def pair(a: int, b: int) -> int:
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n: int) -> tuple[int, int]:
    from math import isqrt
    diagonal = (isqrt(8 * n + 1) - 1) // 2
    b = n - diagonal * (diagonal + 1) // 2
    return diagonal - b, b


def decode_matrix(n: int) -> tuple:
    """Total raw syntax; every output denotes a matrix through default lookup."""
    nat(n)
    if n == 0:
        return BOT
    payload, tag = divmod(n - 1, 3)
    if tag == 0:
        return Rel(*unpair(payload))
    if tag == 1:
        a, b = unpair(payload)
        return Imp(decode_matrix(a), decode_matrix(b))
    return All(decode_matrix(payload))


def encode_matrix(phi: tuple) -> int:
    if phi == BOT:
        return 0
    if phi[0] == 'rel':
        return 1 + 3 * pair(phi[1], phi[2])
    if phi[0] == 'imp':
        return 2 + 3 * pair(encode_matrix(phi[1]), encode_matrix(phi[2]))
    if phi[0] == 'all':
        return 3 + 3 * encode_matrix(phi[1])
    raise ValueError('Only primitive matrix syntax is encodable')


def decode_list(n: int) -> list[int]:
    result = []
    while n:
        head, n = unpair(n - 1)
        result.append(head)
    return result


def encode_list(values: list[int]) -> int:
    result = 0
    for value in reversed(values):
        result = 1 + pair(value, result)
    return result


def decode_tree(n: int) -> list:
    payload, tag = divmod(n, 6)
    if tag == 0:
        return ['close', *unpair(payload)]
    if tag == 1:
        return ['bottom', payload]
    index, tail = unpair(payload)
    if tag == 2:
        return ['imp', index, decode_tree(tail)]
    if tag == 3:
        left, right = unpair(tail)
        return ['imp', index, decode_tree(left), decode_tree(right)]
    if tag == 4:
        return ['all', index, decode_tree(tail)]
    parameter, child = unpair(tail)
    return ['all', index, parameter, decode_tree(child)]


def decode_certificate(n: int) -> dict:
    matrices, proof = unpair(n)
    return {'matrices': [decode_matrix(c) for c in decode_list(matrices)],
            'proof': decode_tree(proof)}


def encode_tree(node: list) -> int:
    tag = node[0]
    if tag == 'close' and len(node) == 3:
        return 6 * pair(node[1], node[2])
    if tag == 'bottom' and len(node) == 2:
        return 6 * node[1] + 1
    if tag == 'imp' and len(node) == 3:
        return 6 * pair(node[1], encode_tree(node[2])) + 2
    if tag == 'imp' and len(node) == 4:
        return 6 * pair(node[1], pair(encode_tree(node[2]), encode_tree(node[3]))) + 3
    if tag == 'all' and len(node) == 3:
        return 6 * pair(node[1], encode_tree(node[2])) + 4
    if tag == 'all' and len(node) == 4:
        return 6 * pair(node[1], pair(node[2], encode_tree(node[3]))) + 5
    raise ValueError('Unknown proof production')


def encode_certificate(certificate: dict) -> int:
    return pair(encode_list([encode_matrix(parse(m)) for m in certificate['matrices']]),
                encode_tree(certificate['proof']))


def accepts_number(n: int) -> bool:
    """Resource exceptions propagate: they never count as refutation or rejection."""
    try:
        return bool(check_refutation(decode_certificate(n))['valid'])
    except ValueError:
        return False


def search() -> int:
    """Unbounded mathematical search specification. Never called by the CLI."""
    candidate = 0
    while not accepts_number(candidate):
        candidate += 1
    return candidate


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', type=Path)
    args = parser.parse_args()
    try:
        print(json.dumps(check_refutation(json.loads(args.certificate.read_text())), indent=2))
    except ValueError as error:
        print(json.dumps({'valid': False, 'error': str(error)}, indent=2))
        raise SystemExit(1)


if __name__ == '__main__':
    main()
