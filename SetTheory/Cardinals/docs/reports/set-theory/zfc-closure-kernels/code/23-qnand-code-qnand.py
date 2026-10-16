#!/usr/bin/env python3
"""Quantified-NAND environment tableaux for equality-free EPSC.

Reference specification, not a compiled or formally verified Turing machine.
The logical grammar has exactly R(i,j) and Q(A,B) = forall x not(A and B),
where Q binds de Bruijn index zero in both children. The public acceptance
predicate generates only closed EPSC axioms from candidate matrix numbers.
There is no conclusion field, Bottom alias, equality, or admitted axiom.

Each proof action starts with an earlier branch-entry index. Its formula
and sign determine all further operands: an atom consumes an opposite-atom
index; positive Q consumes an existing parameter and forks; negative Q has
no further operand, allocates the next parameter, and appends two formulas.
The finite action stream is read in depth-first order and must be exhausted.

Credits: ordinary signed tableaux and de Bruijn notation are classical.
ProveIt batch146 source13 already supplied environment tableaux and a fair
PSC enumerator. Source14 supplied EPSC. The present experiment fuses the
connective and binder, normalizes parameter names, and removes action tags.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
from math import isqrt


class Invalid(ValueError):
    pass


def nat(n):
    if type(n) is not int or n < 0:
        raise Invalid("expected a natural number, excluding bool")
    return n


def pair(a, b):
    nat(a); nat(b)
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n):
    n = nat(n)
    s = (isqrt(8 * n + 1) - 1) // 2
    b = n - s * (s + 1) // 2
    return s - b, b


class Arena:
    """Topological DAG; need[p] is the least environment length for p.

    Interning is an engineering convenience of this reference implementation,
    not required by the proof system or public wire format.
    """
    def __init__(self):
        self.nodes = []
        self.need = []
        self.intern = {}

    def ref(self, p):
        p = nat(p)
        if p >= len(self.nodes):
            raise Invalid("formula reference outside arena")
        return p

    def add(self, tag, a, b):
        if tag not in (0, 1):
            raise Invalid("unknown formula tag")
        a, b = nat(a), nat(b)
        if tag:
            self.ref(a); self.ref(b)
        node = (tag, a, b)
        if node not in self.intern:
            self.intern[node] = len(self.nodes)
            self.nodes.append(node)
            self.need.append(max(0, max(self.need[a], self.need[b]) - 1)
                             if tag else max(a, b) + 1)
        return self.intern[node]

    def rel(self, i, j):
        return self.add(0, i, j)

    def q(self, a, b):
        return self.add(1, a, b)

    def transform(self, p, mapping=None):
        """Shift free indices by one, or apply a finite base-environment map.

        Used only by axiom construction and the diagnostic formula builder.
        Tableau expansion itself never transforms a formula.
        """
        self.ref(p)
        if mapping is not None:
            mapping = tuple(nat(k) for k in mapping)
            if self.need[p] > len(mapping):
                raise Invalid("matrix map has too few slots")
        memo, todo = {}, [(p, 0, False)]
        while todo:
            node, depth, ready = todo.pop()
            if (node, depth) in memo:
                continue
            tag, a, b = self.nodes[node]
            if tag and not ready:
                todo.extend(((node, depth, True), (b, depth + 1, False),
                             (a, depth + 1, False)))
                continue
            if tag:
                result = self.q(memo[a, depth + 1], memo[b, depth + 1])
            else:
                def index(k):
                    if k < depth:
                        return k
                    return k + 1 if mapping is None else depth + mapping[k - depth]
                result = self.rel(index(a), index(b))
            memo[node, depth] = result
        return memo[p, 0]

    def shift(self, p):
        return self.transform(p)

    def nand(self, a, b):
        return self.q(self.shift(a), self.shift(b))

    def neg(self, a):
        shifted = self.shift(a)
        return self.q(shifted, shifted)

    def conj(self, a, b):
        return self.neg(self.nand(a, b))

    def disj(self, a, b):
        return self.nand(self.neg(a), self.neg(b))

    def imp(self, a, b):
        return self.nand(a, self.neg(b))

    def all(self, body):
        negated = self.neg(body)
        return self.q(negated, negated)

    def ex(self, body):
        return self.neg(self.q(body, body))

    def decode(self, n):
        """Every natural is a matrix: even=atom, odd=quantified NAND.

        All recursive odd-node arguments are strictly smaller than their
        parent. Code zero means R(0,0), with no special truth/falsity alias.
        """
        n = nat(n)
        memo, todo = {}, [(n, False)]
        while todo:
            k, ready = todo.pop()
            if k in memo:
                continue
            a, b = unpair(k // 2)
            if k % 2 and not ready:
                todo.extend(((k, True), (b, False), (a, False)))
                continue
            memo[k] = self.q(memo[a], memo[b]) if k % 2 else self.rel(a, b)
        return memo[n]

    def encode(self, root):
        """Diagnostic inverse; very deep numeric codes can be expensive."""
        self.ref(root)
        codes = []
        for tag, a, b in self.nodes[:root + 1]:
            codes.append(2 * pair(codes[a], codes[b]) + 1 if tag
                         else 2 * pair(a, b))
        return codes[root]


def epsc(arena, matrix):
    """Exact empty-input positive subset-closure instance.

    Matrix base slots are input0/output1/parameters2,... . Three fixed slot
    maps plug the unchanged arbitrary matrix into the wrapper's contexts.
    All parameters, including unused gaps below need, are universally closed.
    This is direct de Bruijn construction; it has no named-variable search.
    """
    a = arena
    matrix = a.ref(matrix)
    width = max(2, a.need[matrix])
    parameters = tuple(range(3, width + 1))
    local_phi = a.transform(matrix, (2, 0) + parameters)
    closed_phi = a.transform(matrix, (1, 0) + parameters)
    support_phi = a.transform(matrix, (0, 1) + parameters)

    # Under x,b,y: y=0,b=1,x=2. Under z,x,b,y: z=0,y=1,b=2.
    subset_y_b = a.all(a.imp(a.rel(0, 1), a.rel(0, 2)))
    bounded = a.all(a.ex(a.all(a.imp(local_phi, subset_y_b))))

    # Under c,x,y: y=0,x=1,c=2. The empty predicate binds an additional z.
    empty_x = a.all(a.neg(a.rel(0, 2)))
    active = a.disj(empty_x, a.rel(1, 2))
    closed = a.all(a.all(a.imp(a.conj(active, closed_phi), a.rel(0, 2))))

    # Under c,y: y=0,c=1. Inside the existential x: x=0,y=1,c=2.
    support = a.all(a.imp(a.rel(0, 1), a.ex(support_phi)))
    result = a.imp(bounded, a.ex(a.conj(closed, support)))
    for _ in range(width - 2):
        result = a.all(result)
    if a.need[result] != 0:
        raise Invalid("internal EPSC closure invariant failed")
    return result


@dataclass(frozen=True)
class Entry:
    positive: bool
    formula: int
    environment: tuple[int, ...] = ()


def check_tree(arena, roots, actions):
    """Generic signed-root interface for tests; not the public EPSC predicate."""
    branch = tuple(roots)
    largest = 0
    for e in branch:
        if type(e.positive) is not bool:
            raise Invalid("entry signs must be Boolean")
        arena.ref(e.formula)
        if arena.need[e.formula] > len(e.environment):
            raise Invalid("unbound de Bruijn index")
        for v in e.environment:
            largest = max(largest, nat(v))
    m = largest + 1
    if not isinstance(actions, (list, tuple)):
        raise Invalid("actions must be a finite integer sequence")
    actions = tuple(nat(i) for i in actions)
    cursor = steps = leaves = 0
    maximum_branch = len(branch)
    maximum_parameters = m
    pending = []

    def read():
        nonlocal cursor
        if cursor >= len(actions):
            raise Invalid("truncated action stream")
        result = actions[cursor]
        cursor += 1
        return result

    def previous(i):
        if i >= len(branch):
            raise Invalid("branch-entry index is out of range")
        return branch[i]

    def atom(e):
        tag, i, j = arena.nodes[e.formula]
        return None if tag else (e.environment[i], e.environment[j])

    while True:
        e = previous(read())
        steps += 1
        tag, left, right = arena.nodes[e.formula]
        if not tag:
            other = previous(read())
            if e.positive == other.positive or atom(e) != atom(other):
                raise Invalid("atoms are not opposite evaluated ordered pairs")
            leaves += 1
            if not pending:
                if cursor != len(actions):
                    raise Invalid("trailing data after the last closed branch")
                return {"valid": True, "actions": steps, "operands": cursor,
                        "closed_branches": leaves,
                        "maximum_branch_entries": maximum_branch,
                        "maximum_parameters": maximum_parameters}
            branch, m = pending.pop()
            continue
        if e.positive:
            k = read()
            if k >= m:
                raise Invalid("positive Q must use an existing parameter")
            env = (k,) + e.environment
            pending.append((branch + (Entry(False, right, env),), m))
            branch += (Entry(False, left, env),)
        else:
            env = (m,) + e.environment
            branch += (Entry(True, left, env), Entry(True, right, env))
            m += 1
            maximum_parameters = max(maximum_parameters, m)
        maximum_branch = max(maximum_branch, len(branch))


def check_epsc(matrices, actions):
    """Only this interface is allowed to feed the public refutation search."""
    if not isinstance(matrices, (list, tuple)):
        raise Invalid("matrix list required")
    arena = Arena()
    roots = [Entry(True, epsc(arena, arena.decode(nat(n)))) for n in matrices]
    result = check_tree(arena, roots, actions)
    result.update({"accepted_refutation": True, "schema_instances": len(roots),
                   "formula_dag_nodes": len(arena.nodes)})
    return result


def unary(n):
    return "0" * nat(n) + "1"


def encode_bits(matrices, actions):
    return unary(len(matrices)) + "".join(unary(n) for n in matrices) + "".join(
        unary(n) for n in actions)


def decode_bits(bits):
    if not isinstance(bits, str) or any(c not in "01" for c in bits):
        raise Invalid("wire input is a finite bit string")
    cursor = 0
    def read():
        nonlocal cursor
        stop = bits.find("1", cursor)
        if stop < 0:
            raise Invalid("unterminated unary natural")
        value = stop - cursor
        cursor = stop + 1
        return value
    count = read()
    matrices = [read() for _ in range(count)]
    actions = []
    while cursor < len(bits):
        actions.append(read())
    return matrices, actions


def accepts(bits):
    try:
        matrices, actions = decode_bits(bits)
        return check_epsc(matrices, actions)["accepted_refutation"] is True
    except Invalid:
        return False
    # Host memory/arithmetic failures are not mathematical halts or refutations.


def search():
    """Ideal unbounded finite storage; shortlex enumerates every finite bit word."""
    n = 1
    while True:
        if accepts(bin(n)[3:]):
            return n
        n += 1


def evaluate(arena, root, domain, relation, environment=()):
    """Finite-model test oracle. Not invoked by any acceptance path."""
    tag, left, right = arena.nodes[root]
    if not tag:
        return bool(relation(environment[left], environment[right]))
    return all(not (evaluate(arena, left, domain, relation, (x,) + environment)
                    and evaluate(arena, right, domain, relation, (x,) + environment))
               for x in domain)


def identity_actions(arena, formula, positive, negative, length, m=1):
    """Diagnostic certificate producer for opposite identical closures."""
    tag, left, right = arena.nodes[formula]
    if not tag:
        return [positive, negative]
    return ([negative, positive, m]
            + identity_actions(arena, left, length, length + 2, length + 3, m + 1)
            + identity_actions(arena, right, length + 1, length + 2, length + 3, m + 1))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", type=int, default=1000,
                        help="finite diagnostic candidate count; never a consistency claim")
    args = parser.parse_args()
    if args.prefix < 0:
        parser.error("prefix must be nonnegative")
    accepted = [n for n in range(1, args.prefix + 1) if accepts(bin(n)[3:])]
    print(json.dumps({"candidates_checked": args.prefix, "accepted": accepted,
                      "status": "finite diagnostic only; no consistency conclusion"}, indent=2))


if __name__ == "__main__":
    main()
