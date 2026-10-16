#!/usr/bin/env python3
"""Shared-template, environment-based tableaux for equality-free PSC.

This is an executable research reference, NOT a small binary TM or a verified
proof-assistant kernel. Abstract execution has unbounded finite storage.
Resource exceptions are execution failures, never accepted refutations.

Source syntax: B; R(term,term); I(formula,formula); A(formula).
Terms: ('b',n) for bound de Bruijn indices, ('f',n) for free matrix names.
Free names 0/1 are matrix input/output slots; others are parameters.
The private fixed template additionally has H(input_index,output_index).
No H, assumed conclusion, equality, or custom axiom is accepted as input.

Prior architecture: ProveIt's 2026-10-16 equality-free PSC reports and the
environment-tableau proposal. This implementation adds shared template calls,
separate matrix binder stacks, and dynamic parameterized AX instructions.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass, replace
import json
from pathlib import Path
from typing import Any

Formula = tuple
Term = tuple[str, int]
BOT: Formula = ('B',)


def nat(value: Any) -> int:
    if type(value) is not int or value < 0:
        raise ValueError('Expected a nonnegative integer; Booleans are not codes')
    return value


def term(raw: Any, depth: int) -> Term:
    if not isinstance(raw, (tuple, list)) or len(raw) != 2 or raw[0] not in ('b', 'f'):
        raise ValueError('Bad source term')
    n = nat(raw[1])
    if raw[0] == 'b' and n >= depth:
        raise ValueError('Unbound source de Bruijn index')
    return raw[0], n


def parse(raw: Any, depth: int = 0) -> Formula:
    if not isinstance(raw, (tuple, list)) or not raw:
        raise ValueError('Formula must be a nonempty array')
    op = raw[0]
    if op == 'B' and len(raw) == 1:
        return BOT
    if op == 'R' and len(raw) == 3:
        return op, term(raw[1], depth), term(raw[2], depth)
    if op == 'I' and len(raw) == 3:
        return op, parse(raw[1], depth), parse(raw[2], depth)
    if op == 'A' and len(raw) == 2:
        return op, parse(raw[1], depth + 1)
    raise ValueError('Bad source formula; template holes are private')


def closed(formula: Formula) -> bool:
    op = formula[0]
    if op == 'R':
        return formula[1][0] == formula[2][0] == 'b'
    if op == 'I':
        return closed(formula[1]) and closed(formula[2])
    if op == 'A':
        return closed(formula[1])
    return op == 'B'


def make_template() -> Formula:
    """Compile the fixed hygienic named wrapper, never a supplied matrix."""
    R = lambda x, y: ('r', x, y)
    H = lambda x, y: ('h', x, y)
    I = lambda a, b: ('i', a, b)
    A = lambda x, a: ('a', x, a)
    N = lambda a: I(a, BOT)
    Ex = lambda x, a: N(A(x, N(a)))
    And = lambda a, b: N(I(a, N(b)))
    Or = lambda a, b: I(N(a), b)
    Sub = lambda x, y: A('z', I(R('z', x), R('z', y)))
    sb = A('x', Ex('b', A('y', I(H('x', 'y'), Sub('y', 'b')))))
    guard = Or(Sub('x', 'a'), R('x', 'h'))
    recurrent = A('x', I(guard, A('y', I(H('x', 'y'), R('y', 'h')))))
    support = A('y', I(R('y', 'h'), Ex('x', H('x', 'y'))))
    wrapper = I(sb, A('a', Ex('h', And(recurrent, support))))

    def convert(f, binders=()):
        if f == BOT:
            return BOT
        if f[0] == 'r':
            return 'R', ('b', binders.index(f[1])), ('b', binders.index(f[2]))
        if f[0] == 'h':
            return 'H', binders.index(f[1]), binders.index(f[2])
        if f[0] == 'i':
            return 'I', convert(f[1], binders), convert(f[2], binders)
        return 'A', convert(f[2], (f[1],) + binders)

    return convert(wrapper)


TEMPLATE = make_template()


@dataclass(frozen=True)
class Root:
    matrix: Formula
    parameters: tuple[tuple[int, int], ...] = ()

    def parameter(self, label: int) -> int:
        for key, value in self.parameters:
            if key == label:
                return value
        return 0


@dataclass(frozen=True)
class Closure:
    template: bool
    node: Formula
    bound: tuple[int, ...] = ()
    root: Root | None = None
    slots: tuple[int, int] = (0, 0)

    def expose(self) -> 'Closure':
        if self.node[0] != 'H':
            return self
        if not self.template or self.root is None:
            raise ValueError('Internal template-call invariant failed')
        # Critical: matrix binders start at zero depth. The surrounding wrapper
        # is visible ONLY through the two explicit free-slot overrides.
        return Closure(False, self.root.matrix, (), self.root,
                       (self.bound[self.node[1]], self.bound[self.node[2]]))

    def child(self, which: int, parameter: int | None = None) -> 'Closure':
        q = self.expose()
        env = q.bound if parameter is None else (parameter,) + q.bound
        return replace(q, node=q.node[which], bound=env)

    def value(self, t: Term) -> int:
        if t[0] == 'b':
            return self.bound[t[1]]
        if t[1] < 2:
            return self.slots[t[1]]
        return 0 if self.root is None else self.root.parameter(t[1])

    def atom(self) -> tuple[int, int] | None:
        q = self.expose()
        if q.node[0] != 'R':
            return None
        return q.value(q.node[1]), q.value(q.node[2])


@dataclass(frozen=True)
class Entry:
    positive: bool
    closure: Closure


def parameter_map(raw: Any, counter: int) -> tuple[tuple[int, int], ...]:
    if not isinstance(raw, (list, tuple)):
        raise ValueError('Parameter map must be a list')
    result = {}
    for item in raw:
        if not isinstance(item, (list, tuple)) or len(item) != 2:
            raise ValueError('Bad parameter-map entry')
        label, value = nat(item[0]), nat(item[1])
        if label < 2 or label in result or value >= counter:
            raise ValueError('Duplicate/reserved label or unallocated parameter')
        result[label] = value
    return tuple(sorted(result.items()))


def check(certificate: Any, *, theorem: Any | None = None) -> dict:
    """Only theorem=None is the refutation-search acceptance interface.

    Certificate = {'matrices': [source AST, ...], 'proof': proof tree}.
    The optional theorem interface is for closed logical demonstration files;
    it never labels a theorem demonstration as a refutation.
    """
    if not isinstance(certificate, dict) or set(certificate) != {'matrices', 'proof'}:
        raise ValueError('Expected exactly matrices and proof')
    if not isinstance(certificate['matrices'], list):
        raise ValueError('Matrix pool must be a list')
    matrices = tuple(parse(m) for m in certificate['matrices'])
    target = BOT if theorem is None else parse(theorem)
    if not closed(target):
        raise ValueError('A demonstration target must be a closed sentence')
    roots = (Entry(False, Closure(False, target)),)
    pending = [(roots, 1, certificate['proof'])]
    actions = leaves = ax_calls = matrix_calls = 0
    maximum_entries = maximum_parameters = 1
    while pending:
        branch, counter, node = pending.pop()
        maximum_entries = max(maximum_entries, len(branch))
        maximum_parameters = max(maximum_parameters, counter)
        if not isinstance(node, (tuple, list)) or not node:
            raise ValueError('Every proof instruction must be a tagged array')
        op = node[0]
        actions += 1

        def previous(raw):
            nonlocal matrix_calls
            i = nat(raw)
            if i >= len(branch):
                raise ValueError('Out-of-range branch reference')
            entry = branch[i]
            if entry.closure.node[0] == 'H':
                matrix_calls += 1
            return entry

        if op == 'AX' and len(node) == 4:
            i = nat(node[1])
            if i >= len(matrices):
                raise ValueError('Out-of-range matrix-pool reference')
            params = parameter_map(node[2], counter)
            entry = Entry(True, Closure(True, TEMPLATE, (), Root(matrices[i], params)))
            pending.append((branch + (entry,), counter, node[3]))
            ax_calls += 1
            continue
        if op == 'X' and len(node) == 3:
            a, b = previous(node[1]), previous(node[2])
            if a.positive == b.positive or a.closure.atom() is None or a.closure.atom() != b.closure.atom():
                raise ValueError('Closure requires opposite signs on the same evaluated atom')
            leaves += 1
            continue
        if op == 'B' and len(node) == 2:
            e = previous(node[1])
            if not e.positive or e.closure.expose().node != BOT:
                raise ValueError('Only positive primitive Bottom closes a branch')
            leaves += 1
            continue
        if op in ('I-', 'I+'):
            if len(node) != (3 if op == 'I-' else 4):
                raise ValueError('Wrong implication-rule arity')
            e = previous(node[1])
            if e.positive != (op == 'I+') or e.closure.expose().node[0] != 'I':
                raise ValueError('Wrong implication rule sign or constructor')
            a, b = e.closure.child(1), e.closure.child(2)
            if op == 'I-':
                pending.append((branch + (Entry(True, a), Entry(False, b)), counter, node[2]))
            else:
                pending.append((branch + (Entry(True, b),), counter, node[3]))
                pending.append((branch + (Entry(False, a),), counter, node[2]))
            continue
        if op in ('A-', 'A+'):
            if len(node) != (3 if op == 'A-' else 4):
                raise ValueError('Wrong quantifier-rule arity')
            e = previous(node[1])
            if e.positive != (op == 'A+') or e.closure.expose().node[0] != 'A':
                raise ValueError('Wrong quantifier rule sign or constructor')
            if op == 'A-':
                parameter, child, new_counter = counter, node[2], counter + 1
            else:
                parameter = nat(node[2])
                if parameter >= counter:
                    raise ValueError('Gamma requires an allocated parameter')
                child, new_counter = node[3], counter
            body = Entry(e.positive, e.closure.child(1, parameter))
            pending.append((branch + (body,), new_counter, child))
            continue
        raise ValueError('Unknown proof instruction')
    return dict(valid=True, refutation=theorem is None, actions=actions,
                closed_branches=leaves, axiom_calls=ax_calls,
                matrix_exposures=matrix_calls, maximum_branch_entries=maximum_entries,
                maximum_allocated_parameters=maximum_parameters,
                matrix_pool_size=len(matrices))


def evaluate(closure: Closure, relation: tuple[tuple[bool, ...], ...]) -> bool:
    """Finite semantic oracle for tests; NOT used by the proof checker."""
    q = closure.expose()
    op = q.node[0]
    if op == 'B':
        return False
    if op == 'R':
        a, b = q.atom()
        return relation[a][b]
    if op == 'I':
        return not evaluate(q.child(1), relation) or evaluate(q.child(2), relation)
    if op == 'A':
        return all(evaluate(q.child(1, a), relation) for a in range(len(relation)))
    raise ValueError('Internal closure tag')


def materialize(matrix: Formula, parameters: tuple[tuple[int, int], ...] = ()) -> Formula:
    """Diagnostic expansion with capture-free lifting. NEVER used by check().

    Result parameters are free names. Free name j denotes parameter id j.
    This is a separate reference for the template-call semantics.
    """
    params = dict(parameters)

    def plug(f, input_index, output_index, depth=0):
        def variable(v):
            if v[0] == 'b':
                return v
            if v[1] == 0:
                return 'b', input_index + depth
            if v[1] == 1:
                return 'b', output_index + depth
            return 'f', params.get(v[1], 0)
        if f[0] == 'R':
            return 'R', variable(f[1]), variable(f[2])
        if f[0] == 'I':
            return 'I', plug(f[1], input_index, output_index, depth), plug(f[2], input_index, output_index, depth)
        if f[0] == 'A':
            return 'A', plug(f[1], input_index, output_index, depth + 1)
        return BOT

    def walk(f):
        if f[0] == 'H':
            return plug(matrix, f[1], f[2])
        if f[0] == 'I':
            return 'I', walk(f[1]), walk(f[2])
        if f[0] == 'A':
            return 'A', walk(f[1])
        return f

    return walk(TEMPLATE)


def ordinary_eval(f: Formula, relation, bound=(), free=None) -> bool:
    """Independent locally nameless semantics, for expanded test formulas."""
    free = {} if free is None else free
    def v(t):
        return bound[t[1]] if t[0] == 'b' else free.get(t[1], t[1])
    if f[0] == 'B':
        return False
    if f[0] == 'R':
        return relation[v(f[1])][v(f[2])]
    if f[0] == 'I':
        return not ordinary_eval(f[1], relation, bound, free) or ordinary_eval(f[2], relation, bound, free)
    if f[0] == 'A':
        return all(ordinary_eval(f[1], relation, (a,) + bound, free) for a in range(len(relation)))
    raise ValueError('Not an ordinary formula')


def size(f: Formula) -> int:
    if f[0] == 'I':
        return 1 + size(f[1]) + size(f[2])
    if f[0] == 'A':
        return 1 + size(f[1])
    return 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', type=Path)
    parser.add_argument('--theorem', type=Path,
                        help='Closed theorem demonstration only, never a refutation search')
    args = parser.parse_args()
    try:
        target = json.loads(args.theorem.read_text()) if args.theorem else None
        if args.theorem and target is None:
            raise ValueError('An explicit theorem file must contain a closed formula, not null')
        result = check(json.loads(args.certificate.read_text()), theorem=target)
    except ValueError as error:
        print(json.dumps({'valid': False, 'error': str(error)}, indent=2))
        raise SystemExit(1)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
