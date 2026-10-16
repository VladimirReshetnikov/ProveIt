#!/usr/bin/env python3
"""Environment-based tableaux for the one-schema equality-free PSC theory.

This is a finite-certificate reference, not a compiled small Turing machine.
The mathematical verifier has unbounded finite storage. Resource exhaustion in
this Python implementation is an execution failure, never a refutation.
Formula constructors: ('bot',), ('rel', i, j), ('imp', A, B), ('all', A).
Indices in atoms are De Bruijn indices into an explicit parameter environment.
No textual substitution or alpha comparison occurs in the tableau checker.
"""
from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import qpsc_syntax as ns

Formula = tuple
BOT: Formula = ('bot',)


def natural(n: Any) -> int:
    if type(n) is not int or n < 0:
        raise ValueError('Expected a nonnegative integer, not a Boolean')
    return n


def parse_formula(raw: Any) -> Formula:
    if not isinstance(raw, (list, tuple)) or not raw:
        raise ValueError('A formula must be a nonempty array')
    op = raw[0]
    if op == 'bot' and len(raw) == 1:
        return BOT
    if op == 'rel' and len(raw) == 3:
        return (op, natural(raw[1]), natural(raw[2]))
    if op == 'imp' and len(raw) == 3:
        return (op, parse_formula(raw[1]), parse_formula(raw[2]))
    if op == 'all' and len(raw) == 2:
        return (op, parse_formula(raw[1]))
    raise ValueError('Unknown formula constructor or wrong arity')


def scoped(formula: Formula, depth: int = 0) -> bool:
    op = formula[0]
    if op == 'bot':
        return True
    if op == 'rel':
        return formula[1] < depth and formula[2] < depth
    if op == 'imp':
        return scoped(formula[1], depth) and scoped(formula[2], depth)
    return scoped(formula[1], depth + 1)


def from_named(formula: Formula, binders: tuple[int, ...] = ()) -> Formula:
    """Convert a closed named formula; reject every unbound occurrence."""
    op = formula[0]
    if op == 'B':
        return BOT
    if op == 'T':
        return ('imp', BOT, BOT)
    if op == 'E':
        try:
            return ('rel', binders.index(formula[1]), binders.index(formula[2]))
        except ValueError as exc:
            raise ValueError('An input formula is not closed') from exc
    if op == 'I':
        return ('imp', from_named(formula[1], binders),
                from_named(formula[2], binders))
    if op == 'A':
        return ('all', from_named(formula[2], (formula[1],) + binders))
    raise ValueError('Equality and schema holes are not executable syntax')


def psc_axiom(matrix: Any) -> Formula:
    """Free named slots 0 and 1 are input/output; others are parameters.

    Axiom construction reuses the attributed, capture-avoiding named wrapper.
    Its parameters are universally closed before conversion to De Bruijn form.
    The proof checker below uses environments, not this substitution routine.
    """
    result = from_named(ns.closure(ns.parse(matrix), seed='subset', mixed=False))
    if not scoped(result):
        raise ValueError('Internal scope error in the generated PSC axiom')
    return result


@dataclass(frozen=True)
class Entry:
    positive: bool
    formula: Formula
    environment: tuple[int, ...] = ()

    def atom(self) -> tuple[int, int] | None:
        if self.formula[0] != 'rel':
            return None
        return (self.environment[self.formula[1]],
                self.environment[self.formula[2]])


def check_tree(roots: list[Entry], proof: Any) -> dict[str, Any]:
    """Check a finite tableau. This generic interface is used by regression tests.

    A Q_PSC refutation must enter through check_certificate, which generates all
    nonlogical roots itself and fixes the target to bottom unless a theorem is
    explicitly requested. Branch parameters start with 0, for nonempty domains.
    """
    for entry in roots:
        if type(entry.positive) is not bool:
            raise ValueError('Signs must be Boolean')
        if not scoped(entry.formula, len(entry.environment)):
            raise ValueError('Unbound De Bruijn index')
        for value in entry.environment:
            natural(value)
    initial_used = frozenset({0} | {v for e in roots for v in e.environment})
    pending = [(tuple(roots), initial_used, proof)]
    actions = leaves = max_branch = 0
    while pending:
        branch, used, node = pending.pop()
        max_branch = max(max_branch, len(branch))
        if not isinstance(node, list) or not node or not isinstance(node[0], str):
            raise ValueError('Every proof node must be a tagged array')
        tag = node[0]
        actions += 1

        def previous(i: Any) -> Entry:
            i = natural(i)
            if i >= len(branch):
                raise ValueError('A proof reference is out of range')
            return branch[i]

        if tag == 'close' and len(node) == 3:
            left, right = previous(node[1]), previous(node[2])
            if (left.atom() is None or left.atom() != right.atom()
                    or left.positive == right.positive):
                raise ValueError('Closing atoms are not complementary')
            leaves += 1
            continue
        if tag == 'bottom' and len(node) == 2:
            entry = previous(node[1])
            if not entry.positive or entry.formula != BOT:
                raise ValueError('Only positive bottom closes a branch')
            leaves += 1
            continue
        if tag == 'imp' and len(node) in (3, 4):
            entry = previous(node[1])
            if entry.formula[0] != 'imp':
                raise ValueError('Implication rule used on another constructor')
            a, b = entry.formula[1:]
            env = entry.environment
            if entry.positive and len(node) == 4:
                pending.append((branch + (Entry(True, b, env),), used, node[3]))
                pending.append((branch + (Entry(False, a, env),), used, node[2]))
            elif not entry.positive and len(node) == 3:
                pending.append((branch + (Entry(True, a, env), Entry(False, b, env)),
                                used, node[2]))
            else:
                raise ValueError('Positive implication needs two proof branches')
            continue
        if tag == 'all' and len(node) in (3, 4):
            entry = previous(node[1])
            if entry.formula[0] != 'all':
                raise ValueError('Quantifier rule used on another constructor')
            if entry.positive and len(node) == 4:
                parameter, child = natural(node[2]), node[3]
            elif not entry.positive and len(node) == 3:
                parameter, child = max(used) + 1, node[2]
            else:
                raise ValueError('A negative universal chooses its own fresh parameter')
            body = Entry(entry.positive, entry.formula[1],
                         (parameter,) + entry.environment)
            pending.append((branch + (body,), used | {parameter}, child))
            continue
        raise ValueError('Unknown tableau rule or wrong arity')
    return {'valid': True, 'closed_branches': leaves, 'actions': actions,
            'maximum_branch_entries': max_branch}


def check_certificate(certificate: Any) -> dict[str, Any]:
    if not isinstance(certificate, dict):
        raise ValueError('Expected a certificate object')
    if set(certificate) - {'matrices', 'proof', 'theorem'}:
        raise ValueError('Unknown certificate field')
    matrices = certificate.get('matrices')
    if not isinstance(matrices, list) or 'proof' not in certificate:
        raise ValueError('Expected matrices and a proof')
    axioms = [psc_axiom(m) for m in matrices]
    conclusion = parse_formula(certificate['theorem']) if 'theorem' in certificate else BOT
    if not scoped(conclusion):
        raise ValueError('The conclusion must be a sentence')
    roots = [Entry(True, a) for a in axioms] + [Entry(False, conclusion)]
    result = check_tree(roots, certificate['proof'])
    result.update({'refutation': conclusion == BOT, 'schema_instances': len(axioms),
                   'conclusion': conclusion})
    return result


def identity_tree(formula: Formula, positive: int, negative: int,
                  length: int, used: frozenset[int] = frozenset({0})) -> list:
    """Construct a finite tableau for A and not A with identical environments.

    Used only to make sample certificates. The checker never trusts this code.
    """
    op = formula[0]
    if op == 'bot':
        return ['bottom', positive]
    if op == 'rel':
        return ['close', positive, negative]
    if op == 'all':
        fresh = max(used) + 1
        child = identity_tree(formula[1], length + 1, length, length + 2,
                              used | {fresh})
        return ['all', negative, ['all', positive, fresh, child]]
    a, b = formula[1:]
    left = identity_tree(a, length, length + 2, length + 3, used)
    right = identity_tree(b, length + 2, length + 1, length + 3, used)
    return ['imp', negative, ['imp', positive, left, right]]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', type=Path)
    args = parser.parse_args()
    try:
        result = check_certificate(json.loads(args.certificate.read_text()))
    except (ValueError, KeyError, IndexError) as exc:
        print(json.dumps({'valid': False, 'error': str(exc)}, indent=2))
        raise SystemExit(1)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
