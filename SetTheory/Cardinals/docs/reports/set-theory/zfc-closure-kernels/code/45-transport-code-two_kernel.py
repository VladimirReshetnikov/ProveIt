#!/usr/bin/env python3
"""Two-operation reference kernel for equality-free first-order logic.

This is a mathematical reference implementation, not a Turing-machine compiler.
Bound variables use nonnegative de Bruijn indices. Free names are integers.
The only primitive renamings are up and fused_down; see name_step below.
Adapted from ProveIt source 28 under MIT-0. Other inference rules are unchanged.
All operate only on free names. Proofs have no assumption-opening instruction.
The only AX instruction refers to a supplied finite list of *closed* axioms.

Tuple syntax:
  variable = ('b', index) | ('f', integer)
  formula  = ('bot',) | ('rel', var, var) | ('imp', formula, formula)
             | ('all', formula)
"""

from __future__ import annotations

from itertools import product
from typing import Callable, Iterable

Var = tuple
Formula = tuple
BOT: Formula = ('bot',)
RENAMINGS = frozenset(('up', 'fused_down'))


def B(index: int) -> Var:
    return ('b', index)


def F(name: int) -> Var:
    return ('f', name)


def R(a: Var, b: Var) -> Formula:
    return ('rel', a, b)


def Imp(a: Formula, b: Formula) -> Formula:
    return ('imp', a, b)


def All(body: Formula) -> Formula:
    return ('all', body)


def Not(a: Formula) -> Formula:
    return Imp(a, BOT)


def And(a: Formula, b: Formula) -> Formula:
    return Not(Imp(a, Not(b)))


def Iff(a: Formula, b: Formula) -> Formula:
    return And(Imp(a, b), Imp(b, a))


def freeze(value):
    """Read JSON arrays as immutable syntax, preserving integer names."""
    if isinstance(value, list):
        return tuple(freeze(x) for x in value)
    return value


def integer(n) -> bool:
    return type(n) is int


def scoped(formula: Formula, depth: int = 0) -> bool:
    if not isinstance(formula, tuple) or not formula:
        return False
    tag = formula[0]
    if tag == 'bot':
        return len(formula) == 1
    if tag == 'rel' and len(formula) == 3:
        for var in formula[1:]:
            if not isinstance(var, tuple) or len(var) != 2:
                return False
            if not integer(var[1]):
                return False
            if var[0] == 'b':
                if not 0 <= var[1] < depth:
                    return False
            elif var[0] != 'f':
                return False
        return True
    if tag == 'imp' and len(formula) == 3:
        return scoped(formula[1], depth) and scoped(formula[2], depth)
    if tag == 'all' and len(formula) == 2:
        return scoped(formula[1], depth + 1)
    return False


def free_names(formula: Formula) -> set[int]:
    tag = formula[0]
    if tag == 'bot':
        return set()
    if tag == 'rel':
        return {v[1] for v in formula[1:] if v[0] == 'f'}
    if tag == 'imp':
        return free_names(formula[1]) | free_names(formula[2])
    return free_names(formula[1])


def edit(formula: Formula, fn: Callable[[Var, int], Var], depth=0) -> Formula:
    tag = formula[0]
    if tag == 'bot':
        return BOT
    if tag == 'rel':
        return R(fn(formula[1], depth), fn(formula[2], depth))
    if tag == 'imp':
        return Imp(edit(formula[1], fn, depth), edit(formula[2], fn, depth))
    return All(edit(formula[1], fn, depth + 1))


def rename(formula: Formula, fn: Callable[[int], int]) -> Formula:
    return edit(formula, lambda var, _: F(fn(var[1])) if var[0] == 'f' else var)


def name_step(op: str, name: int) -> int:
    if op == 'up':
        return name + 1
    if op == 'fused_down':
        return 1 if name == 0 else -1 if name == 1 else name - 1
    raise ValueError('unknown primitive free-name map')


def rename_step(op: str, formula: Formula) -> Formula:
    return rename(formula, lambda name: name_step(op, name))


def open_body(body: Formula, name: int) -> Formula:
    """Delete the displayed outer binder and replace its occurrences by F(name).

    Precondition scoped(body, 1) ensures there is no dangling index above depth.
    Internal binders retain their de Bruijn indices; all free fields are copied.
    """
    if not scoped(body, 1) or not integer(name):
        raise ValueError('malformed body/name')
    return edit(body, lambda var, d: F(name) if var == B(d) else var)


def close_name(formula: Formula, name: int) -> Formula:
    """Abstract one free name, making a body for a new outer binder."""
    if not scoped(formula) or not integer(name):
        raise ValueError('malformed formula/name')
    return edit(formula, lambda var, d: B(d) if var == F(name) else var)


def evaluate(formula: Formula, domain: tuple, relation: Callable,
             assignment: Callable[[int], object], stack=()) -> bool:
    def val(var):
        return stack[var[1]] if var[0] == 'b' else assignment(var[1])
    tag = formula[0]
    if tag == 'bot':
        return False
    if tag == 'rel':
        return bool(relation(val(formula[1]), val(formula[2])))
    if tag == 'imp':
        return (not evaluate(formula[1], domain, relation, assignment, stack)
                or evaluate(formula[2], domain, relation, assignment, stack))
    return all(evaluate(formula[1], domain, relation, assignment, (x,) + stack)
               for x in domain)


def check_certificate(certificate: dict, theory: Iterable[Formula] = ()) -> list:
    """Reconstruct every line; raises ValueError on every malformed certificate.

    A theory axiom must be closed. The input theory is the object theory whose
    consequence relation is being checked; it is not a list of accepted proofs.
    A consistency search must fix its theory/axiom emitter independently of
    candidates, and search only for reconstructed BOT.
    """
    if not isinstance(certificate, dict):
        raise ValueError('certificate must be an object')
    theory = tuple(freeze(a) for a in theory)
    if any(not scoped(a) or free_names(a) for a in theory):
        raise ValueError('theory axioms must be closed well-scoped formulas')
    instructions = certificate.get('instructions')
    if not isinstance(instructions, list):
        raise ValueError('missing instruction list')
    lines = []

    def prior(index):
        if not integer(index) or not 0 <= index < len(lines):
            raise ValueError('forward, negative or noninteger line reference')
        return lines[index]

    def formula_arg(ins, name, depth=0):
        formula = freeze(ins.get(name))
        if not scoped(formula, depth):
            raise ValueError('ill-scoped formula argument')
        return formula

    for ins in instructions:
        if not isinstance(ins, dict) or not isinstance(ins.get('op'), str):
            raise ValueError('malformed instruction')
        op = ins['op']
        if op in RENAMINGS:
            result = rename_step(op, prior(ins.get('line')))
        elif op == 'fresh_ui':
            body = formula_arg(ins, 'body', 1)
            fresh = ins.get('fresh')
            if not integer(fresh) or fresh in free_names(body):
                raise ValueError('fresh UI requires a name absent from the body')
            result = Imp(All(body), open_body(body, fresh))
        elif op == 'K':
            a, b = formula_arg(ins, 'a'), formula_arg(ins, 'b')
            result = Imp(a, Imp(b, a))
        elif op == 'S':
            a, b, c = (formula_arg(ins, k) for k in ('a', 'b', 'c'))
            result = Imp(Imp(a, Imp(b, c)), Imp(Imp(a, b), Imp(a, c)))
        elif op == 'Peirce':
            a, b = formula_arg(ins, 'a'), formula_arg(ins, 'b')
            result = Imp(Imp(Imp(a, b), a), a)
        elif op == 'exfalso':
            result = Imp(BOT, formula_arg(ins, 'a'))
        elif op == 'distribution':
            a, b = formula_arg(ins, 'a', 1), formula_arg(ins, 'b', 1)
            result = Imp(All(Imp(a, b)), Imp(All(a), All(b)))
        elif op == 'vacuity':
            a = formula_arg(ins, 'a')
            result = Imp(a, All(a))
        elif op == 'gen':
            a, name = prior(ins.get('line')), ins.get('name')
            if not integer(name):
                raise ValueError('bad generalization name')
            result = All(close_name(a, name))
        elif op == 'mp':
            implication = prior(ins.get('implication'))
            antecedent = prior(ins.get('antecedent'))
            if implication[0] != 'imp' or implication[1] != antecedent:
                raise ValueError('modus ponens does not match')
            result = implication[2]
        elif op == 'axiom':
            index = ins.get('index')
            if not integer(index) or not 0 <= index < len(theory):
                raise ValueError('unknown fixed theory axiom')
            result = theory[index]
        else:
            raise ValueError('unknown instruction')
        if not scoped(result):
            raise ValueError('internal scope invariant failed')
        if 'result' in ins and freeze(ins['result']) != result:
            raise ValueError('supplied line does not equal reconstructed line')
        lines.append(result)
    if 'conclusion' in certificate:
        if not lines or freeze(certificate['conclusion']) != lines[-1]:
            raise ValueError('incorrect final conclusion')
    return lines

