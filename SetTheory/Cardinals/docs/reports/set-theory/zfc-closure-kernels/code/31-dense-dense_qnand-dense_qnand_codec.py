#!/usr/bin/env python3
"""A bijective natural-number codec for quantified NAND at fixed positive scope.

Formula syntax is ('rel', i, j) or ('q', A, B).  The connective q binds
de Bruijn index zero in BOTH children and means forall x, not (A and B).

At scope d >= 1, atoms occupy [0, d*d).  All remaining codes are binary
nodes, whose children have scope d+1.  This is a representation artifact,
not a proof checker, a binary Turing machine, or a state-count claim.

Inputs rejected by this module are malformed Python values or ill-scoped
formulas passed to the encoder.  Every natural-number decoder input at
positive scope has a mathematical result.  Host resource failures propagate.
"""
from __future__ import annotations

from itertools import product
from math import isqrt
from typing import Callable

Formula = tuple


def natural(n: int) -> int:
    if type(n) is not int or n < 0:
        raise ValueError('A natural number, excluding Boolean values, is required')
    return n


def positive_scope(d: int) -> int:
    natural(d)
    if d == 0:
        raise ValueError('This codec is defined for positive scope')
    return d


def pair(a: int, b: int) -> int:
    natural(a)
    natural(b)
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n: int) -> tuple[int, int]:
    natural(n)
    diagonal = (isqrt(8 * n + 1) - 1) // 2
    b = n - diagonal * (diagonal + 1) // 2
    return diagonal - b, b


def decode(d: int, n: int) -> Formula:
    """Decode all n >= 0, with memoization indexed by BOTH scope and code."""
    positive_scope(d)
    natural(n)
    memo: dict[tuple[int, int], Formula] = {}
    pending = [(d, n, False)]
    while pending:
        scope, code, ready = pending.pop()
        key = scope, code
        if key in memo:
            continue
        threshold = scope * scope
        if code < threshold:
            j, i = divmod(code, scope)
            memo[key] = ('rel', i, j)
            continue
        a, b = unpair(code - threshold)
        if ready:
            memo[key] = ('q', memo[scope + 1, a], memo[scope + 1, b])
        else:
            pending.extend(((scope, code, True),
                            (scope + 1, b, False),
                            (scope + 1, a, False)))
    return memo[d, n]


def encode(d: int, formula: Formula) -> int:
    """Encode exactly the formulas whose free de Bruijn indices are below d."""
    positive_scope(d)
    if not isinstance(formula, tuple) or not formula:
        raise ValueError('A formula is a nonempty tuple')
    tag = formula[0]
    if tag == 'rel' and len(formula) == 3:
        i, j = natural(formula[1]), natural(formula[2])
        if i >= d or j >= d:
            raise ValueError('Atom exceeds the current scope')
        return i + d * j
    if tag == 'q' and len(formula) == 3:
        return d * d + pair(encode(d + 1, formula[1]),
                            encode(d + 1, formula[2]))
    raise ValueError('Unknown formula constructor or arity')


def scoped(formula: Formula, d: int) -> bool:
    positive_scope(d)
    if formula[0] == 'rel':
        return all(type(i) is int and 0 <= i < d for i in formula[1:])
    if formula[0] == 'q':
        return scoped(formula[1], d + 1) and scoped(formula[2], d + 1)
    return False


def raw_encode(formula: Formula) -> int:
    """The prior QNAND raw codec: even atom; odd quantified NAND.

    This exact algebraic convention is recorded in the incoming ProveIt
    zfc_qnand_research.zip, code/qnand.py. It has no fixed-scope guarantee.
    """
    if formula[0] == 'rel':
        return 2 * pair(formula[1], formula[2])
    if formula[0] == 'q':
        return 1 + 2 * pair(raw_encode(formula[1]), raw_encode(formula[2]))
    raise ValueError('Unknown raw formula constructor')


def evaluate(formula: Formula, environment: tuple[int, ...],
             domain: tuple[int, ...], relation: Callable[[int, int], bool]) -> bool:
    """Ordinary finite-model semantics; a diagnostic, never a consistency test."""
    if not domain:
        raise ValueError('The domain must be nonempty')
    if formula[0] == 'rel':
        return relation(environment[formula[1]], environment[formula[2]])
    if formula[0] == 'q':
        return all(not (evaluate(formula[1], (x,) + environment, domain, relation)
                        and evaluate(formula[2], (x,) + environment, domain, relation))
                   for x in domain)
    raise ValueError('Unknown semantic constructor')


def evaluate_number(d: int, n: int, environment: tuple[int, ...],
                    domain: tuple[int, ...],
                    relation: Callable[[int, int], bool]) -> bool:
    """Direct code semantics, used independently of AST decoding in regressions."""
    positive_scope(d)
    natural(n)
    if len(environment) != d or not domain:
        raise ValueError('Exactly d environment entries and a nonempty domain are required')
    if n < d * d:
        return relation(environment[n % d], environment[n // d])
    left, right = unpair(n - d * d)
    for x in domain:
        extended = (x,) + environment
        a = evaluate_number(d + 1, left, extended, domain, relation)
        b = evaluate_number(d + 1, right, extended, domain, relation)
        if a and b:
            return False
    return True


def assignments(domain: tuple[int, ...], d: int):
    return product(domain, repeat=positive_scope(d))
