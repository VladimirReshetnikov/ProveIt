#!/usr/bin/env python3
"""Small first-order syntax utilities for the research experiments.

This is NOT a derivation checker or a Turing-machine compiler.  The logical
basis is membership, equality, negation, implication, and universal quantification.
A schema hole carries its ordered list of free-variable arguments.
"""
from __future__ import annotations
from dataclasses import dataclass
from collections import Counter
from typing import Callable, Mapping

@dataclass(frozen=True)
class Formula:
    op: str
    args: tuple

F = Formula

def mem(x: int, y: int) -> F: return F('mem', (x, y))
def eq(x: int, y: int) -> F: return F('eq', (x, y))
def hole(*args: int) -> F: return F('hole', tuple(args))
def neg(p: F) -> F: return F('not', (p,))
def imp(p: F, q: F) -> F: return F('imp', (p, q))
def all_(v: int, p: F) -> F: return F('all', (v, p))
def ex(v: int, p: F) -> F: return neg(all_(v, neg(p)))
def and_(p: F, q: F) -> F: return neg(imp(p, neg(q)))
def or_(p: F, q: F) -> F: return imp(neg(p), q)
def iff(p: F, q: F) -> F: return and_(imp(p, q), imp(q, p))
def alls(vs: list[int], p: F) -> F:
    for v in reversed(vs): p = all_(v, p)
    return p

def ball(v: int, a: int, p: F) -> F: return all_(v, imp(mem(v, a), p))
def bex(v: int, a: int, p: F) -> F: return ex(v, and_(mem(v, a), p))
def subset(a: int, b: int, fresh: int) -> F:
    if fresh in (a, b): raise ValueError('subset witness is not fresh')
    return all_(fresh, imp(mem(fresh, a), mem(fresh, b)))
def same_members(a: int, b: int, fresh: int) -> F:
    if fresh in (a, b): raise ValueError('profile witness is not fresh')
    return all_(fresh, iff(mem(fresh, a), mem(fresh, b)))

def free_vars(p: F) -> set[int]:
    if p.op in ('mem', 'eq', 'hole'): return set(p.args)
    if p.op == 'all': return free_vars(p.args[1]) - {p.args[0]}
    return set().union(*(free_vars(a) for a in p.args))

def all_vars(p: F) -> set[int]:
    if p.op in ('mem', 'eq', 'hole'): return set(p.args)
    if p.op == 'all': return {p.args[0]} | all_vars(p.args[1])
    return set().union(*(all_vars(a) for a in p.args))

def substitute(p: F, variable: int, value: int) -> F:
    """Capture-avoiding substitution of a variable for a free variable."""
    if variable == value or variable not in free_vars(p): return p
    if p.op in ('mem', 'eq', 'hole'):
        return F(p.op, tuple(value if v == variable else v for v in p.args))
    if p.op == 'all':
        binder, body = p.args
        if binder == variable: return p
        if binder == value:
            fresh = max(all_vars(p) | {variable, value}) + 1
            body = substitute(body, binder, fresh)
            binder = fresh
        return all_(binder, substitute(body, variable, value))
    return F(p.op, tuple(substitute(a, variable, value) for a in p.args))

def erase_equality(p: F) -> F:
    """Replace logical equality by same-members equivalence (not raw identity).

    This translation is sound as an equality interpretation under EC, not in
    every binary structure.  Each new binder is fresh even for shadowing inputs.
    """
    fresh = max(all_vars(p), default=-1) + 1
    def go(q: F) -> F:
        nonlocal fresh
        if q.op == 'eq':
            z = fresh; fresh += 1
            return same_members(q.args[0], q.args[1], z)
        if q.op in ('mem', 'hole'): return q
        if q.op == 'all': return all_(q.args[0], go(q.args[1]))
        return F(q.op, tuple(go(a) for a in q.args))
    return go(p)

def alpha_reuse(p: F) -> F:
    """Reuse bound variable names using free-variable liveness.

    The result is alpha-equivalent, not a claim about globally minimal coding.
    It can shadow an outer binder exactly when that value is unused below.
    """
    def go(q: F, mapping: dict[int, int]) -> F:
        if q.op in ('mem', 'eq', 'hole'):
            return F(q.op, tuple(mapping.get(v, v) for v in q.args))
        if q.op == 'all':
            binder, body = q.args
            forbidden = {mapping.get(v, v) for v in free_vars(body) - {binder}}
            target = 0
            while target in forbidden: target += 1
            updated = dict(mapping); updated[binder] = target
            return all_(target, go(body, updated))
        return F(q.op, tuple(go(a, mapping) for a in q.args))
    return go(p, {})

def evaluate(p: F, n: int, relation: Callable[[int, int], bool],
             assignment: Mapping[int, int] | None = None,
             hole_value: Callable[[tuple[int, ...]], bool] | None = None) -> bool:
    """Finite-structure semantics. Equality here is genuine identity."""
    if n < 1: raise ValueError('classical first-order domains must be nonempty')
    env = dict(assignment or {})
    def go(q: F, a: dict[int, int]) -> bool:
        if q.op == 'mem': return bool(relation(a[q.args[0]], a[q.args[1]]))
        if q.op == 'eq': return a[q.args[0]] == a[q.args[1]]
        if q.op == 'hole':
            if hole_value is None: raise ValueError('cannot evaluate an uninstantiated hole')
            return hole_value(tuple(a[v] for v in q.args))
        if q.op == 'not': return not go(q.args[0], a)
        if q.op == 'imp': return not go(q.args[0], a) or go(q.args[1], a)
        if q.op == 'all':
            v, body = q.args
            return all(go(body, a | {v: x}) for x in range(n))
        raise ValueError(f'unknown operator: {q.op}')
    return go(p, env)

def metrics(p: F) -> dict:
    counts: Counter[str] = Counter()
    subtrees: set[F] = set()
    def walk(q: F, depth: int) -> int:
        counts[q.op] += 1; subtrees.add(q)
        if q.op == 'all': return walk(q.args[1], depth + 1)
        children = [a for a in q.args if isinstance(a, F)]
        return max([depth] + [walk(a, depth) for a in children])
    depth = walk(p, 0)
    return dict(nodes=sum(counts.values()), distinct_subtrees=len(subtrees),
                quantifiers=counts['all'], depth=depth,
                hole_occurrences=counts['hole'], variable_labels=len(all_vars(p)),
                operators=dict(sorted(counts.items())))

def pretty(p: F) -> str:
    if p.op == 'mem': return f'(v{p.args[0]} in v{p.args[1]})'
    if p.op == 'eq': return f'(v{p.args[0]} = v{p.args[1]})'
    if p.op == 'hole': return 'Phi(' + ','.join(f'v{x}' for x in p.args) + ')'
    if p.op == 'not': return '~' + pretty(p.args[0])
    if p.op == 'imp': return '(' + pretty(p.args[0]) + ' -> ' + pretty(p.args[1]) + ')'
    if p.op == 'all': return f'(all v{p.args[0]} ' + pretty(p.args[1]) + ')'
    raise ValueError(p.op)
