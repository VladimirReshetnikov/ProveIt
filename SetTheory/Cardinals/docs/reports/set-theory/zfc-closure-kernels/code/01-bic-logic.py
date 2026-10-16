"""Small formula utilities for the report's logical experiments.

These utilities do not implement a proof assistant or a ZFC proof checker.
Variables are nonnegative integers; equality has a configurable interpretation.
Only classical negation, implication, and universal quantification are primitive.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Callable, Mapping

@dataclass(frozen=True)
class Formula:
    op: str
    args: tuple


def E(x: int, y: int) -> Formula:
    return Formula('E', (x, y))

def Eq(x: int, y: int) -> Formula:
    return Formula('=', (x, y))

def Hole(x: int, y: int) -> Formula:
    return Formula('phi', (x, y))

def Not(p: Formula) -> Formula:
    return Formula('not', (p,))

def Imp(p: Formula, q: Formula) -> Formula:
    return Formula('imp', (p, q))

def All(x: int, p: Formula) -> Formula:
    return Formula('all', (x, p))

def Ex(x: int, p: Formula) -> Formula:
    return Not(All(x, Not(p)))

def And(p: Formula, q: Formula) -> Formula:
    return Not(Imp(p, Not(q)))

def Iff(p: Formula, q: Formula) -> Formula:
    return And(Imp(p, q), Imp(q, p))

def all_many(xs: list[int], p: Formula) -> Formula:
    for x in reversed(xs):
        p = All(x, p)
    return p

def variables(p: Formula) -> set[int]:
    if p.op in ('E', '=', 'phi'):
        return set(p.args)
    if p.op == 'all':
        return {p.args[0]} | variables(p.args[1])
    return set().union(*(variables(q) for q in p.args))

def free_variables(p: Formula) -> set[int]:
    if p.op in ('E', '=', 'phi'):
        return set(p.args)
    if p.op == 'all':
        return free_variables(p.args[1]) - {p.args[0]}
    return set().union(*(free_variables(q) for q in p.args))

def fresh(p: Formula, extra: set[int] | None = None) -> int:
    return 1 + max(variables(p) | (extra or set()) | {-1})

def substitute(p: Formula, x: int, y: int) -> Formula:
    """Capture-avoiding substitution of variable y for free occurrences of x."""
    if x == y:
        return p
    if p.op in ('E', '=', 'phi'):
        return Formula(p.op, tuple(y if a == x else a for a in p.args))
    if p.op == 'all':
        z, body = p.args
        if z == x or x not in free_variables(body):
            return p
        if z == y:
            new = fresh(p, {x, y})
            body = substitute(body, z, new)
            z = new
        return All(z, substitute(body, x, y))
    return Formula(p.op, tuple(substitute(q, x, y) for q in p.args))

def alpha_key(p: Formula, bound: tuple[int, ...] = ()) -> tuple:
    def var_key(x: int) -> tuple:
        return ('bound', bound.index(x)) if x in bound else ('free', x)
    if p.op in ('E', '=', 'phi'):
        return (p.op,) + tuple(var_key(x) for x in p.args)
    if p.op == 'all':
        x, q = p.args
        return ('all', alpha_key(q, (x,) + bound))
    return (p.op,) + tuple(alpha_key(q, bound) for q in p.args)

def incoming(x: int, y: int, z: int) -> Formula:
    assert z not in (x, y)
    return All(z, Iff(E(z, x), E(z, y)))

def profile(x: int, y: int, z: int) -> Formula:
    assert z not in (x, y)
    return And(incoming(x, y, z), All(z, Iff(E(x, z), E(y, z))))

def erase_equality(p: Formula, mode: str = 'incoming') -> Formula:
    """Replace = by I or D, using a variable absent from the entire input."""
    if mode not in ('incoming', 'profile'):
        raise ValueError('mode must be incoming or profile')
    z = fresh(p)
    replacement = incoming if mode == 'incoming' else profile
    def walk(q: Formula) -> Formula:
        if q.op == '=':
            return replacement(*q.args, z)
        if q.op in ('E', 'phi'):
            return q
        if q.op == 'all':
            return All(q.args[0], walk(q.args[1]))
        return Formula(q.op, tuple(walk(r) for r in q.args))
    return walk(p)

def evaluate(p: Formula, n: int, mem: Callable[[int, int], bool],
             env: Mapping[int, int] | None = None,
             eq: Callable[[int, int], bool] | None = None,
             phi: Callable[[int, int], bool] | None = None) -> bool:
    if n < 1:
        raise ValueError('first-order domains must be nonempty')
    val = dict(env or {})
    equality = eq or (lambda a, b: a == b)
    if p.op in ('E', '=', 'phi'):
        x, y = (val[i] for i in p.args)
        relation = mem if p.op == 'E' else equality if p.op == '=' else phi
        if relation is None:
            raise ValueError('phi interpretation required')
        return bool(relation(x, y))
    if p.op == 'not':
        return not evaluate(p.args[0], n, mem, val, equality, phi)
    if p.op == 'imp':
        return (not evaluate(p.args[0], n, mem, val, equality, phi)
                or evaluate(p.args[1], n, mem, val, equality, phi))
    if p.op == 'all':
        x, q = p.args
        return all(evaluate(q, n, mem, {**val, x: a}, equality, phi)
                   for a in range(n))
    raise ValueError(f'unknown constructor {p.op}')

def metrics(p: Formula) -> dict:
    seen: set[Formula] = set()
    counts = {'tree_nodes': 0, 'atom_occurrences': 0,
              'variable_occurrences': 0, 'quantifiers': 0}
    def walk(q: Formula) -> None:
        seen.add(q)
        counts['tree_nodes'] += 1
        if q.op in ('E', '=', 'phi'):
            counts['atom_occurrences'] += 1
            counts['variable_occurrences'] += 2
        elif q.op == 'all':
            counts['quantifiers'] += 1
            walk(q.args[1])
        else:
            for r in q.args:
                walk(r)
    walk(p)
    return {**counts, 'distinct_subtrees': len(seen),
            'max_variable_index': max(variables(p), default=-1)}

def templates() -> dict[str, Formula]:
    # Variables in these templates are deliberately fixed and documented.
    # CP: p=0,V=1,x=2,W=3,z=4,t=5.
    sub = lambda x, y: All(5, Imp(E(5, x), E(5, y)))
    cp = All(0, Ex(1, And(E(0, 1), All(2, Imp(E(2, 1),
         And(sub(2, 1), Ex(3, And(E(3, 1),
             All(4, Imp(sub(4, 2), E(4, 3)))))))))))
    ext = all_many([0, 1], Imp(incoming(0, 1, 2), Eq(0, 1)))
    cg = all_many([0, 1], Imp(incoming(0, 1, 2),
                            All(2, Imp(E(0, 2), E(1, 2)))))
    # GIC: B=0,C=1,a=2,y=3,y'=4,x=2.
    gic = All(0, Ex(1, And(
        All(2, Imp(E(2, 0), All(3, Imp(Hole(2, 3),
            Ex(4, And(Hole(2, 4), E(4, 1))))))),
        All(3, Imp(E(3, 1), Ex(2, Hole(2, 3)))))))
    # PFI: A=0,B=1,u=2,y=3,z=4.
    pfi = All(0, Imp(All(2, Imp(E(2, 0), all_many([3, 4],
        Imp(And(Hole(2, 3), Hole(2, 4)), Eq(3, 4))))),
        Ex(1, All(3, Iff(E(3, 1), Ex(2, And(E(2, 0), Hole(2, 3))))))))
    return {'CP': cp, 'Ext': ext, 'CG': cg, 'GIC': gic, 'PFI': pfi,
            'PFI_I': erase_equality(pfi),
            'IR': All(0, Not(E(0, 0)))}
