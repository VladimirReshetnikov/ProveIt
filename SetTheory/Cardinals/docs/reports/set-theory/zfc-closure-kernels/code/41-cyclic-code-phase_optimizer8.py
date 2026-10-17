#!/usr/bin/env python3
"""Exact six-phase tree optimizer for the root-of-complement E8 signature.

Source: p (or a named atomic leaf), n, j, f/g/h. Native: p, j, c, s.
r=s^2, n=s^3, s=n r^2, s^6=id; even powers of s preserve join.
f=c, g=s^2 c s^4, h=s^4 c s^2.

The optional ground law s^2(p)=p is applied to the literal generator only.
Optimization is exact in the stated phase grammar, not under all E8 laws.
All counts are expanded syntax nodes, not binary Turing-machine states.
New implementation, 2026-10-17. MIT-0.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import permutations

from phase_optimizer import IDENTITY, MODALS, Term, prefix, tree_size


def powers(term: Term, exponent: int) -> Term:
    for _ in range(exponent % 6):
        term = ("s", term)
    return term


def direct_translate(term: Term, permutation=IDENTITY) -> Term:
    if len(term) == 1:
        return term
    children = tuple(direct_translate(child, permutation) for child in term[1:])
    kind = term[0]
    if kind == "n" and len(children) == 1:
        return powers(children[0], 3)
    if kind == "j" and len(children) == 2:
        return ("j", *children)
    if kind in MODALS and len(children) == 1:
        axis = 2 * permutation[MODALS[kind]]
        return powers(("c", powers(children[0], -axis)), axis)
    raise ValueError("not a Df3 source term")


@dataclass(frozen=True)
class Plan:
    term: Term
    children: tuple["Plan", ...]
    costs: tuple[int, ...]
    bases: tuple[int, ...]
    axis: int | None

    def emit(self, phase=0):
        phase %= 6
        if self.term[0] == "n":
            return self.children[0].emit(phase - 3)
        base = self.bases[phase]
        if not self.children:
            body = self.term
        elif self.term[0] == "j":
            body = ("j", self.children[0].emit(base), self.children[1].emit(base))
        else:
            body = ("c", self.children[0].emit(self.axis))
        return powers(body, base - phase)


def plan(term: Term, *, invariant=False, permutation=IDENTITY) -> Plan:
    """D_t[i] is the minimum cost of a representative of s^-i translate(t)."""
    if tuple(sorted(permutation)) != IDENTITY:
        raise ValueError("permutation must be a bijection of (0,1,2)")
    if not isinstance(term, tuple) or not term or not isinstance(term[0], str):
        raise ValueError("source terms must be nonempty immutable prefix tuples")
    kind = term[0]
    children = tuple(plan(child, invariant=invariant, permutation=permutation)
                     for child in term[1:])
    if kind == "n" and len(children) == 1:
        return Plan(term, children, tuple(children[0].costs[(i - 3) % 6]
                                         for i in range(6)), (), None)
    base_costs = [None] * 6
    axis = None
    if not children:
        if kind in {"n", "j", "c", "s", "r", *MODALS}:
            raise ValueError("an operation symbol is missing its argument")
        base_costs[0] = 1
        if invariant and term == ("p",):
            base_costs[2] = base_costs[4] = 1
    elif kind == "j" and len(children) == 2:
        for k in (0, 2, 4):
            base_costs[k] = 1 + children[0].costs[k] + children[1].costs[k]
    elif kind in MODALS and len(children) == 1:
        axis = 2 * permutation[MODALS[kind]]
        base_costs[axis] = 1 + children[0].costs[axis]
    else:
        raise ValueError("not a Df3 source term")
    choices = [min((cost + (k - i) % 6, k)
                   for k, cost in enumerate(base_costs) if cost is not None)
               for i in range(6)]
    return Plan(term, children, tuple(cost for cost, k in choices),
                tuple(k for cost, k in choices), axis)


def optimize(term, *, phase=0, invariant=False, permutation=IDENTITY):
    return plan(term, invariant=invariant, permutation=permutation).emit(phase)


def optimize_equations(equations, *, invariant=False, permute=False):
    rows = tuple(equations)
    options = []
    for permutation in permutations(IDENTITY) if permute else (IDENTITY,):
        cost, output = 0, []
        for name, left, right in rows:
            lp = plan(left, invariant=invariant, permutation=permutation)
            rp = plan(right, invariant=invariant, permutation=permutation)
            cost += lp.costs[0] + rp.costs[0]
            output.append((name, lp.emit(), rp.emit()))
        options.append((cost, permutation, tuple(output)))
    cost, permutation, output = min(options, key=lambda row: (row[0], row[1]))
    direct = sum(tree_size(direct_translate(t, permutation))
                 for _, left, right in rows for t in (left, right))
    return dict(cost=cost, permutation=permutation, equations=output,
                direct_cost_for_selected_permutation=direct,
                candidates=[dict(cost=row[0], permutation=row[1]) for row in options])


def negate_normal(term):
    return term[1] if term[0] == "n" else ("n", term)


def normal_form(term, *, rotation=0, complement=False, invariant=False):
    """Independent native canonical form for the phase grammar.

    Expand an outer s as complement times r^2. Distribute only r through
    ordered Boolean nodes, cancel double complements, and retain complement
    in front of a join or c-node. No De Morgan or modal identity is used.
    """
    rotation %= 3
    kind = term[0]
    if len(term) == 1:
        result = ("atom", kind, 0 if invariant and term == ("p",) else rotation)
    elif kind == "s":
        return normal_form(term[1], rotation=rotation + 2,
                           complement=not complement, invariant=invariant)
    else:
        children = tuple(normal_form(child, rotation=rotation, invariant=invariant)
                         for child in term[1:])
        if kind == "c" and len(children) == 1:
            result = ("modal", rotation, children[0])
        elif kind == "j" and len(children) == 2:
            result = ("j", *children)
        else:
            raise ValueError("not a native E8 term")
    return negate_normal(result) if complement else result


def source_normal_form(term, *, rotation=0, complement=False,
                       invariant=False, permutation=IDENTITY):
    rotation %= 3
    kind = term[0]
    if len(term) == 1:
        result = ("atom", kind, 0 if invariant and term == ("p",) else rotation)
    elif kind == "n":
        return source_normal_form(term[1], rotation=rotation, complement=not complement,
                                  invariant=invariant, permutation=permutation)
    else:
        children = tuple(source_normal_form(child, rotation=rotation, invariant=invariant,
                                            permutation=permutation) for child in term[1:])
        if kind in MODALS:
            result = ("modal", (permutation[MODALS[kind]] + rotation) % 3, children[0])
        elif kind == "j" and len(children) == 2:
            result = ("j", *children)
        else:
            raise ValueError("not a Df3 source term")
    return negate_normal(result) if complement else result


def expected_normal_form(term, phase=0, invariant=False, permutation=IDENTITY):
    # s^-i = complement^(i mod 2) times r^(-2i).
    return source_normal_form(term, rotation=-2 * phase, complement=bool(phase % 2),
                              invariant=invariant, permutation=permutation)
