#!/usr/bin/env python3
"""Exact three-phase tree optimizer for the cyclic presentation of Df3.

Source terms: p (or a named atomic leaf), n, j, and f/g/h.
Native terms: the same atoms, n, j, c, and r.  Composition acts rightmost first.
f = c, g = r c r^2, h = r^2 c r; r^3 = identity; r preserves n and j.

Pure E9 is the default.  invariant=True additionally uses the GROUND equation
r(p)=p, not a schema for arbitrary terms.  No Boolean or modal identities
other than rotation distribution/cancellation are used in optimization.

Costs count all tree nodes, including repeated subtrees and atomic leaves.
This is a target-term compiler component, not a binary Turing machine.
New implementation, 2026-10-17. MIT-0.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import permutations


MODALS = {"f": 0, "g": 1, "h": 2}
IDENTITY = (0, 1, 2)
Term = tuple


def tree_size(term: Term) -> int:
    return 1 + sum(tree_size(child) for child in term[1:])


def prefix(term: Term) -> str:
    return term[0] + "".join(prefix(child) for child in term[1:])


def rotations(term: Term, exponent: int) -> Term:
    for _ in range(exponent % 3):
        term = ("r", term)
    return term


def direct_translate(term: Term, permutation=IDENTITY) -> Term:
    """Literal conjugation translation, without even adjacent r^3 removal."""
    kind = term[0]
    if len(term) == 1:
        return term
    children = tuple(direct_translate(child, permutation) for child in term[1:])
    if kind in MODALS:
        axis = permutation[MODALS[kind]]
        return rotations(("c", rotations(children[0], -axis)), axis)
    if (kind == "n" and len(children) == 1) or (kind == "j" and len(children) == 2):
        return (kind, *children)
    raise ValueError(f"not a source term: {term!r}")


@dataclass(frozen=True)
class Plan:
    term: Term
    children: tuple["Plan", ...]
    costs: tuple[int, int, int]
    # For target phase i, bases[i] is the selected zero-leading-r phase k.
    bases: tuple[int, int, int]
    axis: int | None
    invariant: bool

    def emit(self, phase: int = 0) -> Term:
        """Return an optimal representative of r^(-phase) translate(term)."""
        phase %= 3
        base = self.bases[phase]
        kind = self.term[0]
        if not self.children:
            body = self.term
        elif kind == "n":
            body = ("n", self.children[0].emit(base))
        elif kind == "j":
            body = ("j", self.children[0].emit(base), self.children[1].emit(base))
        else:
            body = ("c", self.children[0].emit(self.axis))
        return rotations(body, base - phase)


def plan(term: Term, *, invariant=False, permutation=IDENTITY) -> Plan:
    """Three costs per occurrence, hence linear time in the source tree.

    Exact recurrence (infinity means no zero-leading-r representative):
      B_atom[0]=1; additionally B_p[1]=B_p[2]=1 if r(p)=p is assumed.
      B_not[k]=1+D_child[k].
      B_join[k]=1+D_left[k]+D_right[k].
      B_c_j[j]=1+D_child[j]; its other entries are infinity.
      D[i]=min_k ((k-i) mod 3) + B[k].
    """
    if tuple(sorted(permutation)) != IDENTITY:
        raise ValueError("permutation must be a bijection of (0,1,2)")
    if not isinstance(term, tuple) or not term or not isinstance(term[0], str):
        raise ValueError("source terms must be nonempty immutable prefix tuples")
    kind = term[0]
    children = tuple(plan(child, invariant=invariant, permutation=permutation)
                     for child in term[1:])
    base_costs = [None, None, None]
    axis = None
    if not children:
        if kind in {"n", "j", "c", "r", *MODALS}:
            raise ValueError("an operation symbol is missing its argument")
        base_costs[0] = 1
        if invariant and term == ("p",):
            base_costs[:] = [1, 1, 1]
    elif kind == "n" and len(children) == 1:
        base_costs = [1 + children[0].costs[k] for k in range(3)]
    elif kind == "j" and len(children) == 2:
        base_costs = [1 + children[0].costs[k] + children[1].costs[k] for k in range(3)]
    elif kind in MODALS and len(children) == 1:
        axis = permutation[MODALS[kind]]
        base_costs[axis] = 1 + children[0].costs[axis]
    else:
        raise ValueError(f"not a source term: {term!r}")
    choices = [min((cost + (k - i) % 3, k)
                   for k, cost in enumerate(base_costs) if cost is not None)
               for i in range(3)]
    return Plan(term, children, tuple(cost for cost, k in choices),
                tuple(k for cost, k in choices), axis, invariant)


def optimize(term: Term, *, phase=0, invariant=False, permutation=IDENTITY) -> Term:
    return plan(term, invariant=invariant, permutation=permutation).emit(phase)


def optimize_equations(equations, *, invariant=False, permute=False):
    """Choose ONE global modal renaming for all rows and both equation sides.

    Modal renaming uses the symmetry of the entire Df3 presentation; the
    emitted terms represent the renamed equations.  It does not assert that
    an arbitrary term equals its modal renaming in a fixed algebra.
    """
    rows = tuple(equations)
    options = []
    for permutation in permutations(IDENTITY) if permute else (IDENTITY,):
        output, cost = [], 0
        for name, left, right in rows:
            lp = plan(left, invariant=invariant, permutation=permutation)
            rp = plan(right, invariant=invariant, permutation=permutation)
            cost += lp.costs[0] + rp.costs[0]
            output.append((name, lp.emit(), rp.emit()))
        options.append((cost, permutation, tuple(output)))
    cost, permutation, output = min(options, key=lambda item: (item[0], item[1]))
    direct_cost = sum(tree_size(direct_translate(t, permutation))
                      for _, left, right in rows for t in (left, right))
    return dict(cost=cost, permutation=permutation, equations=output,
                direct_cost_for_selected_permutation=direct_cost,
                candidates=[dict(cost=x[0], permutation=x[1]) for x in options])


def rotation_normal_form(term: Term, *, phase=0, invariant=False) -> Term:
    """Independent free-structure canonical form of a NATIVE term.

    Push all rotations inward.  A c encountered under r^k becomes modal c_k;
    an atomic leaf records the residual rotation.  Ordered Boolean tree
    structure is retained exactly; this applies no Boolean simplification.
    """
    kind = term[0]
    phase %= 3
    if len(term) == 1:
        return ("atom", kind, 0 if invariant and term == ("p",) else phase)
    if kind == "r":
        return rotation_normal_form(term[1], phase=phase + 1, invariant=invariant)
    children = tuple(rotation_normal_form(child, phase=phase, invariant=invariant)
                     for child in term[1:])
    if kind == "c" and len(children) == 1:
        return ("modal", phase, children[0])
    if (kind == "n" and len(children) == 1) or (kind == "j" and len(children) == 2):
        return (kind, *children)
    raise ValueError("not a native term")


def source_normal_form(term: Term, *, phase=0, invariant=False,
                       permutation=IDENTITY) -> Term:
    """Canonical form of r^phase translate(term), without translating first."""
    kind = term[0]
    phase %= 3
    if len(term) == 1:
        return ("atom", kind, 0 if invariant and term == ("p",) else phase)
    children = tuple(source_normal_form(child, phase=phase, invariant=invariant,
                                       permutation=permutation) for child in term[1:])
    if kind in MODALS:
        return ("modal", (permutation[MODALS[kind]] + phase) % 3, children[0])
    return (kind, *children)


def sample_equations():
    p = ("p",)
    h8 = p
    for _ in range(8):
        h8 = ("h", h8)
    branch = ("j", ("g", ("n", ("g", p))), ("g", ("j", p, ("g", p))))
    mixed = ("h", ("j", ("g", ("n", ("h", p))),
                         ("h", ("j", ("f", p), ("g", p)))))
    return (("repeated_h8", h8, p), ("shared_boolean_phase", branch, ("n", p)),
            ("mixed_modal_tree", mixed, ("f", ("n", p))))


def report():
    rows = sample_equations()
    result = {"unit": "expanded syntax-tree nodes; NOT Turing-machine states",
              "exactness_scope": "Rotation distribution, r^3 cancellation, and optionally "
                                  "the literal ground equation r(p)=p only",
              "samples": []}
    for name, left, right in rows:
        direct = direct_translate(left)
        pure = optimize(left)
        invariant = optimize(left, invariant=True)
        result["samples"].append(dict(
            name=name, source=prefix(left), source_nodes=tree_size(left),
            direct=prefix(direct), direct_nodes=tree_size(direct),
            pure=prefix(pure), pure_nodes=tree_size(pure),
            invariant=prefix(invariant), invariant_nodes=tree_size(invariant)))
    result["joint_global_permutation_example"] = {
        key: value for key, value in optimize_equations(rows, permute=True).items()
        if key != "equations"}
    return result


if __name__ == "__main__":
    import json
    print(json.dumps(report(), indent=2))
