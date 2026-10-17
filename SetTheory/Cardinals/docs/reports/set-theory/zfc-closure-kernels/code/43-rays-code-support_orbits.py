#!/usr/bin/env python3
"""Finite checks for the support argument in the accompanying paper.

These checks do NOT construct a finite model of EPSC1.  The actual model is
a proper class interpretation (or its interpretation inside a model of ZFC).
The finite orbit calculation is the combinatorial step in that proof.
Python 3.10 or later; standard library only.
"""
from __future__ import annotations

import argparse
import itertools
import json
from dataclasses import dataclass
from pathlib import Path


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def subsets(items, maximum=None):
    items = tuple(items)
    maximum = len(items) if maximum is None else min(maximum, len(items))
    for size in range(maximum + 1):
        for choice in itertools.combinations(items, size):
            yield frozenset(choice)


def orbit_check(maximum_capacity=3):
    """Check all support sets, using the exact stabilizer orbit description.

    If A is fixed pointwise, the orbit of B consists of B intersect A together
    with every subset of I minus A of size |B minus A|.  We independently
    check this description using literal permutations for capacity one.
    """
    rows = []
    for capacity in range(1, maximum_capacity + 1):
        indices = frozenset(range(2 * capacity + 1))
        small = tuple(subsets(indices, capacity))
        pairs = leaking = contradictions = permutations_checked = 0
        for fixed in small:
            free = indices - fixed
            for output in small:
                pairs += 1
                inside = output & fixed
                outside_size = len(output - fixed)
                orbit = {inside | s for s in subsets(free, outside_size)
                         if len(s) == outside_size}
                actual_union = frozenset().union(*orbit)
                expected_union = inside | (free if outside_size else frozenset())
                require(actual_union == expected_union, "Incorrect orbit union")
                if capacity == 1:
                    literal = set()
                    for perm in itertools.permutations(sorted(free)):
                        mapping = dict(zip(sorted(free), perm))
                        mapping.update({i: i for i in fixed})
                        literal.add(frozenset(mapping[i] for i in output))
                        permutations_checked += 1
                    require(literal == orbit, "Stabilizer orbit mismatch")
                if not output <= fixed:
                    leaking += 1
                    require(len(actual_union) > capacity,
                            "A fresh component escaped the support bound")
                    for bound in small:
                        require(not actual_union <= bound,
                                "A bounded support contains the whole fresh orbit")
                        contradictions += 1
        rows.append(dict(capacity=capacity, components=len(indices),
                         support_pairs=pairs, leaking_pairs=leaking,
                         impossible_bound_checks=contradictions,
                         literal_permutations=permutations_checked))
    return rows


@dataclass(frozen=True)
class Atom:
    component: int
    level: int


@dataclass(frozen=True)
class SetCode:
    elements: frozenset


def support(obj):
    if isinstance(obj, Atom):
        return frozenset((obj.component,))
    return frozenset().union(*(support(x) for x in obj.elements))


def members(obj):
    if isinstance(obj, Atom):
        return frozenset((Atom(obj.component, obj.level + 1),))
    return obj.elements


class SupportOverflow(ValueError):
    pass


def make_set(elements, capacity=1):
    """Normalize atom singletons; reject unions with excessive support."""
    elements = frozenset(elements)
    used = frozenset().union(*(support(x) for x in elements))
    if len(used) > capacity:
        raise SupportOverflow(f"Support {sorted(used)} exceeds {capacity}")
    if len(elements) == 1:
        x = next(iter(elements))
        if isinstance(x, Atom):
            return Atom(x.component, x.level - 1)
    return SetCode(elements)


def permute(obj, permutation):
    if isinstance(obj, Atom):
        return Atom(permutation[obj.component], obj.level)
    return make_set(permute(x, permutation) for x in obj.elements)


def finite_examples():
    empty = make_set(())
    atoms = tuple(Atom(i, n) for i in range(3) for n in range(-2, 3))
    sample = {empty, *atoms}
    for atom in atoms:
        sample.add(make_set((empty, atom)))
        sample.add(make_set((make_set((empty, atom)),)))
    sample.add(make_set((empty,)))
    sample.add(make_set((empty, make_set((empty,)))))
    sample = tuple(sample)
    extensional_pairs = automorphism_checks = support_checks = 0
    for x in sample:
        require(support(x) == frozenset().union(*(support(y) for y in members(x))),
                "Support is not the union of member supports")
        require(make_set(members(x)) == x, "Extension normalization failed")
        for y in sample:
            extensional_pairs += 1
            require((members(x) == members(y)) == (x == y),
                    "Extensionality failed on examples")
            if members(x) <= members(y):
                support_checks += 1
                require(support(x) <= support(y), "Subset support monotonicity failed")
        for permutation in itertools.permutations(range(3)):
            automorphism_checks += 1
            require(members(permute(x, permutation)) ==
                    frozenset(permute(y, permutation) for y in members(x)),
                    "Permutation does not preserve membership")
        union = make_set(z for y in members(x) for z in members(y))
        require(members(union) == frozenset(z for y in members(x) for z in members(y)),
                "Union failed")
        power = make_set(make_set(s) for s in subsets(members(x)))
        require(members(power) == frozenset(make_set(s) for s in subsets(members(x))),
                "Power set failed")
        frontier = {x}
        for depth in range(1, 9):
            frontier = {z for y in frontier for z in members(y)}
            require(x not in frontier, f"A cycle of length {depth} was found")
    failures = 0
    for i, j in itertools.permutations(range(3), 2):
        try:
            make_set((Atom(i, 0), Atom(j, 0)))
        except SupportOverflow:
            failures += 1
        else:
            raise AssertionError("Cross-component pair was admitted")
    return dict(sample_objects=len(sample), extensional_pairs=extensional_pairs,
                automorphism_checks=automorphism_checks,
                subset_support_checks=support_checks,
                rejected_cross_component_pairs=failures,
                cycle_lengths_checked=list(range(1, 9)),
                warning="Finite examples only; not a finite EPSC1 model.")


def two_parameter_obstruction():
    """A finite trace of the explicit impossible EPSC2 hull.

    rho(x,y;a,b) = (Empty(x) and y=a) or (x=a and y=b).
    a is nonempty, so its fibers have size at most one.  A hull from Empty
    must first contain a and then b, contradicting the one-support restriction.
    """
    empty, a, b = make_set(()), Atom(0, 0), Atom(1, 0)
    def fiber(x):
        if not members(x):
            return frozenset((a,))
        if x == a:
            return frozenset((b,))
        return frozenset()
    require(fiber(empty) == {a}, "Empty seed failed")
    require(fiber(a) == {b}, "Recurrent closure failed")
    require(members(a) <= members(a) and members(b) <= members(b),
            "Singleton fibers are not subset bounded")
    try:
        make_set(fiber(empty) | fiber(a))
    except SupportOverflow:
        return dict(initial_output="a[0,0]", recurrent_output="a[1,0]",
                    fiber_cardinality_bound=1, required_components=2,
                    permitted_components=1, contradiction=True)
    raise AssertionError("An impossible two-component hull was accepted")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = dict(status="passed", scope="finite combinatorial diagnostics",
                  orbit_checks=orbit_check(), examples=finite_examples(),
                  epsc2_obstruction=two_parameter_obstruction())
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
