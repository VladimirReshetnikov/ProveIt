#!/usr/bin/env python3
"""Finite regression for the three-component EPSC1 interpretation.

This finite rank truncation is NOT a model of EPSC1.  The unbounded
hierarchy and exact-fiber omega closure are proved in epsc1_separation.md.
Only coding, support, permutations, Ext, IR, and one EPSC2 failure are
checked here.  The implementation uses no third-party dependencies.
"""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path
from typing import FrozenSet, Tuple, Union

Base = Tuple[str, int, int]
Node = Tuple[str, FrozenSet["Object"]]
Object = Union[Base, Node]


def base(i: int, s: int) -> Base:
    assert 0 <= i < 3 and s in (0, 1)
    return ("base", i, s)


def is_base(t: Object) -> bool:
    return t[0] == "base"


def members(t: Object) -> FrozenSet[Object]:
    if is_base(t):
        return frozenset((base(t[1], 1 - t[2]),))
    return t[1]


def normalize(xs: FrozenSet[Object]) -> Object:
    if len(xs) == 1:
        t = next(iter(xs))
        if is_base(t):
            return base(t[1], 1 - t[2])
    return ("set", xs)


def support(t: Object) -> FrozenSet[int]:
    if is_base(t):
        return frozenset((t[1],))
    return frozenset().union(*(support(x) for x in members(t)))


def rename(t: Object, perm: Tuple[int, int, int]) -> Object:
    if is_base(t):
        return base(perm[t[1]], t[2])
    return normalize(frozenset(rename(x, perm) for x in members(t)))


def powerset(xs: FrozenSet[Object]):
    values = tuple(xs)
    for bits in itertools.product((False, True), repeat=len(values)):
        yield frozenset(x for x, take in zip(values, bits) if take)


def component(i: int, stages: int) -> FrozenSet[Object]:
    # Eagerly include the common empty node. This merely shifts finite
    # hierarchy indices; the unbounded component is unchanged.
    values = frozenset((base(i, 0), base(i, 1), normalize(frozenset())))
    for _ in range(stages):
        values = values | frozenset(normalize(x) for x in powerset(values))
    return values


def run_stage(stage: int) -> dict:
    comps = [component(i, stage) for i in range(3)]
    universe = frozenset().union(*comps)
    empty = normalize(frozenset())
    assert empty in universe
    assert all(members(t) <= universe for t in universe)
    assert all(len(support(t)) <= 1 for t in universe)

    # Canonical member sets, extensionality, and irreflexivity.
    assert len({members(t) for t in universe}) == len(universe)
    assert all(t not in members(t) for t in universe)
    assert all(normalize(members(t)) == t for t in universe)
    assert all(
        support(t) == frozenset().union(*(support(x) for x in members(t)))
        for t in universe
    )

    subset_comparisons = 0
    subset_pairs = 0
    for y in universe:
        for b in universe:
            subset_comparisons += 1
            if members(y) <= members(b):
                subset_pairs += 1
                assert support(y) <= support(b)

    # Every component permutation is an automorphism of this truncation.
    automorphism_member_checks = 0
    for perm in itertools.permutations(range(3)):
        assert frozenset(rename(t, perm) for t in universe) == universe
        for t in universe:
            assert members(rename(t, perm)) == frozenset(
                rename(x, perm) for x in members(t)
            )
            automorphism_member_checks += 1
        for i in range(3):
            if perm[i] == i:
                assert all(rename(t, perm) == t for t in comps[i])

    # Exact two-parameter EPSC witness. Its local bounds are a and b.
    a, b = base(0, 0), base(1, 0)

    def relation(x: Object, y: Object) -> bool:
        bound = a if not members(x) else b
        return members(y) <= members(bound)

    local_bound_checks = 0
    for x in universe:
        bound = a if not members(x) else b
        for y in universe:
            assert not relation(x, y) or members(y) <= members(bound)
            local_bound_checks += 1

    # No object contains a and b, so closure itself already fails.
    assert not any(a in members(c) and b in members(c) for c in universe)
    closure_counterexamples = 0
    for c in universe:
        # A local, independently checked closure violation for every c.
        # This avoids a needless cubic scan of all triples (c,x,y).
        x, y = (empty, a) if a not in members(c) else (a, b)
        assert not members(x) or x in members(c)
        assert relation(x, y)
        assert y not in members(c)
        closure_counterexamples += 1

    # The finite counterpart of the key orbit obstruction: if x and p
    # belong to component i, its pointwise stabilizer swaps the other two.
    # No bound can contain an off-component y and its image as subsets.
    orbit_bound_checks = 0
    for i in range(3):
        j, k = [v for v in range(3) if v != i]
        perm = tuple(k if v == j else j if v == k else v for v in range(3))
        for y in universe - comps[i]:
            yy = rename(y, perm)
            assert support(y) != support(yy)
            for bound in universe:
                assert not (
                    members(y) <= members(bound)
                    and members(yy) <= members(bound)
                )
                orbit_bound_checks += 1

    # Explicit negative control: the finite truncation FAILS EPSC1 itself.
    # Let r(x,y;p) be Sub(y,p), independent of x. Local boundedness is
    # witnessed by p. Empty activation would force the whole fiber into
    # c. Choose p whose power object lies beyond the truncation.
    if stage == 0:
        p = a
    else:
        p = normalize(component(0, stage - 1))
    assert p in universe
    fiber = frozenset(y for y in universe if members(y) <= members(p))
    assert not any(fiber <= members(c) for c in universe)
    max_member_count = max(map(lambda t: len(members(t)), universe))
    assert len(fiber) > max_member_count

    return {
        "status": "passed",
        "scope": "finite coding regression; NOT a model of EPSC1",
        "components": 3,
        "base_points": 6,
        "hierarchy_successor_steps_after_eager_empty": stage,
        "component_sizes": [len(c) for c in comps],
        "universe_size": len(universe),
        "pure_objects": sum(not support(t) for t in universe),
        "subset_comparisons": subset_comparisons,
        "true_subset_pairs": subset_pairs,
        "automorphism_member_checks": automorphism_member_checks,
        "orbit_bound_checks": orbit_bound_checks,
        "J_local_bound_checks": local_bound_checks,
        "J_closed_hulls": 0,
        "J_explicit_closure_counterexamples": closure_counterexamples,
        "EPSC1_negative_control": {
            "matrix": "Sub(y,p), independent of x",
            "parameter_member_count": len(members(p)),
            "fiber_size": len(fiber),
            "largest_member_set_in_truncation": max_member_count,
            "local_boundedness_witness": "p",
            "hulls": 0,
            "interpretation": "finite truncation is NOT an EPSC1 model",
        },
        "extensionality": True,
        "irreflexivity": True,
        "normalization_roundtrip": True,
        "no_common_container_for_distinct_base_components": True,
    }


def run() -> dict:
    stages = [run_stage(n) for n in range(3)]
    assert [s["universe_size"] for s in stages] == [7, 20, 760]
    assert [s["component_sizes"][0] for s in stages] == [3, 8, 256]
    assert [s["pure_objects"] for s in stages] == [1, 2, 4]
    return {
        "status": "passed",
        "scope": "finite coding regression; NO truncation models EPSC1",
        "stages": stages,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = run()
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")
