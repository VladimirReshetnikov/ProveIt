#!/usr/bin/env python3
"""Finite diagnostics for the two-atom orbit model.

The all-ranks theorem is mathematical. This program checks the first
two closure levels and all invariant unary truth assignments on D1 for
sources in D1, with output witnesses in D2. D2 is not asserted to model
the whole infinite schema. No external packages or input files required.
"""
from __future__ import annotations

import itertools
import json
from pathlib import Path
from typing import Union

Atom = tuple[str, int]
Obj = Union[Atom, frozenset]
E0: Atom = ("atom", 0)
E1: Atom = ("atom", 1)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def members(obj: Obj) -> frozenset:
    return obj if isinstance(obj, frozenset) else frozenset()


def swap(obj: Obj) -> Obj:
    if isinstance(obj, tuple):
        return ("atom", 1 - obj[1])
    return frozenset(swap(member) for member in obj)


def serial(obj: Obj):
    if isinstance(obj, tuple):
        return ["atom", obj[1]]
    return ["set", sorted((serial(member) for member in obj), key=repr)]


def ordered(objects):
    return sorted(objects, key=lambda x: repr(serial(x)))


def orbits(objects):
    remaining = set(objects)
    result = []
    while remaining:
        first = ordered(remaining)[0]
        orbit = frozenset((first, swap(first)))
        require(orbit <= remaining, "level not invariant or malformed orbit")
        remaining.difference_update(orbit)
        result.append(orbit)
    return result


C0 = frozenset((E0,))
C1 = frozenset((E1,))
SEEDS = frozenset((E0, E1, C0, C1))


def next_level(level):
    blocks = orbits(level)
    result = set(SEEDS)
    for choices in itertools.product((False, True), repeat=len(blocks)):
        selected = frozenset(
            element
            for chosen, block in zip(choices, blocks)
            if chosen
            for element in block
        )
        if selected:
            result.add(selected)
    return frozenset(result)


def main():
    d0 = SEEDS
    d1 = next_level(d0)
    d2 = next_level(d1)
    require([len(d0), len(d1), len(d2)] == [4, 7, 35],
            "unexpected level cardinalities")
    require(d0 <= d1 <= d2, "levels not increasing")
    require(all(swap(swap(obj)) == obj for obj in d2), "swap not involutive")
    require(all(members(obj) <= d2 for obj in d2), "D2 not hereditary")
    for x in d2:
        for a in d2:
            require((x in members(a)) == (swap(x) in members(swap(a))),
                    "swap not a membership automorphism")
    for source in d1:
        represented = frozenset(
            x for x in d2 if members(x) <= members(source)
        )
        require(represented <= d1, "supported object lies outside D1")

    truth_orbits = orbits(d1)
    require(len(truth_orbits) == 5, "expected five D1 orbits")
    witness_cases = 0
    implication_checks = 0
    nonexact_witness_cases = 0
    for bits in itertools.product((False, True), repeat=len(truth_orbits)):
        truth = frozenset(
            x for chosen, block in zip(bits, truth_orbits) if chosen for x in block
        )
        require(frozenset(swap(x) for x in truth) == truth,
                "truth assignment is not invariant")
        for source in d1:
            selected = frozenset(
                x for x in d2 if members(x) <= members(source) and x in truth
            )
            orbit_closure = selected | frozenset(swap(x) for x in selected)
            witness = orbit_closure if orbit_closure else E0
            require(witness in d2, "witness absent from D2")
            for x in d2:
                require(x not in members(witness) or x in truth,
                        "upper filter clause fails")
                require(not (members(x) <= members(source) and x in truth)
                        or x in members(witness), "lower filter clause fails")
                implication_checks += 2
            witness_cases += 1
            nonexact_witness_cases += bool(orbit_closure - selected)

    require({x for x in d2 if members(x) == members(C0)} == {C0},
            "c0's member profile should be unique")
    absent_singleton = frozenset((C0,))
    absent_exact_power = frozenset((E0, E1, C0))
    require(absent_singleton not in d2, "forbidden singleton present")
    require(absent_exact_power not in d2, "forbidden exact power present")
    require(swap(absent_singleton) != absent_singleton, "singleton invariant")
    require(swap(absent_exact_power) != absent_exact_power, "power invariant")
    require(absent_singleton not in SEEDS and absent_exact_power not in SEEDS,
            "forbidden output accidentally a seed")
    require({x for x in d2 if members(x) <= members(C0)}
            == set(absent_exact_power), "incorrect represented-subset list")

    result = {
        "status": "passed",
        "scope": (
            "Finite construction diagnostics only; D2 is not a model of "
            "the entire schema. The all-ranks orbit argument is in the paper."
        ),
        "level_sizes": [len(d0), len(d1), len(d2)],
        "D1_orbits": len(truth_orbits),
        "invariant_truth_assignments": 2 ** len(truth_orbits),
        "source_witness_cases": witness_cases,
        "upper_and_lower_implication_checks": implication_checks,
        "cases_with_intentionally_extra_output_members": nonexact_witness_cases,
        "membership_automorphism_checks": len(d2) ** 2,
        "forbidden_singleton": serial(absent_singleton),
        "forbidden_exact_power": serial(absent_exact_power),
        "all_ranks_exclusion_basis": "nonseed and not fixed by swap",
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

