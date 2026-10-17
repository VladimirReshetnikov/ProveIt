#!/usr/bin/env python3
"""Independent bounded optimality and algebra checks for the six-phase compiler.
New implementation, 2026-10-17. MIT-0.
"""
from __future__ import annotations

import argparse
from itertools import product
import json
from pathlib import Path
import time

import phase_optimizer as three
import phase_optimizer8 as six
from test_phase_optimizer import TABLES, require, trees


def evaluate(term, p):
    kind = term[0]
    if kind == "p":
        return p
    if kind == "j":
        return tuple(a | b for a, b in zip(evaluate(term[1], p), evaluate(term[2], p)))
    value = evaluate(term[1], p)
    if kind == "s":
        return 255 ^ value[2], 255 ^ value[0], 255 ^ value[1]
    if kind == "c":
        return tuple(TABLES[i][a] for i, a in enumerate(value))
    raise ValueError("not a native E8 term")


def s_value(value, exponent):
    for _ in range(exponent % 6):
        value = 255 ^ value[2], 255 ^ value[0], 255 ^ value[1]
    return value


def oracle_check(source, native):
    report = {}
    for invariant in (False, True):
        minima = {}
        for size, terms in enumerate(native):
            for term in terms:
                normal = six.normal_form(term, invariant=invariant)
                if normal not in minima:
                    minima[normal] = size
        exact, above = 0, 0
        for terms in source:
            for term in terms:
                plan = six.plan(term, invariant=invariant)
                for phase in range(6):
                    emitted = plan.emit(phase)
                    expected = six.expected_normal_form(term, phase, invariant)
                    require(six.normal_form(emitted, invariant=invariant) == expected,
                            "six-phase emitted normal form differs")
                    require(three.tree_size(emitted) == plan.costs[phase],
                            "six-phase emitted cost differs")
                    if plan.costs[phase] < len(native):
                        require(minima.get(expected) == plan.costs[phase],
                                "six-phase cost is not native-enumeration minimum")
                        exact += 1
                    else:
                        require(expected not in minima,
                                "native enumeration found a smaller term below cutoff")
                        above += 1
        report["invariant" if invariant else "pure"] = dict(
            exact_cost_comparisons=exact, absences_below_cutoff=above,
            distinct_native_normal_forms=len(minima))
    return report


def semantics(source):
    report = {}
    for invariant in (False, True):
        cutoff = 5 if invariant else 4
        terms = [term for level in source[:cutoff + 1] for term in level]
        valuations = [(a, a, a) for a in range(256)] if invariant else list(product(
            (0, 1, 3, 5, 15, 85, 170, 255), repeat=3))
        checks = 0
        for term in terms:
            direct = six.direct_translate(term)
            plan = six.plan(term, invariant=invariant)
            emitted = [plan.emit(i) for i in range(6)]
            for valuation in valuations:
                expected = evaluate(direct, valuation)
                for phase in range(6):
                    require(evaluate(emitted[phase], valuation) == s_value(expected, -phase),
                            "six-phase finite algebra semantic mismatch")
                    checks += 1
        report["invariant" if invariant else "pure"] = dict(
            source_terms=len(terms), source_tree_node_bound=cutoff,
            generator_valuations=len(valuations), phase_comparisons=checks)
    return report


def examples():
    rows = three.sample_equations()
    samples = []
    for name, left, right in rows:
        direct = six.direct_translate(left)
        pure, invariant = six.optimize(left), six.optimize(left, invariant=True)
        samples.append(dict(name=name, source=three.prefix(left),
                            source_nodes=three.tree_size(left),
                            literal=three.prefix(direct), literal_nodes=three.tree_size(direct),
                            pure=three.prefix(pure), pure_nodes=three.tree_size(pure),
                            invariant=three.prefix(invariant),
                            invariant_nodes=three.tree_size(invariant)))
    global_result = six.optimize_equations(rows, permute=True)
    for (name, left, right), (_, new_left, new_right) in zip(rows, global_result["equations"]):
        for source, native in ((left, new_left), (right, new_right)):
            require(six.normal_form(native) == six.expected_normal_form(
                source, permutation=global_result["permutation"]),
                "joint global permutation changed inconsistently")
    # Invariance of p must not leak into substitution variables.
    for variable in ("x", "y", "z"):
        require(six.plan((variable,), invariant=True).costs == (1, 6, 5, 4, 3, 2),
                "ground invariant equation was treated as a schema")
    return dict(unit="expanded syntax-tree nodes; NOT Turing-machine states",
                samples=samples, joint_global_permutation={
                    key: value for key, value in global_result.items() if key != "equations"})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    started = time.monotonic()
    source = trees(6, ("n", "f", "g", "h"))
    native = trees(11, ("c", "s"))
    report = dict(status="PASS", source_tree_node_bound=6,
                  source_terms=sum(map(len, source)), native_tree_node_bound=11,
                  native_terms=sum(map(len, native)),
                  optimality=oracle_check(source, native),
                  semantic_model="A^3, A=P({0,1}^3), s(a,b,c)=(~c,~a,~b)",
                  semantics=semantics(source), examples=examples())
    report["seconds"] = time.monotonic() - started
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
