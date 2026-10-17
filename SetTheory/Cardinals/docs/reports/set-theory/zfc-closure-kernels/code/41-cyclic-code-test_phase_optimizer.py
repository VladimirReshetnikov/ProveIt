#!/usr/bin/env python3
"""Independent bounded optimality and semantic checks for phase_optimizer.py.

The optimality oracle enumerates native terms directly; it does not use the
optimizer recurrence.  The semantic model is the product of three copies of
the full powerset cylindric algebra on the eight points {0,1}^3.
New implementation, 2026-10-17. MIT-0.
"""
from __future__ import annotations

import argparse
import importlib.util
from itertools import product
import json
from pathlib import Path
import time

import phase_optimizer as opt


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def trees(maximum, unary):
    by_size = [[], [("p",)]]
    for size in range(2, maximum + 1):
        current = [(op, term) for op in unary for term in by_size[size - 1]]
        for left_size in range(1, size - 1):
            right_size = size - 1 - left_size
            current.extend(("j", a, b) for a in by_size[left_size]
                           for b in by_size[right_size])
        by_size.append(current)
    return by_size


def oracle(native, invariant):
    minima = {}
    for size, terms in enumerate(native):
        for term in terms:
            normal = opt.rotation_normal_form(term, invariant=invariant)
            if normal not in minima:
                minima[normal] = size
    return minima


def optimality_check(source, native):
    result = {}
    for invariant in (False, True):
        minima = oracle(native, invariant)
        exact, above_cutoff = 0, 0
        for terms in source:
            for term in terms:
                plan = opt.plan(term, invariant=invariant)
                for phase in range(3):
                    emitted = plan.emit(phase)
                    normal = opt.source_normal_form(term, phase=-phase,
                                                    invariant=invariant)
                    require(opt.rotation_normal_form(emitted, invariant=invariant) == normal,
                            "incorrect reconstructed rotation normal form")
                    require(opt.tree_size(emitted) == plan.costs[phase],
                            "emitted tree cost differs from plan")
                    if plan.costs[phase] < len(native):
                        require(minima.get(normal) == plan.costs[phase],
                                "optimizer disagrees with independent native-term enumeration")
                        exact += 1
                    else:
                        require(normal not in minima,
                                "oracle found a smaller term below the cutoff")
                        above_cutoff += 1
        result["invariant" if invariant else "pure"] = dict(
            exact_cost_comparisons=exact,
            certified_absences_below_native_cutoff=above_cutoff,
            distinct_native_normal_forms=len(minima))
    return result


def model_tables():
    # A world is a three-bit tuple, encoded by its three coordinate bits.
    # Existential cylindrification along axis i adds the bit-flipped neighbor.
    tables = []
    for axis in range(3):
        image = []
        for subset in range(256):
            closure = subset
            for world in range(8):
                if subset & (1 << world):
                    closure |= 1 << (world ^ (1 << axis))
            image.append(closure)
        tables.append(image)
    return tables


TABLES = model_tables()


def evaluate(term, p):
    kind = term[0]
    if kind == "p":
        return p
    if kind == "n":
        return tuple(255 ^ a for a in evaluate(term[1], p))
    if kind == "j":
        return tuple(a | b for a, b in zip(evaluate(term[1], p), evaluate(term[2], p)))
    value = evaluate(term[1], p)
    if kind == "r":
        return value[1], value[2], value[0]
    if kind == "c":
        return tuple(TABLES[i][a] for i, a in enumerate(value))
    raise ValueError("not a native term")


def rotate_value(value, phase):
    phase %= 3
    return value[phase:] + value[:phase]


def semantic_check(source):
    result = {}
    for invariant in (False, True):
        cutoff = 5 if invariant else 4
        terms = [t for group in source[:cutoff + 1] for t in group]
        # The invariant case exhausts all r-fixed generator values of A^3.
        # The pure case exhausts the 8^3 tuples in this stated probe set.
        valuations = [(a, a, a) for a in range(256)] if invariant else list(product(
            (0, 1, 3, 5, 15, 85, 170, 255), repeat=3))
        checks = 0
        for term in terms:
            direct = opt.direct_translate(term)
            plan = opt.plan(term, invariant=invariant)
            emitted = [plan.emit(i) for i in range(3)]
            for valuation in valuations:
                expected = evaluate(direct, valuation)
                for phase in range(3):
                    require(evaluate(emitted[phase], valuation) == rotate_value(expected, -phase),
                            "finite algebra semantic mismatch")
                    checks += 1
        result["invariant" if invariant else "pure"] = dict(
            source_terms=len(terms), source_tree_node_bound=cutoff,
            generator_valuations=len(valuations), phase_comparisons=checks)
    return result


def permutation_check():
    rows = opt.sample_equations()
    result = opt.optimize_equations(rows, permute=True)
    require(len(result["candidates"]) == 6, "not all global modal permutations were considered")
    require(result["cost"] == min(x["cost"] for x in result["candidates"]),
            "global permutation choice is not optimal among its six options")
    for (name, left, right), (new_name, new_left, new_right) in zip(rows, result["equations"]):
        require(name == new_name, "equation row mismatch")
        for source, target in ((left, new_left), (right, new_right)):
            require(opt.rotation_normal_form(target) == opt.source_normal_form(
                source, permutation=result["permutation"]),
                "a side did not use the single selected global permutation")
    return {key: value for key, value in result.items() if key != "equations"}


def reference_check(path, source):
    spec = importlib.util.spec_from_file_location("rotation9_reference", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    count = 0
    for terms in source:
        for term in terms:
            require(module.translate(term) == opt.direct_translate(term),
                    "reference translation convention differs")
            count += 1
    rows = module.df18()
    direct = sum(opt.tree_size(opt.direct_translate(t))
                 for _, left, right in rows for t in (left, right))
    improved = opt.optimize_equations(rows, permute=True)
    # An optional ground axiom must not erase rotations on schema variables.
    for leaf in (module.X, module.Y, module.Z):
        require(opt.plan(leaf, invariant=True).costs == (1, 3, 2),
                "ground invariance was incorrectly promoted to a schema")
    emitted_rows = []
    for (name, left, right), (_, new_left, new_right) in zip(rows, improved["equations"]):
        emitted_rows.append(dict(
            name=name, source=[opt.prefix(left), opt.prefix(right)],
            literal=[opt.prefix(opt.direct_translate(left)),
                     opt.prefix(opt.direct_translate(right))],
            optimized=[opt.prefix(new_left), opt.prefix(new_right)],
            literal_nodes=opt.tree_size(opt.direct_translate(left))
                          + opt.tree_size(opt.direct_translate(right)),
            optimized_nodes=opt.tree_size(new_left) + opt.tree_size(new_right)))
    return dict(reference_translation_comparisons=count,
                df18_literal_translation_nodes=direct,
                df18_optimized_translation_nodes=improved["cost"],
                df18_selected_global_permutation=improved["permutation"],
                df18_emitted_rows=emitted_rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference", type=Path,
                        help="optional independent rotation9.py implementation")
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    started = time.monotonic()
    source = trees(6, ("n", "f", "g", "h"))
    native = trees(9, ("n", "c", "r"))
    report = dict(status="PASS", source_tree_node_bound=6,
                  source_terms=sum(map(len, source)), native_tree_node_bound=9,
                  native_terms=sum(map(len, native)),
                  optimality=optimality_check(source, native),
                  semantic_model="A^3 for A=P({0,1}^3), Boolean bitsets and ordinary "
                                 "existential cylindrifications; r(a,b,c)=(b,c,a)",
                  semantics=semantic_check(source),
                  global_permutation=permutation_check(), examples=opt.report())
    if args.reference:
        report["independent_reference"] = reference_check(args.reference, source)
    report["seconds"] = time.monotonic() - started
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
