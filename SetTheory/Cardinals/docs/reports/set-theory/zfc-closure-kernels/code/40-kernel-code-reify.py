#!/usr/bin/env python3
"""Explicit closed-selector and class-term construction for pure-E formulas.

Formula syntax: ('atom', i, j), ('nand', p, q), ('exists', i, p), ('bottom',).
Variables 0 and 1 are reserved as the two free matrix arguments. Values of
other free variables are loaded into a finite assignment. The output is
syntax, not a serialized derivation in a proof-assistant kernel.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import finite_kernel as fk

c = fk.term("c")
k = fk.term("N", c, c)
vcc = fk.term("V", c, c)
vkk = fk.term("V", k, k)
r = fk.term("C", fk.term("C", c, c, fk.term("N", vcc, vcc)),
            k, fk.term("N", vkk, vkk))


def successor(t):
    return fk.term("C", r, r, t)


def selector(index):
    if type(index) is not int or index < 0:
        raise ValueError("nonnegative variable index required")
    if index == 0:
        return c
    if index == 1:
        return k
    result = c
    for _ in range(index - 1):
        result = successor(result)
    return result


def free_variables(formula):
    kind = formula[0]
    if kind == "atom":
        return {formula[1], formula[2]}
    if kind == "bottom":
        return set()
    if kind == "nand":
        return free_variables(formula[1]) | free_variables(formula[2])
    if kind == "exists":
        return free_variables(formula[2]) - {formula[1]}
    raise ValueError("unknown formula constructor")


def reify(formula):
    kind = formula[0]
    if kind == "atom":
        return fk.term("A", selector(formula[1]), selector(formula[2]))
    if kind == "nand":
        return fk.term("N", reify(formula[1]), reify(formula[2]))
    if kind == "exists":
        return fk.term("Q", selector(formula[1]), reify(formula[2]))
    if kind == "bottom":
        top = fk.term("N", c, k)
        return fk.term("N", top, top)
    raise ValueError("unknown formula constructor")


def descriptor(formula):
    result = c
    for index in sorted(free_variables(formula) - {0, 1}):
        result = fk.term("C", result, selector(index), fk.variable("p" + str(index)))
    # Header is loaded last; these parameter selectors are all different from c.
    return fk.term("C", result, c, reify(formula))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=Path(__file__).resolve().parents[1] / "data")
    args = parser.parse_args()
    # R(x,y;p) = NAND(E(x,p), exists z NAND(E(z,y),E(z,x))).
    # This is a representation example, not a refutation or a set axiom.
    example = ("nand", ("atom", 0, 2),
               ("exists", 3, ("nand", ("atom", 3, 1), ("atom", 3, 0))))
    code = reify(example)
    desc = descriptor(example)
    if fk.term_variables(code):
        raise AssertionError("class term must be closed")
    if fk.term_variables(desc) != {"p2"}:
        raise AssertionError("descriptor has an unexpected parameter")
    record = {"formula": example, "free_variables": sorted(free_variables(example)),
              "class_term": code, "class_term_occurrences": fk.term_size(code),
              "descriptor_term": desc, "descriptor_term_occurrences": fk.term_size(desc),
              "selector_occurrences": [fk.term_size(selector(i)) for i in range(12)],
              "scope": "explicit syntax construction; proof is in the report"}
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / "reification_example.json").write_text(json.dumps(record, indent=2) + "\n")
    (args.out / "reification_example.txt").write_text(
        "CLASS TERM\n" + fk.show_term(code) + "\n\nDESCRIPTOR\n" + fk.show_term(desc) + "\n")
    print(json.dumps({key: record[key] for key in
                      ("free_variables", "class_term_occurrences", "descriptor_term_occurrences", "selector_occurrences")}, indent=2))


if __name__ == "__main__":
    main()
