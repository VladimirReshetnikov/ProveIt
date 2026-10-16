#!/usr/bin/env python3
"""Finite diagnostic for the retained logical rows, not the full theory.

All quantifiers act as the identity. Distinct named membership atoms are
independent Boolean variables. This interpretation validates every retained
logical schema, but refutes an ordinary first-order instantiation theorem.
The C/G theory rows are deliberately not claimed valid in this interpretation.
"""
import argparse
import itertools
import json
from pathlib import Path


def imp(a, b):
    return (not a) or b


def rel_and(a, b, falsity):
    return imp(imp(a, imp(b, falsity)), falsity)


def run():
    values = (False, True)
    counts = {}
    tests = {
        "lukasiewicz": (4, lambda a, b, c, u:
            imp(imp(imp(c, u), a), imp(imp(a, c), imp(b, c)))),
        "quantifier_distribution_identity": (2, lambda a, b:
            imp(imp(a, b), imp(a, b))),
        "quantifier_commutation_identity": (1, lambda a: imp(a, a)),
        "old_B6c_identity": (1, lambda a: imp(a, a)),
        "dual_B6c_identity": (1, lambda a: imp(a, a)),
        "vacuity_identity": (1, lambda a: imp(a, a)),
        "reflexivity_identity": (1, lambda a: imp(a, a)),
    }
    for name, (arity, predicate) in tests.items():
        rows = list(itertools.product(values, repeat=arity))
        if not all(predicate(*row) for row in rows):
            raise RuntimeError("Failed logical-schema check: " + name)
        counts[name] = len(rows)
    # Generalization sends a valid A to the same truth value, hence is sound.
    counts["generalization_validity_preservation"] = 1
    counterexample = {"Rel(0,0)": False, "Rel(0,1)": True,
                      "Rel(2,1)": False, "All(i,A)": "A"}
    target_value = imp(counterexample["Rel(0,1)"], counterexample["Rel(2,1)"])
    if target_value:
        raise RuntimeError("The intended instantiation counterexample failed")
    swap_checks = 0
    for f, a, b, c in itertools.product(values, repeat=4):
        assert rel_and(a, b, f) == rel_and(b, a, f)
        assert rel_and(rel_and(a, b, f), c, f) == rel_and(a, rel_and(b, c, f), f)
        assert rel_and(a, b, f) == (f or (a and b))
        swap_checks += 3
    return {
        "logical_schema_boolean_cases": counts,
        "ordinary_FOL_valid_formula": "All(0,Rel(0,1)) -> Rel(2,1)",
        "counterinterpretation": counterexample,
        "formula_value": target_value,
        "conclusion": "The retained logical rows alone are not FOL complete.",
        "limitation": "This is not a model of the C/G theory rows and does not prove nonhalting of any candidate.",
        "relative_conjunction_checks": swap_checks,
        "relative_conjunction_identity": "and_F(A,B) = F or (A and B)",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = json.dumps(run(), indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(result)
    print(result, end="")
