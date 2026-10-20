#!/usr/bin/env python3
"""Finite counterinterpretation for deleting B6c in favor of modal T.

This interprets the PURE LOGICAL rows, not the K set-theoretic axioms.
It proves that the retained logical rows, even with full atomic equality
vacuity, do not entail B6c.  It does not prove an inconsistency or a
consistency claim for the resulting set theory.
"""
import argparse
import itertools
import json
from pathlib import Path


WORLDS = (0, 1)
EDGES = {(0, 0), (0, 1), (1, 1)}
TOP = frozenset(WORLDS)
BOTTOM = frozenset()
VALUES = tuple(frozenset(w for w in WORLDS if mask & (1 << w))
               for mask in range(4))


def implies(a, b):
    return (TOP - a) | b


def box(a):
    return frozenset(w for w in WORLDS
                     if all(v in a for x, v in EDGES if x == w))


def diamond(a):
    # Exists is the original relative-negation definition, with F = false.
    return implies(box(implies(a, BOTTOM)), BOTTOM)


def all_valid(values):
    values = list(values)
    if any(v != TOP for v in values):
        raise AssertionError("A claimed axiom failed in the counterinterpretation")
    return len(values)


def check():
    # Each Eq(a,b), independently of the two labels, means the same up-set.
    equality = frozenset({1})
    # Each Rel(a,b), independently of labels, is false at both worlds.
    membership = BOTTOM
    checks = {}
    checks["classical_Lukasiewicz_row_all_truthsets"] = all_valid(
        implies(implies(implies(c, u), a),
                implies(implies(a, c), implies(b, c)))
        for a, b, c, u in itertools.product(VALUES, repeat=4))
    checks["rho2_normal_modal_K_all_truthsets"] = all_valid(
        implies(box(implies(a, b)), implies(box(a), box(b)))
        for a, b in itertools.product(VALUES, repeat=2))
    checks["replacement_T_all_truthsets"] = all_valid(
        implies(box(a), a) for a in VALUES)
    checks["rho4_quantifier_commutation_all_truthsets"] = all_valid(
        implies(box(box(a)), box(box(a))) for a in VALUES)
    checks["rho1_equality_witness_including_coincident_labels"] = all_valid(
        [diamond(equality)])
    checks["rho7_Euclid"] = all_valid(
        [implies(equality, implies(equality, equality))])
    checks["rho3_and_rho5_membership_congruence"] = all_valid(
        [implies(equality, implies(membership, membership))] * 2)
    checks["full_membership_vacuity"] = all_valid(
        [implies(membership, box(membership))])
    checks["full_equality_vacuity_stronger_than_REL_helper"] = all_valid(
        [implies(equality, box(equality))])
    checks["modus_ponens_preserves_global_validity"] = sum(
        1 for a, b in itertools.product(VALUES, repeat=2)
        if not (a == TOP and implies(a, b) == TOP) or b == TOP)
    if checks["modus_ponens_preserves_global_validity"] != 16:
        raise AssertionError("Modus ponens did not preserve global validity")
    checks["generalization_preserves_global_validity"] = all_valid([box(TOP)])
    # A is a real formula, Eq(0,0), not a fresh propositional letter.
    antecedent = diamond(box(equality))
    b6c = implies(antecedent, equality)
    if 0 not in antecedent or 0 in equality or 0 in b6c:
        raise AssertionError("The B6c failure witness is not a counterexample")
    return {
        "status": "PASS_PURE_LOGICAL_NONDERIVABILITY_OBSTRUCTION",
        "worlds": list(WORLDS),
        "accessibility": [list(edge) for edge in sorted(EDGES)],
        "interpretation": {
            "all_named_universals": "the same forward box on accessibility",
            "all_membership_atoms": sorted(membership),
            "all_equality_atoms": sorted(equality),
            "relative_false_Rel_0_0": [],
        },
        "validity_checks": checks,
        "B6c_failure": {
            "formula_A": "Eq(0,0)",
            "A_truthset": sorted(equality),
            "All_a_A_truthset": sorted(box(equality)),
            "Exists_a_All_a_A_truthset": sorted(antecedent),
            "B6c_truthset": sorted(b6c),
            "failure_world": 0,
        },
        "scope": (
            "The logical rows with B6c replaced by T cannot derive B6c, "
            "even granting full equality vacuity. This is not a model "
            "of the K set-theoretic axiom scheme, and it does not settle "
            "the consistency strength of a K-plus-T variant."
        ),
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = check()
    payload = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload)
    print(payload, end="")
