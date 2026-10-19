#!/usr/bin/env python3
"""Exhaustive finite certificate for the fourth-input no-go theorem.

No theorem prover, SAT solver, external package, or bounded proof search.
The checker proves the finite matrix obligations.  The unbounded term
claim additionally uses the elementary induction in fourth_input_no_go.tex.
Only the logical subsystem is covered; CP and GIC are not assumed valid.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path

if not __debug__:
    raise RuntimeError('Run this certificate checker without -O or -OO.')


M3 = [[2, 2, 2], [1, 2, 2], [0, 1, 2]]
M4 = [[3, 3, 3, 3], [3, 3, 0, 3], [3, 3, 3, 3], [0, 0, 0, 3]]


def verify(matrix, order, role):
    size = len(matrix)
    values = tuple(range(size))
    top = size - 1
    assert sorted(order) == list(values)
    assert all(len(row) == size and all(x in values for x in row) for row in matrix)
    rank = {x: i for i, x in enumerate(order)}
    implication = lambda x, y: matrix[x][y]
    negation = lambda x: implication(x, 0)
    universal = lambda x, y: min((x, y), key=rank.__getitem__)
    existential = lambda x, y: negation(universal(negation(x), negation(y)))
    lukasiewicz = lambda a, b, c, u: implication(
        implication(implication(c, u), a),
        implication(implication(a, c), implication(b, c)),
    )
    peirce = lambda a, b: implication(implication(implication(a, b), a), a)
    checks = {}

    def check(name, arity, condition):
        cases = tuple(itertools.product(values, repeat=arity))
        for case in cases:
            assert condition(*case), (role, name, case)
        checks[name] = len(cases)

    check("modus_ponens", 2,
          lambda a, b: a != top or implication(a, b) != top or b == top)
    check("identity", 1, lambda a: implication(a, a) == top)
    check("K", 2, lambda a, b: implication(a, implication(b, a)) == top)
    check("ex_falso", 1, lambda a: implication(0, a) == top)
    check("double_negation_elimination", 1,
          lambda a: implication(negation(negation(a)), a) == top)
    check("rho2_quantifier_distribution", 4,
          lambda a0, b0, a1, b1: implication(
              universal(implication(a0, b0), implication(a1, b1)),
              implication(universal(a0, a1), universal(b0, b1))) == top)
    check("rho4_quantifier_commutation", 4,
          lambda a, b, c, d: universal(universal(a, b), universal(c, d))
          == universal(universal(a, c), universal(b, d)))
    check("rho6_at_both_individual_assignments", 2,
          lambda a, b: implication(existential(universal(a, b), universal(a, b)), a) == top
          and implication(existential(universal(a, b), universal(a, b)), b) == top)
    check("fresh_atomic_vacuity", 1,
          lambda a: implication(a, universal(a, a)) == top)
    assert universal(top, top) == top
    checks["generalization_of_valid_formula"] = 1

    # Native equality on a two-element individual domain.  Coincident labels
    # give the vector (top,top), and distinct labels give (top,0) or (0,top).
    for equality_vector in ((top, 0), (0, top), (top, top)):
        assert existential(*equality_vector) == top
    checks["rho1_equality_existence"] = 3

    individuals = (0, 1)
    equality = lambda x, y: top if x == y else 0
    triples = tuple(itertools.product(individuals, repeat=3))
    equality_checks = 0
    # Every membership truth table, not only our selected irreflexive witness.
    for cells in itertools.product(values, repeat=4):
        membership = lambda x, y: cells[2*x+y]
        for a, b, c in triples:
            assert implication(equality(c, a),
                               implication(equality(c, b), equality(a, b))) == top
            assert implication(equality(c, a),
                               implication(membership(c, b), membership(a, b))) == top
            assert implication(equality(a, b),
                               implication(membership(c, a), membership(c, b))) == top
            equality_checks += 1
    checks["rho3_rho5_rho7_each_all_membership_tables"] = equality_checks
    assert negation(0) == top
    checks["irreflexivity_for_zero_diagonal_membership"] = 1

    failures = [list(v) + [lukasiewicz(*v)]
                for v in itertools.product(values, repeat=4)
                if lukasiewicz(*v) != top]

    if role == "bare_a":
        check("specialization_U_equals_a", 3,
              lambda a, b, c: lukasiewicz(a, b, c, a) == top)
        assert failures == [[1, 2, 1, 0, 1]]
        witness_membership = [[0, 1], [0, 0]]
        p, q = 1, 0
        covered = ["U=a"]
    else:
        assert role == "all_compounds_and_other_leaves"
        implication_range = sorted({x for row in matrix for x in row})
        assert implication_range == [0, top]
        assert failures == [[0, 3, 1, 2, 0], [1, 3, 1, 2, 0], [2, 3, 1, 2, 0]]
        check("rho8_for_every_possible_implication_root", 4,
              lambda a, b, c, u: u not in (0, top)
              or lukasiewicz(a, b, c, u) == top)
        check("specialization_U_equals_b", 3,
              lambda a, b, c: lukasiewicz(a, b, c, b) == top)
        check("specialization_U_equals_c", 3,
              lambda a, b, c: lukasiewicz(a, b, c, c) == top)
        check("specialization_U_equals_F", 3,
              lambda a, b, c: lukasiewicz(a, b, c, 0) == top)
        check("specialization_U_equals_Truth", 3,
              lambda a, b, c: lukasiewicz(a, b, c, top) == top)
        witness_membership = [[0, 1], [2, 0]]
        p, q = 1, 2
        covered = ["U=b", "U=c", "U=F", "U=Truth", "any implication-root term U"]

    assert peirce(p, q) != top
    assert all(witness_membership[x][x] == 0 for x in individuals)
    return {
        "role": role,
        "matrix": matrix,
        "designated_values": [top],
        "F": 0,
        "Truth": top,
        "universal_minimum_order": order,
        "individual_domain": list(individuals),
        "checked_cases": checks,
        "full_rho8_failures": failures,
        "covered_substitutions": covered,
        "witness_membership": witness_membership,
        "Peirce_counterexample": {"P": p, "Q": q, "value": peirce(p, q)},
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("fourth_input_no_go_certificate.json"))
    args = parser.parse_args()
    result = {
        "status": "PASS",
        "matrices": [verify(M3, [0, 1, 2], "bare_a"),
                     verify(M4, [0, 2, 1, 3], "all_compounds_and_other_leaves")],
        "unbounded_claim": (
            "For every finite implication term U over a,b,c,F,Truth, the logical "
            "subsystem obtained by replacing rho8(a,b,c,u) with rho8(a,b,c,U) "
            "fails at least one Peirce instance. A term is a leaf or has an "
            "implication root; the two matrices cover all possibilities."
        ),
        "scope": "rho1-rho7, specialized rho8, MP, GEN, fresh atomic vacuity, IR, K, identity, ex falso, DNE",
        "CP_or_GIC_validity_claimed": False,
        "full_set_theory_inequiconsistency_claimed": False,
        "new_Turing_machine_state_bound_claimed": False,
        "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": result["status"], "output": str(args.output),
                      "case_counts": [m["checked_cases"] for m in result["matrices"]]}, indent=2))


if __name__ == "__main__":
    main()
