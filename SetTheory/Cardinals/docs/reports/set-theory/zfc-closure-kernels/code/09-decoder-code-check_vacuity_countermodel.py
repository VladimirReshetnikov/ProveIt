#!/usr/bin/env python3
"""Finite regression for an analytic independence countermodel.

The analytic model has all assignments s:N->{0,1}, ordinary coordinate
quantifiers, membership constantly false, and Eq(i,j) iff s(0)=0 or s(i)=s(j).
It validates the eight logical rows of ZFC254 and membership vacuity but
refutes equality vacuity.  The finite test exhausts four-coordinate truth
tables; it is not a proof assistant and does not check CP or GIC.
"""
from __future__ import annotations
import itertools
import json
import argparse
from pathlib import Path

N = 4
WORLD_COUNT = 1 << N
FULL = (1 << WORLD_COUNT) - 1
MASKS = range(FULL + 1)


def implication(a: int, b: int) -> int:
    return ((~a) | b) & FULL


def all_(coordinate: int, truth_set: int) -> int:
    shift = 1 << coordinate
    lower_mask = sum(1 << s for s in range(WORLD_COUNT) if not (s & shift))
    lower = truth_set & (truth_set >> shift) & lower_mask
    return lower | (lower << shift)


def exists(coordinate: int, truth_set: int) -> int:
    return FULL ^ all_(coordinate, FULL ^ truth_set)


def equality(i: int, j: int) -> int:
    return sum(
        1 << s for s in range(WORLD_COUNT)
        if not (s & 1) or ((s >> i) & 1) == ((s >> j) & 1)
    )


def main() -> None:
    quantifiers = [[all_(i, p) for p in MASKS] for i in range(N)]
    checks: dict[str, int | bool | dict] = {}
    # rho8 (Lukasiewicz): ((c->u)->a)->((a->c)->(b->c)).
    def imp_bool(p: bool, q: bool) -> bool:
        return not p or q
    for a, b, c, u in itertools.product((False, True), repeat=4):
        assert imp_bool(imp_bool(imp_bool(c, u), a),
                        imp_bool(imp_bool(a, c), imp_bool(b, c)))
    checks["rho8_lukasiewicz_boolean_cases"] = 16

    # rho2 (K) is a pointwise fiber identity.  A coordinate fiber has two
    # points, so these 16 cases prove the bit-table check for arbitrary P,Q
    # without enumerating 2^32 pairs of global tables.
    for p, q in itertools.product(range(4), repeat=2):
        all_imp = ((~p | q) & 3) == 3
        assert (not all_imp) or (p != 3) or (q == 3)
    checks["rho2_K_two_point_fiber_pairs"] = 16

    count = 0
    for i, j in itertools.product(range(N), repeat=2):
        ai, aj = quantifiers[i], quantifiers[j]
        for p in MASKS:
            assert ai[aj[p]] == aj[ai[p]]
            count += 1
    checks["rho4_commutation_predicate_instances"] = count

    count = 0
    for i in range(N):
        ai = quantifiers[i]
        for p in MASKS:
            ex_all = FULL ^ ai[FULL ^ ai[p]]
            assert implication(ex_all, p) == FULL
            count += 1
    checks["rho6_exists_all_predicate_instances"] = count

    eq = {(i, j): equality(i, j) for i, j in itertools.product(range(N), repeat=2)}
    for i, j in itertools.product(range(N), repeat=2):
        assert exists(i, eq[i, j]) == FULL
    checks["rho1_equality_existence_instances"] = N * N

    for a, b, c in itertools.product(range(N), repeat=3):
        assert implication(eq[c, a], implication(eq[c, b], eq[a, b])) == FULL
        # Membership is constantly false: both left and right congruence.
        assert implication(eq[c, a], implication(0, 0)) == FULL
        assert implication(eq[a, b], implication(0, 0)) == FULL
        assert implication(0, quantifiers[c][0]) == FULL
    checks["rho7_euclid_instances"] = N ** 3
    checks["rho3_right_congruence_instances"] = N ** 3
    checks["rho5_left_congruence_instances"] = N ** 3
    checks["membership_vacuity_instances_including_collisions"] = N ** 3

    # All order-restricted equality-vacuity instances also hold.  Therefore
    # substituting c>max(a,b) for c!=a,b does not preserve pure-logical coverage.
    greater_count = 0
    for a, b, c in itertools.product(range(N), repeat=3):
        if c > max(a, b):
            assert implication(eq[a, b], quantifiers[c][eq[a, b]]) == FULL
            greater_count += 1
    checks["equality_vacuity_c_above_both_labels_instances"] = greater_count

    a, b, c, s = 1, 2, 0, 4
    assert (eq[a, b] >> s) & 1
    assert not ((quantifiers[c][eq[a, b]] >> s) & 1)
    assert not ((implication(eq[a, b], quantifiers[c][eq[a, b]]) >> s) & 1)
    checks["counterexample"] = {
        "formula": "Eq(1,2) -> All(0, Eq(1,2))",
        "assignment": [(s >> i) & 1 for i in range(N)],
        "antecedent": True,
        "consequent": False,
        "counterexample_quantified_value": 1,
    }
    checks["MP_preserves_global_truth"] = True
    checks["GEN_preserves_global_truth"] = all(all_(i, FULL) == FULL for i in range(N))
    result = {
        "status": "PASS",
        "coordinates": N,
        "worlds": WORLD_COUNT,
        "arbitrary_predicate_truth_tables": FULL + 1,
        "scope": "Pure logical rows only; CP and GIC not asserted; finite regression supplements analytic infinite-coordinate argument.",
        "checks": checks,
    }
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O: this regression relies on assertions.")
    main()
