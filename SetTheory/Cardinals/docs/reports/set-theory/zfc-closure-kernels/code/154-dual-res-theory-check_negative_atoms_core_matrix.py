#!/usr/bin/env python3
"""Check a small obstruction to a proposed negative-atom shortcut.

This checks a core matrix, NOT the native K scheme and NOT a Turing machine.
The finite powerset checks cover every possible set of value pairs in one
quantifier fiber, hence verify the stated distribution law without a bound
on the cardinality of the underlying domain.
"""
from itertools import product
from pathlib import Path
import json

if not __debug__:
    raise RuntimeError("Run without Python optimization: assertions are checks")

C = (
    (3, 3, 3, 3),
    (3, 3, 0, 3),
    (3, 3, 3, 3),
    (0, 0, 1, 3),
)
F = 0
DESIGNATED = 3
VALUES = range(4)


def imp(a, b):
    return C[a][b]


def neg(a):
    return imp(a, F)


def qall(values):
    values = frozenset(values)
    assert values
    if values == {DESIGNATED}:
        return DESIGNATED
    return 2 if F in values else 0


def lukasiewicz(a, b, c, u):
    return imp(imp(imp(c, u), a), imp(imp(a, c), imp(b, c)))


def nonempty_subsets(seq):
    seq = tuple(seq)
    for mask in range(1, 1 << len(seq)):
        yield tuple(seq[i] for i in range(len(seq)) if mask & (1 << i))


def run():
    assert all(imp(DESIGNATED, x) != DESIGNATED for x in VALUES
               if x != DESIGNATED)
    assert all(imp(x, x) == DESIGNATED for x in VALUES)
    assert all(imp(F, x) == DESIGNATED for x in VALUES)
    assert qall({DESIGNATED}) == DESIGNATED
    assert all(lukasiewicz(a, b, c, F) == DESIGNATED
               for a, b, c in product(VALUES, repeat=3))
    distribution_count = 0
    for pairs in nonempty_subsets(product(VALUES, repeat=2)):
        lhs = qall(imp(a, b) for a, b in pairs)
        rhs = imp(qall(a for a, b in pairs), qall(b for a, b in pairs))
        assert imp(lhs, rhs) == DESIGNATED, pairs
        distribution_count += 1

    # Along a quantifier fiber Q A is constant, so subsequent Q's in
    # Ex Q A apply qall to singleton sets. Check every possible A-value set.
    rho6_count = 0
    for values in nonempty_subsets(VALUES):
        qa = qall(values)
        ex_qa = neg(qall({neg(qa)}))
        assert all(imp(ex_qa, a) == DESIGNATED for a in values), values
        rho6_count += 1

    # Commuting coordinate quantifiers have the same designatedness:
    # each iterated Q is designated iff every entry of the value array is.
    # All Q outputs lie in {0,2,3}; among these, nondesignated antecedents
    # imply every value. This finite implication check proves rho4 once
    # that elementary quantifier-fiber observation is made.
    qvalues = {qall(s) for s in nonempty_subsets(VALUES)}
    assert qvalues == {0, 2, 3}
    for x, y in product(qvalues, repeat=2):
        if (x == DESIGNATED) == (y == DESIGNATED):
            assert imp(x, y) == DESIGNATED

    negatives = {neg(x) for x in VALUES}
    assert negatives == {0, 3}
    closure = set(negatives)
    while True:
        expanded = closure | {imp(a, b) for a, b in product(closure, repeat=2)}
        expanded |= {qall(s) for s in nonempty_subsets(closure)}
        if expanded == closure:
            break
        closure = expanded
    assert closure == set(VALUES)
    witness = (0, 3, 1, 2)
    assert lukasiewicz(*witness) != DESIGNATED

    # Double negation does normalize to ordinary Boolean values. This
    # demonstrates why the example does not refute a stabilized translation.
    assert all(neg(neg(x)) == (3 if x == 3 else 0) for x in VALUES)
    for a, b in product((0, 3), repeat=2):
        assert imp(a, b) == (0 if a == 3 and b == 0 else 3)
    for values in nonempty_subsets(VALUES):
        assert neg(neg(qall(values))) == (3 if set(values) == {3} else 0)

    return {
        "claim": "CORE_MATRIX_ONLY; no native K or equiconsistency claim",
        "implication": C,
        "F": F,
        "designated": DESIGNATED,
        "quantifier": "3 on {3}; 2 if 0 belongs to the nonempty value set; 0 otherwise",
        "checked": {
            "modus_ponens": True,
            "identity": True,
            "explosion": True,
            "GEN": True,
            "restricted_L_F_instances": 64,
            "distribution_value_pair_sets": distribution_count,
            "rho6_value_sets": rho6_count,
            "rho4": "same designatedness plus the checked {0,2,3} implication property",
        },
        "negative_values": sorted(negatives),
        "I_Q_closure_of_negative_values": sorted(closure),
        "full_L_failure_abcu": witness,
        "full_L_failure_value": lukasiewicz(*witness),
        "double_negation_normalizes_to_boolean": True,
    }


if __name__ == "__main__":
    receipt = run()
    output = Path(__file__).with_name("negative_atoms_core_matrix_receipt.json")
    output.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))
