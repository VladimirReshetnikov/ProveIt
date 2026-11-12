"""Check the finite selector calculations in boolean_absorber.tex.

This is a symbolic algebra sanity check, not a formal verification of
first-order derivations, primitive-recursive interpretation, or
bi-interpretability.  The accumulator is an uninterpreted symbol, so these
checks make no boundedness or Boolean assumption about its value.
"""

import json


def selector(flag, left, right):
    """The two proved selector equations at flags 0 and 1 only."""
    assert flag in (0, 1)
    return left if flag == 0 else right


def main():
    accumulator = "arbitrary_accumulator_value"
    transitions = []
    for old_flag in (0, 1):
        for new_flag in (0, 1):
            # The induction step excludes precisely the transition 0 -> 1.
            if old_flag == 0 and new_flag == 1:
                continue
            old_value = selector(old_flag, accumulator, 0)
            next_accumulator = old_value
            new_value = selector(new_flag, next_accumulator, 0)
            assert new_value == old_value
            transitions.append(
                {
                    "old_flag": old_flag,
                    "new_flag": new_flag,
                    "old_F": old_value,
                    "new_F": new_value,
                }
            )

    # The initial and terminal selector equations used by the proof.
    assert selector(0, 1, 0) == 1
    assert selector(1, accumulator, 0) == 0

    # Quantifier-free characteristic terms use 0 for true and 1 for false.
    connective_rows = []
    for p in (0, 1):
        for q in (0, 1):
            conjunction = selector(p, q, 1)
            disjunction = selector(p, 0, q)
            implication = selector(p, q, 0)
            assert (conjunction == 0) == ((p == 0) and (q == 0))
            assert (disjunction == 0) == ((p == 0) or (q == 0))
            assert (implication == 0) == ((p != 0) or (q == 0))
            connective_rows.append(
                {"p": p, "q": q, "and": conjunction,
                 "or": disjunction, "implies": implication}
            )

    print(json.dumps({
        "result": "PASS",
        "stationary_transition_cases": transitions,
        "connective_truth_tables": connective_rows,
        "accumulator_interpretation": "uninterpreted symbol",
        "not_checked": [
            "formal first-order derivations",
            "schema soundness in all models",
            "primitive-recursive translation",
            "bi-interpretability",
        ],
    }, indent=2))


if __name__ == "__main__":
    main()
