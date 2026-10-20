#!/usr/bin/env python3
"""Finite algebra certificate for the uniform restricted-rho8 obstruction.

The infinite HC interpretation is inherited from the released K219 proof.
This checker certifies the finite premises of the extension; the induction
over arbitrary term size is stated in uniform_rho8_obstruction.md.
"""
from itertools import product
import json
from pathlib import Path

TABLE = ((3, 3, 3, 3), (3, 3, 1, 3), (3, 3, 3, 3), (0, 0, 0, 3))
VALUES = range(4)
SAFE = {0, 1, 3}


def implication(a, b):
    return TABLE[a][b]


def row(a, b, c, u):
    I = implication
    return I(I(I(c, u), a), I(I(a, c), I(b, c)))


def verify():
    bad = [x for x in product(VALUES, repeat=4) if row(*x) != 3]
    assert bad == [(0, 3, 1, 2), (1, 3, 1, 2)]
    assert {v for r in TABLE for v in r} == SAFE
    assert all(row(a, b, c, u) == 3
               for a, b, c in product(VALUES, repeat=3) for u in SAFE)
    assert all(row(a, b, c, u) == 3
               for a, b, c in product(VALUES, repeat=3)
               for u in (a, b, c, 0, 3))
    for a, b, c, u in bad:
        assert u == 2 and {a, b, c, 0, 3}.issubset(SAFE)
    return {
        "status": "FINITE_PREMISES_VERIFIED",
        "matrix": TABLE,
        "designated": 3,
        "falsum": 0,
        "all_nondesignated_L_instances": bad,
        "implication_range": sorted(SAFE),
        "quantifier_and_equality_range": [0, 3],
        "safe_U_instances": 4**3 * len(SAFE),
        "simple_projection_and_constant_instances": 4**3 * 5,
        "uniform_extension": (
            "Every U built from A,B,C,F,truth and equality atoms by implication "
            "and universal quantification is valid as a restriction; arbitrary "
            "independent formulas are allowed under an implication or quantifier "
            "at U's root. The proof is structural, not a bounded term search."
        ),
        "scope": (
            "Finite algebra premises only. The inherited HC model validates "
            "every other native row, MP, GEN and full gated seed-K; the note "
            "explains why that proof is unaffected."
        ),
    }


if __name__ == "__main__":
    result = verify()
    destination = Path(__file__).with_suffix(".json")
    destination.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
