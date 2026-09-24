#!/usr/bin/env python3
"""A 126-operation certificate for a recoding of the Jones 1980 system.

The input parameters are x,Z,u,y,H. Put z=Z/2 and L=5**59 at the
metalevel. The quadruple Z,u,y,H is admissible when (z,u,y) is an
admissible Jones triple and H is a power of two greater than

    max(2*Z**(2*L+1), Z*60**4, 3*L).

H is part of the encoding, so its construction is not hidden inside this
certificate. The numeral L is free under the basic operation convention.
The new radix is B=H*b**4, and the Pell exponent is q=B**L. The old
combined inequality is replaced by b=x+beta and e*l*g**2+alpha=q**2.
See ../1980/RECODING_PROOF.md for the equivalence proof and size bounds.

This file deliberately retains all other parts of the original 129-step
schedule, to isolate three operations saved by recoding alone. Run it
directly to perform exact symbolic checks and write its JSON receipt.
"""
from __future__ import annotations

import json
from pathlib import Path
import sympy as sp

import round4_1980_operation_count as baseline

HERE = Path(__file__).resolve().parent
OUT = HERE / "round4_1980_recoded_certificate.json"
L = 5 ** 59


def make_schedule():
    result = []
    omitted = {"xy", "bxy", "R1", "z2", "ezl"}
    for target, op, left, right in baseline.SCHEDULE:
        if target in omitted:
            continue
        if target == "b5":
            result.append(("B", "*", "H", "b4"))
            continue
        if target == "L1":
            result.append((target, op, left, right))
            result.append(("bx", "+", "x", "beta"))
            continue
        if target == "L3":
            result.append((target, "+", "th", "Z"))
            continue
        if target == "zl":
            result.append((target, "*", "Z", "la"))
            result.append(("twice_e", "*", 2, "e"))
            continue
        if target == "t2":
            result.append((target, "-", "twice_e", "zl"))
            continue
        if target == "amb":
            result.append((target, "-", "a", "B"))
            continue
        if target == "R20":
            result.append((target, "+", "Dam1", L))
            continue
        result.append(("H17" if target == "H" else target, op,
                       "B" if left == "b5" else "H17" if left == "H" else left,
                       "B" if right == "b5" else "H17" if right == "H" else right))
    return result


SCHEDULE = make_schedule()
EQUALITIES = [("L1", "q2"), ("b", "bx")] + [
    ("B" if left == "b5" else left,
     "B" if right == "b5" else right)
    for left, right in baseline.EQUALITIES[1:]
]
NAMES = [name for name in baseline.NAMES if name != "z"] + ["Z", "H", "beta"]
SYM = {name: sp.Symbol(name) for name in NAMES}


def source_residuals():
    s = SYM
    B = s["H"] * s["b"] ** 4
    substitutions = {baseline.SYM["z"]: s["Z"] / 2,
                     baseline.SYM["b"] ** 5: B}
    old = baseline.source_residuals()
    result = [s["e"] * s["l"] * s["g"] ** 2 + s["al"] - s["q"] ** 2,
              s["b"] - s["x"] - s["beta"]]
    result.extend(sp.expand(res.subs(substitutions, simultaneous=True))
                  for res in old[1:])
    result[-3] = s["mu"] - (s["q"] + s["ka"] * (s["a"] - B)
                            + s["rho"] * (2 * s["a"] * B - B ** 2 - 1))
    result[-1] = s["ka"] - (L + s["Delta"] * (s["a"] - 1))
    return result


def verify_certificate():
    env = dict(SYM)
    histogram = baseline.run_schedule(SCHEDULE, env)
    residuals = source_residuals()
    baseline.need(len(EQUALITIES) == len(residuals) == 21, "twenty-one equations")
    signs = []
    for (left, right), source in zip(EQUALITIES, residuals):
        difference = sp.expand(env[left] - env[right])
        if sp.expand(difference - source) == 0:
            signs.append(1)
        elif sp.expand(difference + source) == 0:
            signs.append(-1)
        else:
            raise AssertionError(f"symbolic residual mismatch: {left} = {right}")
    used = {name for _, _, left, right in SCHEDULE
            for name in (left, right) if isinstance(name, str)}
    used |= {name for pair in EQUALITIES for name in pair}
    baseline.need(set(NAMES) <= used, "every parameter and variable used")
    baseline.need(sum(histogram.values()) == 126, "126-operation recoding")
    return {"status": "PASS", "operations": sum(histogram.values()),
            "straight_line_histogram": histogram,
            "additions_and_multiplications_only": {
                "additions": histogram["+"] + histogram["-"],
                "multiplications": histogram["*"]},
            "equality_tests": len(EQUALITIES), "residual_signs": signs,
            "unknowns": 33, "parameters": ["x", "Z", "u", "y", "H"],
            "equations": 21, "exponent_numeral": str(L),
            "scope": "recoded admissible indices; not pointwise equivalence to the original tuples"}


if __name__ == "__main__":
    receipt = verify_certificate()
    OUT.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(receipt, indent=2))
