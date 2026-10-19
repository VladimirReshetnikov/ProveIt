#!/usr/bin/env python3
"""Sufficient proof certificates for safe C254 formula and stack codes.

This is a sound, deliberately incomplete recognizer.  A negative recognition
result means UNKNOWN, not nonderivability.  The rules are justified in
safe_start_proof.tex; this Python program is not a proof-assistant kernel.
The logical source interface is DirtyProgram254.path_halts_iff_native_refutation.
"""
from __future__ import annotations

import argparse
from functools import lru_cache
from math import isqrt
import json


def pair(a: int, b: int) -> int:
    if a < 0 or b < 0:
        raise ValueError("Cantor pairing requires natural numbers")
    return (a + b) * (a + b + 1) // 2 + b


def unpair(z: int) -> tuple[int, int]:
    if z < 0:
        raise ValueError("A code must be a natural number")
    diagonal = (isqrt(8 * z + 1) - 1) // 2
    b = z - diagonal * (diagonal + 1) // 2
    return diagonal - b, b


@lru_cache(maxsize=None)
def classify(n: int) -> tuple[int, str, tuple[int, ...]]:
    """Return (polarity, rule, premises).

    +1 certifies C254(n); -1 certifies C254(n -> F); 0 is unknown.
    Premises are numeric codes, with the rule fixing their polarities.
    In particular, -1 does NOT claim that C254(n) is unprovable.
    """
    if n < 0:
        raise ValueError("A code must be a natural number")
    if n == 0:
        return 1, "truth", ()
    a, b = unpair(n // 4)
    tag = n % 4
    if tag == 1 and a == b:
        return -1, "irreflexive_membership", (a,)
    if tag == 3 and a == b:
        return 1, "equality_reflexivity", (a,)
    if tag == 2:
        if classify(b)[0] == 1:
            return 1, "generalization", (a, b)
        return 0, "unknown", ()
    if tag == 0:
        sa, sb = classify(a)[0], classify(b)[0]
        if sb == 1:
            return 1, "theorem_consequent", (a, b)
        if sa == -1:
            return 1, "refutable_antecedent", (a, b)
        if a == b:
            return 1, "implication_identity", (a,)
        if sa == 1 and sb == -1:
            return -1, "refutable_implication", (a, b)
    return 0, "unknown", ()


def formula_safe(n: int) -> bool:
    return classify(n)[0] == 1


def stack_certificate(z: int) -> dict | None:
    """Certify Good(z) by peeling a finite list followed by the zero stream."""
    original = z
    heads = []
    while z != 0:
        a, b = unpair(z)
        if not formula_safe(a):
            return None
        if not b < z:
            raise AssertionError("Nonzero Cantor tail must decrease")
        heads.append(a)
        z = b
    return {"code": original, "heads": heads, "tail": 0}


def stack_safe(z: int) -> bool:
    return stack_certificate(z) is not None


def logical_root_safe(registers) -> bool:
    """Input order is N,T,W,A,D,H,X,Y,L, not physical tape order."""
    if len(registers) != 9 or any(not isinstance(x, int) or x < 0 for x in registers):
        return False
    return formula_safe(registers[1]) and stack_safe(registers[2]) and formula_safe(registers[5])


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--limit", type=int, default=256)
    ap.add_argument("--output")
    args = ap.parse_args()
    if args.limit < 0:
        ap.error("--limit must be nonnegative")
    formulas = [n for n in range(args.limit + 1) if formula_safe(n)]
    stacks = [n for n in range(args.limit + 1) if stack_safe(n)]
    result = {
        "status": "SUFFICIENT_CERTIFICATES",
        "limit_inclusive": args.limit,
        "theorem_codes": formulas,
        "safe_stack_codes": stacks,
        "formula_rules": {
            str(n): {"polarity": classify(n)[0], "rule": classify(n)[1], "premises": classify(n)[2]}
            for n in range(args.limit + 1) if classify(n)[0] != 0
        },
        "stack_certificates": [stack_certificate(n) for n in stacks],
        "unknown_means": "No certificate from this recognizer, not nonderivability",
        "negative_polarity_means": "Derivable implication to falsity, not metatheoretic nonderivability",
        "proof_status": "Ordinary rule-soundness proof; no new Lean compilation",
    }
    out = json.dumps(result, indent=2) + "\n"
    if args.output:
        with open(args.output, "w", encoding="utf-8") as f:
            f.write(out)
    print(json.dumps({"limit": args.limit, "theorem_codes": formulas, "safe_stack_codes": stacks}))


if __name__ == "__main__":
    main()
