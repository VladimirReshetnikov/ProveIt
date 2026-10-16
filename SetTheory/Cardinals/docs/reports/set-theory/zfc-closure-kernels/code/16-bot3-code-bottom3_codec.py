#!/usr/bin/env python3
"""Three-residue formula codec with Truth=0 and genuine Bottom=1.

This is a reference implementation and finite regression suite for a numerical
syntax theorem. It is not a proof checker, compiler proof, or consistency result.
Formula normalization only contracts Imp(Truth, Truth) to Truth, recursively.
No imported repository code is required; Python's standard library suffices.
"""

from __future__ import annotations

import argparse
from functools import cache
import itertools
import json
from math import isqrt
from pathlib import Path
import random


TOP = ("top",)
BOTTOM = ("bottom",)


def pair(a: int, b: int) -> int:
    if a < 0 or b < 0:
        raise ValueError("Cantor pairing requires natural numbers")
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n: int) -> tuple[int, int]:
    if n < 0:
        raise ValueError("Cantor unpairing requires a natural number")
    s = (isqrt(8 * n + 1) - 1) // 2
    b = n - s * (s + 1) // 2
    return s - b, b


def imp(a, b):
    return TOP if a == TOP and b == TOP else ("imp", a, b)


def normalize(f):
    tag = f[0]
    if tag in ("top", "bottom", "rel"):
        return f
    if tag == "imp":
        return imp(normalize(f[1]), normalize(f[2]))
    if tag == "all":
        return ("all", f[1], normalize(f[2]))
    raise ValueError(f"Unknown formula tag: {tag}")


def encode(f) -> int:
    tag = f[0]
    if tag == "top":
        return 0
    if tag == "bottom":
        return 1
    if tag == "rel":
        return 3 * pair(f[1], f[2]) + 4
    if tag == "imp":
        return 3 * pair(encode(f[1]), encode(f[2]))
    if tag == "all":
        return 3 * pair(f[1], encode(f[2])) + 2
    raise ValueError(f"Unknown formula tag: {tag}")


@cache
def decode(n: int):
    if n < 0:
        raise ValueError("Formula codes are natural numbers")
    if n == 0:
        return TOP
    if n == 1:
        return BOTTOM
    residue = n % 3
    if residue == 0:
        a, b = unpair(n // 3)
        return ("imp", decode(a), decode(b))
    if residue == 1:
        a, b = unpair((n - 4) // 3)
        return ("rel", a, b)
    a, b = unpair((n - 2) // 3)
    return ("all", a, decode(b))


def labels(f):
    """All labels, including bound-variable labels (not only free labels)."""
    if f[0] in ("top", "bottom"):
        return set()
    if f[0] == "rel":
        return {f[1], f[2]}
    if f[0] == "imp":
        return labels(f[1]) | labels(f[2])
    if f[0] == "all":
        return {f[1]} | labels(f[2])
    raise ValueError(f)


def alpha_key(f, binders=()):
    def variable(i):
        for depth, label in enumerate(reversed(binders)):
            if i == label:
                return ("bound", depth)
        return ("free", i)
    if f[0] in ("top", "bottom"):
        return f
    if f[0] == "rel":
        return ("rel", variable(f[1]), variable(f[2]))
    if f[0] == "imp":
        return ("imp", alpha_key(f[1], binders), alpha_key(f[2], binders))
    if f[0] == "all":
        return ("all", alpha_key(f[2], binders + (f[1],)))
    raise ValueError(f)


def rename(f, permutation):
    """Rename all labels by a permutation, including their binders."""
    if f[0] in ("top", "bottom"):
        return f
    if f[0] == "rel":
        return ("rel", permutation[f[1]], permutation[f[2]])
    if f[0] == "imp":
        return ("imp", rename(f[1], permutation), rename(f[2], permutation))
    if f[0] == "all":
        return ("all", permutation[f[1]], rename(f[2], permutation))
    raise ValueError(f)


def evaluate(f, relation, env, domain):
    if f[0] == "top":
        return True
    if f[0] == "bottom":
        return False
    if f[0] == "rel":
        return (env[f[1]], env[f[2]]) in relation
    if f[0] == "imp":
        return not evaluate(f[1], relation, env, domain) or evaluate(
            f[2], relation, env, domain)
    if f[0] == "all":
        return all(evaluate(f[2], relation, env | {f[1]: a}, domain)
                   for a in domain)
    raise ValueError(f)


def random_formula(rng, depth):
    choices = 3 if depth == 0 else 5
    tag = rng.randrange(choices)
    if tag == 0:
        return TOP
    if tag == 1:
        return BOTTOM
    if tag == 2:
        return ("rel", rng.randrange(4), rng.randrange(4))
    if tag == 3:
        return ("imp", random_formula(rng, depth - 1),
                random_formula(rng, depth - 1))
    return ("all", rng.randrange(4), random_formula(rng, depth - 1))


def check(limit=200_000, random_cases=5_000):
    for n in range(limit):
        f = decode(n)
        assert encode(f) == n
        assert normalize(f) == f
        assert all(i < n for i in labels(f))
        assert (f == BOTTOM) == (n == 1)
        assert (f == TOP) == (n == 0)
    rng = random.Random(20261016)
    semantic_cases = 0
    renaming_cases = 0
    for _ in range(random_cases):
        f = random_formula(rng, 5)
        g = normalize(f)
        assert decode(encode(f)) == g
        assert encode(g) == encode(f)
        assert normalize(g) == g
        p = list(range(4))
        rng.shuffle(p)
        assert normalize(rename(f, p)) == rename(g, p)
        renaming_cases += 1
        # Independent finite model semantics checks ancestor normalization,
        # quantifiers, vacuous binders, and binder shadowing.
        for _model in range(4):
            relation = {(a, b) for a, b in itertools.product(range(2), repeat=2)
                        if rng.randrange(2)}
            env = {i: rng.randrange(2) for i in range(4)}
            assert evaluate(f, relation, env, range(2)) == evaluate(
                g, relation, env, range(2))
            semantic_cases += 1
    # Alpha-equivalent canonical formulas need not have equal numerical codes.
    a = ("all", 0, ("rel", 0, 0))
    b = ("all", 1, ("rel", 1, 1))
    assert alpha_key(a) == alpha_key(b)
    assert encode(a) != encode(b)
    # Same implication constructor collision can occur inside any ancestor.
    c = ("all", 2, ("imp", ("imp", TOP, TOP), BOTTOM))
    d = ("all", 2, ("imp", TOP, BOTTOM))
    assert c != d and encode(c) == encode(d)
    assert normalize(c) == d
    # Genuine Bottom is never a diagonal membership atom.
    assert encode(("rel", 0, 0)) == 4
    assert decode(1) == BOTTOM and decode(4) == ("rel", 0, 0)
    return {
        "codec": "Truth0_Bottom1_Imp3P_Rel3Pplus4_All3Pplus2",
        "numeric_roundtrips": limit,
        "strict_label_bound_cases": limit,
        "canonical_formula_roundtrips": random_cases,
        "normalization_renaming_cases": renaming_cases,
        "normalization_semantic_cases": semantic_cases,
        "alpha_equivalence_is_not_numeric_equality": True,
        "ancestor_collision_control": True,
        "bottom_is_not_membership_atom": True,
        "numerical_encode_decode_identity": True,
        "raw_ast_decode_encode_identity": False,
        "raw_ast_decode_encode_is_recursive_normalization": True,
        "proof_calculus_or_binary_machine_certified": False,
        "sample_codes": {str(n): repr(decode(n)) for n in range(15)},
    }


def main():
    if not __debug__:
        raise RuntimeError("Run without -O; this regression suite uses assertions")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--limit", type=int, default=200_000)
    args = parser.parse_args()
    evidence = check(args.limit)
    text = json.dumps(evidence, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
