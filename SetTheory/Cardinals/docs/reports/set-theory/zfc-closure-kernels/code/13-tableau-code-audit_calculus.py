#!/usr/bin/env python3
"""Executable diagnostics for the 252-state equality-free logical kernel.

The accompanying mathematical proof is an induction over derivations using
the Boolean valuation below. The finite tests only audit this implementation.
No valuation here is asserted to satisfy the C/G nonlogical bundles.
"""
from __future__ import annotations

import argparse
from functools import lru_cache
from itertools import product
from math import isqrt
import json
from pathlib import Path


def pair(a: int, b: int) -> int:
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n: int) -> tuple[int, int]:
    s = (isqrt(8 * n + 1) - 1) // 2
    b = n - s * (s + 1) // 2
    return s - b, b


def imp(a: int, b: int) -> int:
    return 3 * pair(a, b)


def rel(i: int, j: int) -> int:
    return 3 * pair(i, j) + 1


def all_(i: int, a: int) -> int:
    return 3 * pair(i, a) + 2


def not_(a: int) -> int:
    return imp(a, 1)


def ex(i: int, a: int) -> int:
    return not_(all_(i, not_(a)))


def luk(a: int, b: int, c: int, u: int) -> int:
    return imp(imp(imp(c, u), a), imp(imp(a, c), imp(b, c)))


def qi(a: int, b: int, c: int) -> int:
    return imp(all_(a, imp(b, c)), imp(all_(a, b), all_(a, c)))


def comm(a: int, b: int, c: int) -> int:
    return imp(all_(a, all_(b, c)), all_(b, all_(a, c)))


def dual(a: int, b: int) -> int:
    return imp(b, all_(a, ex(a, b)))


def old(a: int, b: int) -> int:
    return imp(ex(a, all_(a, b)), b)


def vac(a: int, b: int, c: int) -> int:
    return imp(rel(a, b), all_(c, rel(a, b)))


def valuation(true_atoms: frozenset[tuple[int, int]]):
    @lru_cache(maxsize=100000)
    def val(n: int) -> bool:
        if n == 0:
            return True
        a, b = unpair(n // 3)
        tag = n % 3
        if tag == 0:
            return not val(a) or val(b)
        if tag == 1:
            return (a, b) in true_atoms
        return val(b)  # Every quantifier is the identity Boolean operation.
    return val


@lru_cache(maxsize=50000)
def decode(n: int):
    if n == 0:
        return ("top",)
    a, b = unpair(n // 3)
    if n % 3 == 0:
        return ("imp", decode(a), decode(b))
    if n % 3 == 1:
        return ("rel", a, b)
    return ("all", a, decode(b))


def encode(f):
    match f:
        case ("top",): return 0
        case ("imp", a, b): return imp(encode(a), encode(b))
        case ("rel", a, b): return rel(a, b)
        case ("all", a, b): return all_(a, encode(b))
    raise ValueError(f)


def labels(f):
    match f:
        case ("top",): return set()
        case ("imp", a, b): return labels(a) | labels(b)
        case ("rel", a, b): return {a, b}
        case ("all", a, b): return {a} | labels(b)
    raise ValueError(f)


def check() -> dict:
    # Universal scalar schematic cases for identity quantifiers. This is
    # independent of numeric coding and uses every truth assignment.
    impl = lambda a, b: not a or b
    truth_cases = []
    for a, b, c, u in product((False, True), repeat=4):
        assert impl(impl(impl(c, u), a), impl(impl(a, c), impl(b, c)))
        assert impl(impl(b, c), impl(b, c))  # QI.
        assert impl(c, c)                  # Commutation and atomic vacuity.
    for f, p in product((False, True), repeat=2):
        exists_p = impl(impl(p, f), f)
        dual_value, old_value = impl(p, exists_p), impl(exists_p, p)
        assert dual_value
        assert old_value == impl(f, p)
        truth_cases.append({"F": f, "p": p, "dual": dual_value, "old": old_value})
    models = {
        "name_incoherent_false_F": frozenset({(0, 1)}),
        "true_F": frozenset({(0, 0)}),
    }
    evidence = {}
    for name, atoms in models.items():
        v = valuation(atoms)
        tested = 0
        for a, b, c, u in product(range(8), repeat=4):
            assert v(luk(a, b, c, u))
            tested += 1
        for a, b, c in product(range(8), repeat=3):
            for schema in (qi, comm, vac):
                assert v(schema(a, b, c))
                tested += 1
        for a, b in product(range(8), repeat=2):
            assert v(dual(a, b))
            assert v(all_(a, b)) == v(b)
            assert v(imp(a, b)) == (not v(a) or v(b))
            tested += 3
        evidence[name] = {"true_atoms": sorted(atoms), "F_value": v(1),
                          "schema_and_constructor_checks": tested}
    v = valuation(models["name_incoherent_false_F"])
    substitution = imp(all_(0, rel(0, 1)), rel(2, 1))
    alpha = imp(all_(0, all_(1, rel(0, 1))),
                all_(2, all_(1, rel(2, 1))))
    assert not v(substitution) and not v(alpha)
    # Old B6c is also valid throughout the first Boolean algebra.
    assert all(v(old(a, b)) for a, b in product(range(8), repeat=2))
    w = valuation(models["true_F"])
    p = rel(0, 1)
    assert w(dual(0, p)) and not w(old(0, p))
    count = 10000
    for n in range(count):
        a, b = unpair(n)
        assert pair(a, b) == n
        assert encode(decode(n)) == n
        assert all(i < n for i in labels(decode(n)))
        if n:
            a, b = unpair(n // 3)
            assert a < n and b < n
    return {
        "status": "passed",
        "Lukasiewicz_all_boolean_assignments": 16,
        "identity_quantifier_old_dual_truth_table": truth_cases,
        "models": evidence,
        "valid_FOL_but_kernel_underivable": {
            "substitution_formula": "(forall v0. Rel(v0,v1)) -> Rel(v2,v1)",
            "substitution_base3_code": substitution,
            "substitution_countermodel_value": v(substitution),
            "closed_alpha_formula": "(forall v0 forall v1. Rel(v0,v1)) -> (forall v2 forall v1. Rel(v2,v1))",
            "closed_alpha_base3_code": alpha,
            "closed_alpha_countermodel_value": v(alpha),
        },
        "dual_not_old": {
            "p_base3_code": p,
            "dual_value": w(dual(0, p)),
            "old_value": w(old(0, p)),
        },
        "codec_integer_range_checked": [0, count - 1],
        "codec_checks": ["Cantor inversion", "encode(decode(n))=n", "all labels < n", "positive-node children < n"],
        "scope": "Exact witnesses and finite code diagnostics. Universal nonderivability rests on the Boolean soundness proof. Neither model is asserted to satisfy full C/G, and no 252-state nonhalting or consistency theorem is asserted.",
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    result = check()
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
