#!/usr/bin/env python3
"""Exact finite checks for Lubin--Tate interpolation inverse poles.

This uses ordinary integer arithmetic modulo p**r, hence tests the unramified
coefficient case pi=p. q may be any tested power of p. The report's proof,
not these examples, establishes the result for general ramified DVRs.

Run from any directory; the JSON output is written to ../checks/jet_checks.json
relative to this script. No third-party packages are required.
"""
from __future__ import annotations

import json
from math import comb
from pathlib import Path


def add(a: dict[int, int], b: dict[int, int], modulus: int) -> dict[int, int]:
    result = a.copy()
    for exponent, coefficient in b.items():
        result[exponent] = (result.get(exponent, 0) + coefficient) % modulus
    return {i: c for i, c in result.items() if c}


def mul(a: dict[int, int], b: dict[int, int], modulus: int) -> dict[int, int]:
    result: dict[int, int] = {}
    for i, x in a.items():
        for j, y in b.items():
            result[i + j] = (result.get(i + j, 0) + x * y) % modulus
    return {i: c for i, c in result.items() if c}


def power(a: dict[int, int], n: int, modulus: int) -> dict[int, int]:
    result = {0: 1}
    for _ in range(n):
        result = mul(result, a, modulus)
    return result


def vp(n: int, p: int) -> int:
    assert n > 0
    answer = 0
    while n % p == 0:
        answer += 1
        n //= p
    return answer


def check_case(p: int, q: int, contacts: tuple[int, ...], r: int) -> dict:
    modulus = p**r
    largest = max(contacts)
    iterates = [{1: 1}]
    for _ in range(largest):
        linear = {i: p * c % modulus for i, c in iterates[-1].items()}
        iterates.append(add(linear, power(iterates[-1], q, modulus), modulus))

    product = {0: 1}
    inverse = {0: 1}
    for depth in contacts:
        f = iterates[depth]
        degree = q**depth
        product = mul(product, f, modulus)
        # F_a = X**degree * (1+G), with G divisible by p and nilpotent.
        negative_g = {
            i - degree: (-c) % modulus for i, c in f.items() if i != degree
        }
        term = {0: 1}
        geometric = {0: 1}
        for _ in range(1, r):
            term = mul(term, negative_g, modulus)
            geometric = add(geometric, term, modulus)
        inverse = mul(
            inverse, {i - degree: c for i, c in geometric.items()}, modulus
        )

    assert mul(product, inverse, modulus) == {0: 1}, "inverse identity failed"
    pole = -min(inverse)
    w = sum(q**a for a in contacts)
    multiplicity = contacts.count(largest)
    slope = (q - 1) * q ** (largest - 1) if largest else 0
    upper = w + (r - 1) * slope
    old_upper = w + (r - 1) * (q**largest - 1)
    binomial = comb(multiplicity + r - 2, r - 1)
    predicted_equality = largest == 0 or binomial % p != 0
    assert pole <= upper
    assert (pole == upper) == predicted_equality
    if largest > 1 and r > 1:
        assert upper < old_upper, "old-bound strictness failed"
        assert pole < old_upper
    depth_one_k = None
    if largest == 1:
        depth_one_k = max(
            k
            for k in range(r)
            if k + vp(comb(multiplicity + k - 1, k), p) < r
        )
        assert pole == w + (q - 1) * depth_one_k

    return {
        "p": p,
        "q": q,
        "contacts": list(contacts),
        "r": r,
        "W": w,
        "A": largest,
        "m": multiplicity,
        "lambda": slope,
        "actual_pole": pole,
        "actual_precision": pole + 1,
        "improved_upper_pole": upper,
        "old_upper_pole": old_upper,
        "extreme_binomial_mod_p": binomial % p,
        "predicted_equality": predicted_equality,
        "depth_one_K": depth_one_k,
        "inverse_identity_verified": True,
    }


def main() -> None:
    contact_sets = (
        (1,), (1, 1), (1, 1, 1), (0, 1, 1), (2,),
        (1, 2), (2, 2), (1, 2, 2), (3,),
    )
    cases = []
    for p, q in ((2, 2), (2, 4), (3, 3), (3, 9)):
        for contacts in contact_sets:
            if q == 9 and max(contacts) > 2:
                continue
            for r in range(1, 7):
                cases.append(check_case(p, q, contacts, r))
    assert len(cases) == 210
    example = next(
        c for c in cases
        if c["p"] == c["q"] == 3 and c["contacts"] == [1, 1] and c["r"] == 3
    )
    assert example["actual_pole"] == 8
    assert example["actual_precision"] == 9
    assert example["old_upper_pole"] + 1 == 11
    report = {
        "status": "passed",
        "arithmetic": "exact sparse Laurent polynomials over Z/(p^r), pi=p",
        "case_count": len(cases),
        "checks": [
            "computed inverse multiplied by original product equals one",
            "improved Newton-slope bound",
            "exact binomial equality criterion",
            "strictness of old bound for A>1 and r>1",
            "exact depth-one all-r finite maximum formula",
            "q=3, m=2, r=3 gives pole 8 and precision 9 instead of coarse 11",
        ],
        "strict_improved_bound_cases": sum(
            c["actual_pole"] < c["improved_upper_pole"] for c in cases
        ),
        "old_bound_strict_by_depth_cases": sum(
            c["A"] > 1 and c["r"] > 1 for c in cases
        ),
        "highlighted_example": example,
        "cases": cases,
        "limitations": [
            "Finite examples do not substitute for the mathematical proof.",
            "Ramified coefficient DVRs are covered by the proof, not these computations.",
        ],
    }
    output = Path(__file__).resolve().parents[1] / "checks" / "jet_checks.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: {len(cases)} exact Laurent inverse checks")
    print("Highlighted q=3, m=2, r=3: pole 8; required precision 9; coarse precision 11")
    print(f"JSON results: {output}")


if __name__ == "__main__":
    main()
