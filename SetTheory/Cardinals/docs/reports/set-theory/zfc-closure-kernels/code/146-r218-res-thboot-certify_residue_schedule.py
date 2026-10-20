#!/usr/bin/env python3
"""Recheck the algebra and bounded arithmetic regression for the residue lemma.

The theorem for all natural parameters is proved in residue_scheduler.tex.
This standard-library script checks both polynomial identities exactly and
performs the stated finite regression; the finite part is not its proof.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def add(*polys):
    out = {}
    for p in polys:
        for m, c in p.items():
            out[m] = out.get(m, 0) + c
    return {m: c for m, c in out.items() if c}


def scale(c, p):
    return {m: c * x for m, x in p.items() if c * x}


def mul(p, q):
    out = {}
    for m, c in p.items():
        for n, d in q.items():
            key = tuple(x + y for x, y in zip(m, n))
            out[key] = out.get(key, 0) + c * d
    return {m: c for m, c in out.items() if c}


def pair2(a, b):
    s = add(a, b)
    return add(mul(s, s), s, scale(2, b))


def exact_identities():
    one = {(0, 0, 0): 1}
    a, b, d = ({(1, 0, 0): 1}, {(0, 1, 0): 1}, {(0, 0, 1): 1})
    first = add(pair2(add(a, d), b), scale(-1, pair2(a, b)))
    first_rhs = mul(d, add(scale(2, a), scale(2, b), d, one))
    second = add(pair2(a, add(b, d)), scale(-1, pair2(a, b)))
    second_rhs = mul(d, add(scale(2, a), scale(2, b), d, scale(3, one)))
    assert first == first_rhs
    assert second == second_rhs
    return [
        "2(P(a+d,b)-P(a,b)) = d(2(a+b)+d+1)",
        "2(P(a,b+d)-P(a,b)) = d(2(a+b)+d+3)",
    ]


def pair(a, b):
    return (a + b) * (a + b + 1) // 2 + b


def candidate(u, tail):
    return pair(3, pair(1, pair(1, pair(u, tail))))


def v2(n):
    assert n > 0
    return (n & -n).bit_length() - 1


def finite_regression():
    valuations = 0
    bijections = 0
    lifts = 0
    for tail in range(8):
        for base in range(16):
            values = [candidate(base + 16 * t, tail) for t in range(257)]
            for s in range(32):
                for t in range(s + 1, 65):
                    assert v2(values[t] - values[s]) == v2(t - s)
                    valuations += 1
            for k in range(1, 9):
                modulus = 1 << k
                assert len({v % modulus for v in values[:modulus]}) == modulus
                bijections += 1
                for wanted in range(modulus):
                    index = 0
                    for bit in range(k):
                        if ((values[index] - wanted) >> bit) & 1:
                            index += 1 << bit
                    assert values[index] % modulus == wanted
                    lifts += 1
    return dict(
        tail_range=[0, 7],
        base_range=[0, 15],
        valuation_comparisons=valuations,
        modulus_exponents=[1, 8],
        residue_bijections=bijections,
        constructive_lifts=lifts,
    )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=HERE / "residue_lemma_receipt.json")
    args = parser.parse_args()
    result = dict(
        status="EXACT_POLYNOMIAL_IDENTITIES_AND_BOUNDED_ARITHMETIC_REGRESSION_PASS",
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        identities=exact_identities(),
        regression=finite_regression(),
        scope=("The polynomial identities are checked coefficient by coefficient over Z. "
               "The all-natural valuation and cofinality theorem is an ordinary mathematical "
               "proof in residue_scheduler.tex; the bounded regression is supplementary."),
    )
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
