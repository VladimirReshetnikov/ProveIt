#!/usr/bin/env python3
"""Finite regression for HIGH_MASK_SINGLE_OFFSET_PROOF.md, not its proof."""
from __future__ import annotations

import json
from pathlib import Path
from random import Random


def digits(value, radix, count):
    out = []
    for _ in range(count):
        value, digit = divmod(value, radix)
        out.append(digit)
    return out


def main():
    rng = Random(103104)
    cases = high_digits = rejected_aliases = 0
    epsilon_counts = {-1: 0, 0: 0}
    for K in range(1, 7):
        L, b, Z = 3*K + 3, 8, 4
        # This toy scale directly meets the high-mask inequality; no
        # astronomical fixed index of the actual certificate is evaluated.
        bound = Z*(K*b)**2*4**(K + 2)
        B = 1 << bound.bit_length()
        q = B**L
        la = (q*q - 1)//(B - 1)
        for _ in range(24):
            coeffs = [rng.randrange(b) for _ in range(K)]
            coeffs[0] = rng.randrange(1, b)
            C = sum(value*B**j for j, value in enumerate(coeffs))
            A = sum(coeffs)**2
            e = rng.randrange(1, B**K)
            assert 0 < Z*A < B//4 and 0 < 2*e*C*C < q
            V = Z*la*C*C
            epsilon = (2*e*C*C - V % q)//q
            assert epsilon in (-1, 0)
            S3 = (2*e - Z*la)*C*C + B*la*q
            assert S3 > 0
            actual = digits(S3//q, B, K + 1)
            expected = [B - Z*A + epsilon] + [B - Z*A]*K
            assert actual == expected
            epsilon_counts[epsilon] += 1
            high_digits += len(actual)
            for m in [0, 1, 2, B**K - 1, rng.randrange(1, B**K)]:
                X = (B - 4)*m
                xd = digits(X, B, K + 1)
                F4 = sum(value*4**j for j, value in enumerate(xd))
                assert F4 % (B - 4) == 0
                if m:
                    assert any(x + y >= B for x, y in zip(xd, actual))
                    rejected_aliases += 1
                else:
                    assert all(value == 0 for value in xd)
            cases += 1
    result = {
        "status": "PASS", "integer_cases": cases,
        "high_digits_compared": high_digits,
        "nonzero_aliases_rejected": rejected_aliases,
        "epsilon_counts": epsilon_counts,
        "scope": "deterministic finite regression of the independent high-digit lemma; universal validity is proved in HIGH_MASK_SINGLE_OFFSET_PROOF.md",
    }
    out = Path(__file__).with_suffix(".json")
    out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
