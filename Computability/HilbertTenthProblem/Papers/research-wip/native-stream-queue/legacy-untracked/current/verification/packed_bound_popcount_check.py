#!/usr/bin/env python3
"""Finite exact regression for the unbounded packed-bound counterfamily.

This checks the integer identity R=P*2**m-D, its binary digit sum, and
the central-binomial valuation. It does not instantiate the enormous
admissible coefficient index or prove the universal Pell construction;
that proof is in EXPLORATION_PACKED_BOUND_FULL_COUNTEREXAMPLE.md.
"""
from __future__ import annotations

import json
from math import comb
from pathlib import Path


def v2_positive(value: int) -> int:
    assert value > 0
    return (value & -value).bit_length() - 1


def factorial_v2(value: int) -> int:
    result = 0
    while value:
        value //= 2
        result += value
    return result


def verify() -> dict:
    families = 0
    exact_binomials = 0
    threshold_checks = 0
    passing_thresholds = 0
    for p in range(2, 33):
        for d in range(1, p):
            for m in range(1, 25):
                if 2**m <= d:
                    continue
                r = p * 2**m - d
                predicted = (p - 1).bit_count() + m - (d - 1).bit_count()
                assert r > 0
                assert r.bit_count() == predicted
                valuation = factorial_v2(2 * r) - 2 * factorial_v2(r)
                assert valuation == predicted
                families += 1
                if r <= 512:
                    assert v2_positive(comb(2 * r, r)) == predicted
                    exact_binomials += 1
                for n_exponent in range(1, 9):
                    threshold = (2 * n_exponent + (d - 1).bit_count()
                                 - (p - 1).bit_count())
                    passes = valuation >= 2 * n_exponent
                    assert passes == (m >= threshold)
                    threshold_checks += 1
                    passing_thresholds += passes
    return {
        "status": "PASS",
        "family_identity_cases": families,
        "exact_math_comb_cases": exact_binomials,
        "divisibility_threshold_cases": threshold_checks,
        "passing_divisibility_threshold_cases": passing_thresholds,
        "parameters": {"P": [2, 32], "D": "1 <= D < P",
                       "m": "1 <= m <= 24, 2**m > D",
                       "N": "2**j, 1 <= j <= 8"},
        "proof": "../1980/EXPLORATION_PACKED_BOUND_FULL_COUNTEREXAMPLE.md",
        "scope": "Finite exact regression only; the universal collapse and all positive Pell witnesses are established in the separate proof note.",
    }


if __name__ == "__main__":
    receipt = verify()
    Path(__file__).with_suffix(".json").write_text(
        json.dumps(receipt, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(receipt, indent=2))
