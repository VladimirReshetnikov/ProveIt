#!/usr/bin/env python3
"""Deterministic finite regressions for the reversed-code high-mask lemma.

These bounded integer examples supplement the general proof. They neither
construct the enormous fixed universal index nor establish the universal
positive-domain theorem by testing. No frozen certificate is imported or
modified.
"""
from __future__ import annotations

import itertools
import json
from pathlib import Path
import random

SEED = 0x1980111


def evaluate(coefficients, base):
    result = 0
    for coefficient in reversed(coefficients):
        result = result*base+coefficient
    return result


def digits(value, base, length):
    result = []
    for _ in range(length):
        value, digit = divmod(value, base)
        result.append(digit)
    assert value == 0, "requested digit window must contain the whole number"
    return result


def power_two_above(value):
    return 1 << value.bit_length()


def coefficient_patterns(K, b, rng):
    if b == 2 and K <= 3:
        return [(1,)+row for row in itertools.product(range(b), repeat=K)]
    rows = {(1,)+(0,)*K, (1,)+(b-1,)*K,
            (1,)+tuple((b-1) if i % 2 else 0 for i in range(K))}
    for i in range(K):
        rows.add((1,)+tuple((b-1) if i == j else 0 for j in range(K)))
    for _ in range(4):
        rows.add((1,)+tuple(rng.randrange(b) for _ in range(K)))
    return sorted(rows)


def multipliers(e0, B, K, rng):
    candidates = {0, 1, 2, e0-1, e0//2, e0//3}
    candidates.update(range(min(65, e0)))
    for i in range(K+1):
        for delta in [-1, 0, 1]:
            candidates.add(B**i+delta)
    for _ in range(24):
        candidates.add(rng.randrange(e0))
    return sorted(m for m in candidates if 0 <= m < e0)


def weak_bound_control():
    """A nonzero quotient can escape when the exponential bound is omitted."""
    B, Z, K, L = 8, 4, 1, 6
    C, A, e0, m = 1, 1, 9, 3
    e = e0-m
    q = B**L
    lam = (q*q-1)//(B-1)
    S3 = (2*e-Z*lam)*C*C+B*lam*(1+q)
    X = (B-2)*m
    assert B > Z*A
    assert B <= Z*A*2**(K+2)
    assert S3 & (X*q) == 0
    assert m > 0 and X % (B-2) == 0
    return {"B": B, "Z": Z, "K": K, "L": L, "C": C,
            "e0": e0, "m": m, "X": X,
            "high_digits": [(S3//q//B**j) % B for j in range(K+2)],
            "mask_digits": digits(X, B, K+2),
            "meaning": "Nonzero m passes the high mask when the required exponential bound is omitted"}


def main():
    rng = random.Random(SEED)
    counters = {"coefficient_cases": 0, "residual_code_cases": 0,
                "quotient_trials": 0, "high_digits_checked": 0,
                "nonzero_quotients_rejected": 0,
                "zero_quotients_accepted": 0,
                "compatible_artificial_masks": 0,
                "nonzero_artificial_masks": 0}
    B_values = []
    sample = None
    for K in range(5):
        L = 3*K+3
        assert L > 3*K+2
        for b, Z in itertools.product([2, 4], [4, 8]):
            for C_coefficients in coefficient_patterns(K, b, rng):
                A = sum(C_coefficients)**2
                B = power_two_above(max(Z*A*2**(K+3), 8*Z*b*b, 16))
                B_values.append(B)
                assert B > Z*A*2**(K+2)
                C = evaluate(C_coefficients, B)
                assert C_coefficients[0] == 1
                assert all(0 <= digit < b for digit in C_coefficients)
                assert A == sum(C_coefficients)**2
                q = B**L
                lam, remainder = divmod(q*q-1, B-1)
                assert remainder == 0
                assert C*C < q
                expected_high = [B-Z*A]+[B-Z*A+1]*(K+1)
                counters["coefficient_cases"] += 1
                codes = {(1,)*(K+1), (Z-1,)*(K+1),
                         tuple(rng.randrange(1, Z) for _ in range(K+1))}
                for code_coefficients in sorted(codes):
                    e0 = evaluate(code_coefficients, B)
                    assert 0 < e0 < Z*B**K
                    counters["residual_code_cases"] += 1
                    for m in multipliers(e0, B, K, rng):
                        e = e0-m
                        assert 0 < e <= e0
                        assert 2*e*C*C < B**(3*K+1) < q
                        S3 = (2*e-Z*lam)*C*C+B*lam*(1+q)
                        assert 0 < S3 < q**4
                        actual_high = [(S3//q//B**j) % B for j in range(K+2)]
                        assert actual_high == expected_high
                        assert all(B-Z*A <= digit <= B-Z*A+2 for digit in actual_high)
                        X = (B-2)*m
                        X_digits = digits(X, B, K+2)
                        carry_free = (S3 & (q*X)) == 0
                        digitwise_carry_free = all((left & right) == 0
                                                  for left, right in zip(actual_high, X_digits))
                        assert carry_free == digitwise_carry_free
                        if carry_free:
                            assert all(digit <= Z*A-1 for digit in X_digits)
                            evaluation_at_two = evaluate(X_digits, 2)
                            assert evaluation_at_two < Z*A*2**(K+2) < B-2
                            assert (X-evaluation_at_two) % (B-2) == 0
                            assert evaluation_at_two == 0
                            assert m == 0
                            counters["zero_quotients_accepted"] += 1
                        else:
                            assert m != 0
                            counters["nonzero_quotients_rejected"] += 1
                        counters["quotient_trials"] += 1
                        counters["high_digits_checked"] += K+2
                        if sample is None and K == 2 and m:
                            sample = {"K": K, "L": L, "B": B, "b": b,
                                      "Z": Z, "C_coefficients": list(C_coefficients),
                                      "A": A, "e0_coefficients": list(code_coefficients),
                                      "m": m, "high_digits": actual_high,
                                      "mask_digits": X_digits, "carry_free": carry_free}
                    # Exercise the no-carry digit bound nonvacuously: construct
                    # compatible masks without requiring divisibility by B-2.
                    for _ in range(8):
                        mask_digits = [rng.randrange(B) & (B-1-digit)
                                       for digit in expected_high]
                        assert all((digit & mask) == 0 for digit, mask in zip(expected_high, mask_digits))
                        assert all(mask <= Z*A-1 for mask in mask_digits)
                        mask_value = evaluate(mask_digits, B)
                        evaluation_at_two = evaluate(mask_digits, 2)
                        assert (mask_value-evaluation_at_two) % (B-2) == 0
                        assert 0 <= evaluation_at_two < Z*A*2**(K+2) < B-2
                        assert (mask_value % (B-2) == 0) == (mask_value == 0)
                        counters["compatible_artificial_masks"] += 1
                        counters["nonzero_artificial_masks"] += bool(mask_value)
    assert counters["nonzero_quotients_rejected"] > 1000
    assert counters["nonzero_artificial_masks"] > 100
    receipt = {"status": "PASS", "seed": SEED, "maximum_tested_degree": 4,
               "coefficient_bounds_b": [2, 4], "digit_bases_Z": [4, 8],
               "L_rule": "L=3K+3", "minimum_radix": min(B_values),
               "maximum_radix": max(B_values), "counts": counters,
               "sample_rejected_quotient": sample,
               "control_without_exponential_bound": weak_bound_control(),
               "scope": "Deterministic finite regressions of high-digit formulas, no-carry bounds, and evaluation at 2; supplements the general proof only",
               "universal_index_constructed": False,
               "formal_proof_claimed": False}
    Path(__file__).with_suffix(".json").write_text(json.dumps(receipt, indent=2)+"\n", encoding="utf-8")
    print("PASS:", json.dumps(counters, sort_keys=True))
    print("PASS: nonzero-quotient control when exponential hypothesis is omitted")


if __name__ == "__main__":
    main()
