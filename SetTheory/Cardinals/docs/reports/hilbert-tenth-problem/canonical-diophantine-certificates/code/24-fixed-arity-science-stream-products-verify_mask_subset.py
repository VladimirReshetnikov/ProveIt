#!/usr/bin/env python3
"""Own finite checks; no imports or execution of upstream certificate code."""
import json
import math
from pathlib import Path


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


cases = 0
valid_cases = 0
for M in range(128):
    L = 2 ** (M + 1)
    Z = (1 + L) ** M
    for X in range(M + 4):
        Y = L ** X
        quotient, r = divmod(Z, Y)
        q, c = divmod(quotient, L)
        true_coefficient = math.comb(M, X) if X <= M else 0
        require(c == true_coefficient, (M, X, "coefficient"))
        is_subset = X & M == X
        require(c % 2 == int(is_subset), (M, X, "parity"))
        require(Z == (q * L + c) * Y + r, (M, X, "division"))
        require(0 <= c < L and 0 <= r < Y, (M, X, "bounds"))
        if is_subset:
            o = (c - 1) // 2
            s_c, s_r = L - c, Y - r
            require(q >= 0 and o >= 0 and r >= 0, (M, X, "sign"))
            require(s_c > 0 and s_r > 0, (M, X, "slacks"))
            require(Z == (q * L + 2 * o + 1) * Y + r, (M, X, "witness1"))
            require(2 * o + 1 + s_c == L, (M, X, "witness2"))
            require(r + s_r == Y, (M, X, "witness3"))
            valid_cases += 1
        cases += 1

outer_nodes = ["A", "A", "A", "A", "A", "M", "A", "M", "A", "M", "A", "A", "A"]
require(outer_nodes.count("M") == 3 and outer_nodes.count("A") == 10, "outer ledger")
receipt = {
    "checked_mask_pairs": cases,
    "checked_valid_witnesses": valid_cases,
    "outer": {"M": 3, "A": 10, "positive_internal_witnesses": 8, "equations": 3},
    "inherited_power_calls": 3,
    "inherited_power_receipt_each": {"M": 31, "A": 39, "positive_internal_witnesses": 25, "equations": 15},
    "complete": {"M": 96, "A": 127, "operations": 223, "positive_internal_witnesses": 83, "equations": 48},
    "scope": "Own finite coefficient/parity/witness checks; inherited POWER macro not executed",
}
print(json.dumps(receipt, indent=2))
