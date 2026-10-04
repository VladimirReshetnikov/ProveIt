#!/usr/bin/env python3
"""Own finite arithmetic tests, no upstream imports or execution."""
import json


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


and_cases = 0
for x in range(32):
    for y in range(32):
        T = 2 ** (x + y + 1)
        for z in range(min(x, y) + 1):
            a, b = x - z, y - z
            M = x + T * y + T * T * (a + b)
            Q = z + T * z + T * T * a
            formula = Q & M == Q
            require(formula == (z == x & y), (x, y, z, "AND formula"))
            and_cases += 1

spread_cases = 0
for k in range(1, 4):
    B = 2 ** k
    for n in range(1, 5):
        for s in range(n + 1, n + 4):
            P, C = B ** n, B ** (s - 1)
            E = C ** n
            D, F = B * C, E * P
            G1 = (E - 1) // (C - 1)
            G2 = (F - 1) // (D - 1)
            mask = (B - 1) * G2
            require((C - 1) * G1 == E - 1, (k, n, s, "G1"))
            require((D - 1) * G2 == F - 1, (k, n, s, "G2"))
            for U in range(P):
                W = (U * G1) & mask
                explicit = sum(((U // (B ** i)) % B) * (B ** (s * i)) for i in range(n))
                require(W == explicit, (k, n, s, U, "SPREAD"))
                require(0 <= W < B ** (s * n), (k, n, s, U, "output bound"))
                spread_cases += 1

receipt = {
    "and_small_triples": and_cases,
    "spread_full_digit_streams": spread_cases,
    "and_ledger": {"M": 132, "A": 177, "operations": 309, "positive_internal_witnesses": 111, "equations": 65, "POWER_calls": 4},
    "spread_supplied_radix_ledger": {"M": 231, "A": 302, "operations": 533, "positive_internal_witnesses": 193, "equations": 114, "POWER_calls": 7},
    "spread_internal_radix_ledger": {"M": 262, "A": 341, "operations": 603, "positive_internal_witnesses": 219, "equations": 129, "POWER_calls": 8},
    "scope": "Own semantic arithmetic checks; no upstream code or nested Pell witnesses executed",
}
print(json.dumps(receipt, indent=2))
