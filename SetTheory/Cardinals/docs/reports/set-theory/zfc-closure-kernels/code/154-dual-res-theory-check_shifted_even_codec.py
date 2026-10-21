#!/usr/bin/env python3
"""Arithmetic regressions for the directly calibrated shifted-even codec.

The all-natural argument is in shifted_even_codec.md. This finite receipt
is not a proof of the Hilbert calibration or a source/machine certificate.
"""
from itertools import product
from math import isqrt
from pathlib import Path
import json

if not __debug__:
    raise RuntimeError("Run without Python optimization: assertions are checks")


def pair(a, b):
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n):
    s = (isqrt(8 * n + 1) - 1) // 2
    b = n - s * (s + 1) // 2
    return s - b, b


def imp(a, b):
    return max(0, 4 * pair(a, b) - 2)


def quant(a, b):
    return 4 * pair(a, b)


def neg(a):
    return imp(a, 1)


def decode(h):
    return unpair(h // 4 + (h % 4 == 2))


def run():
    fields = 0
    for a, b in product(range(129), repeat=2):
        for constructor in (imp, quant):
            h = constructor(a, b)
            assert decode(h) == (a, b)
            assert h > max(a, b) if h else (a == b == 0)
            fields += 1
    code_cases = 0
    for h in range(100001):
        a, b = decode(h)
        if h % 4 == 0:
            assert quant(a, b) == h
        elif h % 4 == 2:
            assert imp(a, b) == h
        code_cases += 1
    assert imp(0, 0) == quant(0, 0) == 0
    assert neg(0) == 6 and neg(neg(0)) == 114
    assert all(neg(neg(a)) >= 114 for a in range(10001))
    return {
        "status": "SHIFTED_EVEN_CODEC_ARITHMETIC_REGRESSIONS_PASS",
        "field_checks": fields,
        "natural_code_cases": code_cases,
        "zero_alias": "I*(0,0)=Q*(0,0)=0, semantically truth",
        "minimum_double_negation_code": 114,
        "decoder": "unP(floor(h/4)+[h mod 4=2])",
        "exact_on": ["I*", "Q*"],
        "unconstrained_on": ["R", "J"],
        "scope": "Finite arithmetic regression; the unbounded argument is in shifted_even_codec.md. Not a native-calculus formalization or machine certificate."
    }


if __name__ == "__main__":
    result = run()
    Path(__file__).with_name("shifted_even_codec_receipt.json").write_text(
        json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
