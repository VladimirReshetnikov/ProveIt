"""Canonical total base-three formula codec, with independent finite checks.

This is an executable companion to the mathematical argument in
base3_codec_note.tex, not a proof-assistant verification of the machine.
"""
from functools import lru_cache
from itertools import product
from math import isqrt
from pathlib import Path
import hashlib
import json

TOP = ("top",)


def pair(a, b):
    s = a+b
    return s*(s+1)//2+b


def unpair(n):
    s = (isqrt(8*n+1)-1)//2
    b = n-s*(s+1)//2
    return s-b, b


def implication(a, b):
    return TOP if a == TOP and b == TOP else ("imp", a, b)


@lru_cache(None)
def decode(n):
    if n == 0:
        return TOP
    k, r = divmod(n, 3)
    a, b = unpair(k)
    if r == 0:
        assert a < n and b < n and (a,b) != (0,0)
        return ("imp", decode(a), decode(b))
    if r == 1:
        return ("mem", a, b)
    assert b < n
    return ("all", a, decode(b))


def encode(f):
    if f == TOP:
        return 0
    kind, a, b = f
    if kind == "mem":
        return 3*pair(a,b)+1
    if kind == "all":
        return 3*pair(a,encode(b))+2
    assert kind == "imp" and (a,b) != (TOP,TOP)
    return 3*pair(encode(a),encode(b))


def labels(f):
    if f == TOP:
        return set()
    kind, a, b = f
    if kind == "mem":
        return {a,b}
    if kind == "all":
        return {a} | labels(b)
    return labels(a) | labels(b)


def main():
    upto = 100000
    largest_depth = 0
    for n in range(upto):
        a, b = unpair(n)
        assert pair(a,b) == n
        f = decode(n)
        assert encode(f) == n
        assert all(i < n for i in labels(f))
        assert (f == TOP) == (n == 0)
    cases = 0
    for a,b in product(range(64), repeat=2):
        assert decode(3*pair(a,b)) == implication(decode(a),decode(b))
        assert decode(3*pair(a,b)+1) == ("mem",a,b)
        assert decode(3*pair(a,b)+2) == ("all",a,decode(b))
        cases += 3
    # Independent triangular enumeration verifies the closed-form unpairing.
    triangular_cases = 0
    for s in range(256):
        for b in range(s+1):
            a = s-b
            assert unpair(s*(s+1)//2+b) == (a,b)
            triangular_cases += 1
    # Normalization is transparent under both Boolean values of each child.
    semantic_cases = 0
    for a,b in product((False,True), repeat=2):
        ordinary = (not a) or b
        normalized = True if a and b else ordinary
        assert ordinary == normalized
        semantic_cases += 1
    result = {"integers_roundtripped_and_freshness_checked": upto,
        "constructor_contract_cases": cases,
        "independent_triangular_unpair_cases": triangular_cases,
        "truth_normalization_boolean_cases": semantic_cases,
        "code_zero_decodes_to_label_free_truth": decode(0)==TOP and not labels(decode(0)),
        "only_nonliteral_constructor_case": "Imp(code0,code0) decodes as Truth",
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "formal_Lean_verification": False,
        "compiler_or_calculus_calibration_claimed": False}
    out = Path(__file__).with_name("base3-codec-results.json")
    out.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))


if __name__ == "__main__":
    main()
