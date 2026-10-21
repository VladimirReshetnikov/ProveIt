#!/usr/bin/env python3
"""Concrete mathematical source-level counterexample for the local-7 fold.

This file checks the identified macro substitution, using the accepted
K218 macro contracts. It does not certify a physical binary table or its
blank run. The surrounding report proves the arbitrary-input statement.
"""
import json


def pair(a, b):
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n):
    from math import isqrt
    s = (isqrt(8 * n + 1) - 1) // 2
    b = n - s * (s + 1) // 2
    return s - b, b


def replacement(t, w, d, h):
    # Every PUSH/I/a/b macro starts and ends with X=Y=0. H and D are
    # retained by all of them. The sole terminal '+' changes only T.
    words = ["PUSH", "+", "I", "I", "+", "+", "PUSH", "+",
             "I", "a", "b", "I", "+"]
    for word in words:
        if word == "PUSH":
            t, w = 0, pair(t, w)
        elif word == "+":
            t += 1
        elif word == "I":
            head, w = unpair(w)
            t = 4 * pair(head, t)
        elif word == "a":
            t, w = d, pair(t, w)
        elif word == "b":
            t, w = h, pair(t, w)
        else:
            raise AssertionError(word)
    return t, w, d, h, 0, 0


def main():
    # After an AX reset and an MP(1) input, the early I constructor creates
    # I(old_T,1). Choose old_T=W=0 for a small explicit witness.
    t, w, d, h, x, y = replacement(4 * pair(0, 1), 0, 1, 0)
    assert (t, d, h, x, y) == (5, 1, 0, 0, 0)
    after_replacement = dict(T=t, W=w, D=d, H=h, X=x, Y=y)
    # The following equality test compares H and X, now both zero. It takes
    # its success continuation 'a', which pushes current T and copies D.
    assert h == x
    t, w = d, pair(t, w)
    assert t == 1
    after_wrong_MP = dict(T=t, W=w, D=d, H=0)
    # DROP; NIP; NIP halts, regardless of the preceding contents of W.
    t, w = h, pair(t, w)
    assert h != 1
    h, w = unpair(w)
    assert h == 1
    print(json.dumps({
        "status": "PASS_SOURCE_COUNTEREXAMPLE",
        "old_source_prefix": "11101",
        "old_macro": "MOVE(T,X)",
        "new_macro": ["PUSH", "+", "I", "I", "+", "+", "PUSH", "+", "I", "a", "b", "I", "+"],
        "after_replacement": after_replacement,
        "after_wrong_MP": after_wrong_MP,
        "suffix": ["DROP", "NIP", "NIP"],
        "suffix_halts": True,
        "scope": "Identified source-macro substitution only, using inherited macro contracts. No independent binary-refinement or blank-run claim.",
    }, indent=2))


if __name__ == "__main__":
    main()
