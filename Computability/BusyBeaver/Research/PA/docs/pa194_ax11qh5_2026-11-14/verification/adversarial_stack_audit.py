#!/usr/bin/env python3
"""Independent integer audit of the AX11QH5 command interface.

This is a regression check of the mathematical interface, not a physical
machine or exact formula-emitter check. AX heads q_0,...,q_8 are replaced by
small representatives of their proved residue-zero contract; q_9 is the
actual U_5(d,h). This keeps integers manageable while testing canonical
Cantor stacks, including zero aliases, without a free-list implementation.
The universal proof is in ax11qh5_proof.tex and the symbolic checker.
"""
from itertools import product
from math import isqrt
from pathlib import Path
import argparse
import json


def pair(a, b):
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n):
    s = (isqrt(8 * n + 1) - 1) // 2
    b = n - s * (s + 1) // 2
    return s - b, b


def stack(values, tail):
    for value in reversed(values):
        tail = pair(value, tail)
    return tail


def implication(a, b):
    return 5 * pair(a, b)


def universal(i, a):
    return implication(a, i) + 2


def execute(word, initial, pattern=0):
    t, w, d, h = initial
    for op in word:
        if op[0] == "S":
            if h == 1:
                return None
            a, w = unpair(w)
            t, h = h, a
        elif op[0] == "MP":
            b = d + op[1]
            t, d, h = (b if implication(t, b) == h else 0), b, 0
        elif op[0] == "A":
            # Two deliberately different contract models: maximal zero
            # aliasing and mixtures of zero and positive implication tags.
            q = [0] * 9 if pattern == 0 else [5 * (j % 3) for j in range(9)]
            q.append(universal(d, h))
            w = stack(q + [t], w)
            t, d, h = 0, op[4], 0
        else:
            raise AssertionError(op)
    return t, w, d, h


S = ("S",)
A0 = ("A", 0, 0, 0, 0)
PUSH = [A0] + [S] * 10 + [("MP", 0)]
POP = [A0] + [S] * 12


def verify():
    checks = {}
    count = 0

    def equal(actual, expected):
        nonlocal count
        if actual != expected:
            raise AssertionError((actual, expected))
        count += 1

    for n in range(4096):
        a, b = unpair(n)
        equal(pair(a, b), n)
        equal(n == 0 or b < n, True)
    for a, b in product(range(64), repeat=2):
        equal(unpair(pair(a, b)), (a, b))
    checks["pairing_and_canonical_tail"] = count

    start = count
    # Non-empty notation can denote the numerical empty stack.
    for length in range(32):
        equal(stack([0] * length, 0), 0)
    for t, w, h in product(range(6), repeat=3):
        equal(execute([("MP", 0)], (t, w, 0, h)), (0, w, 0, 0))
        expected = None if h == 1 else (h, unpair(w)[1], 0, unpair(w)[0])
        equal(execute([S], (t, w, 0, h)), expected)
    for z, w in product(range(16), range(6)):
        equal(execute([("MP", z)], (0, w, 0, 0)), (0, w, z, 0))
    checks["zero_alias_and_branch_cases"] = count - start

    start = count
    for pattern, t, w, d, h in product(range(2), (0, 1, 2, 5), (0, 1, 2, 8), (0, 1), (0, 1)):
        initial = (t, w, d, h)
        equal(execute(PUSH, initial, pattern), (0, pair(t, w), 0, 0))
        expected = None if t == 1 else (t, unpair(w)[1], 0, unpair(w)[0])
        equal(execute(POP, initial, pattern), expected)
    checks["integer_push_pop_contract_models"] = count - start

    start = count
    for pattern, a, b, w in product(range(2), (0, 1, 2, 5), (0, 1, 2, 5), (0, 1, 2)):
        initial = (0, stack([a, implication(a, b), 0], w), 0, 0)
        expected = None if 1 in (a, b) else (b, w, 0, 0)
        equal(execute([S, S, ("MP", b)] + POP, initial, pattern), expected)
    checks["integer_mp_suffix_contract_models"] = count - start

    start = count
    for pattern, a, i, w in product(range(2), (0, 1, 2), (0, 1, 2), (0, 1)):
        gen = PUSH + [("MP", i), S, ("A", i, 0, 0, 0)] + [S] * 11
        equal(execute(gen, (a, w, 0, 0), pattern), (universal(i, a), w, 0, 0))
    checks["integer_generalization_contract_models"] = count - start

    return {
        "status": "PASS", "assertions": count, "groups": checks,
        "scope": "Finite integer regression of universal command-interface claims; AX formula heads abstracted only by their independently proved residue contract.",
        "not_claimed": ["Exact AX formula-emitter validation", "physical TM simulation", "new formal proof-assistant endpoint"],
        "canonical_stack": "Actual Cantor integers and total projections; all-zero pushes onto zero collapse to zero."
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = verify()
    rendered = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered)
    print(rendered)
