#!/usr/bin/env python3
"""Two fixed renamings with 11+13 reachable binary-stream control states.

u(z)=z+1; w(0)=1, w(1)=-1, w(z)=z-1 otherwise.
Intermediate h(0)=2,h(1)=0,h(z)=z otherwise equals the word wu.
All words act left to right.  Agreement is on finite LIVE names, not global
equality with finite permutations.  Support computation is needed only in
this external completeness compiler, not by the proposed proof checker.

Formula encoding and the standard four-generator finite-map factorization
come from ProveIt source 28, as documented in transport26.py and NOTICE.md.
The fixed maps, protected-hole routing and compiler here refine the preserved
26-control construction in transport26.py.  These counts are stream-transducer
control counts, NOT binary Turing-machine states or a complete checker.
"""
from __future__ import annotations

from collections import deque

from transport26 import (INIT, OLD_MODES, encode, encode_var, factor_four,
                        finish, free_names, rename, scalar as old_scalar,
                        shift, transition as old_transition)

THREE_MODES = frozenset("sSh")
TWO_MODES = frozenset("uw")


def scalar(mode: str, value: int) -> int:
    if mode == "h":
        return {0: 2, 1: 0}.get(value, value)
    if mode == "w":
        return {0: 1, 1: -1}.get(value, value - 1)
    return old_scalar(mode, value)


def evaluate(word: str, value: int) -> int:
    for mode in word:
        value = scalar(mode, value)
    return value


def apply_support(word: str, live: set[int]) -> set[int]:
    return {evaluate(word, x) for x in live}


def reduce_three(word: str) -> str:
    """Only the globally valid cancellations sS=Ss=identity are used."""
    out = []
    for mode in word:
        if mode not in THREE_MODES:
            raise ValueError("expected a three-mode h word")
        if out and (out[-1], mode) in (("s", "S"), ("S", "s")):
            out.pop()
        else:
            out.append(mode)
    return "".join(out)


def shifted_h(j: int) -> str:
    """Globally j->j+2 and j+1->j; all other integers fixed."""
    return shift(-j) + "h" + shift(j)


def swap_interval(lo: int, hi: int, i: int) -> str:
    """Swap i,i+1 on [lo,hi], keeping every other interval name fixed.

    Raw length is 2*m+3+abs(1-lo)+abs(hi), m=hi-lo+1.
    On [0,m-1] this is 3*m+3.  The hole proof is in two_map24_section.tex.
    """
    if not lo <= i < hi:
        raise ValueError("adjacent endpoints must lie in the interval")
    return (shift(1 - lo) + "h" + "Sh" * (i + 1 - lo)
            + "sh" + "Sh" * (hi - i) + shift(hi))


def swap_live(live: set[int], i: int) -> str:
    if not ({i, i + 1} & live):
        return ""
    if i + 2 not in live:
        return reduce_three(shift(-i) + "hSh" + shift(i + 1))
    lo, hi = min(live | {i}), max(live | {i + 1})
    return reduce_three(swap_interval(lo, hi, i))


def compile_four(word: str, live: set[int], *, with_certificate=False):
    """Old s,S,t,k -> s,S,h, maintaining pointwise agreement on entry names."""
    if any(mode not in OLD_MODES for mode in word):
        raise ValueError("invalid four-mode word")
    parts, certificate = [], []
    for mode in word:
        before = set(live)
        if mode in "sS":
            macro = mode
        elif mode == "t":
            macro = swap_live(live, 0)
        elif 0 not in live:
            macro = ""
        else:
            # (1 2), h, (0 1), (1 2) realizes 0->1 on the live set.
            macro_parts = []
            working = set(live)
            for instruction in (1, "h", 0, 1):
                piece = ("h" if instruction == "h"
                         else swap_live(working, instruction))
                macro_parts.append(piece)
                working = apply_support(piece, working)
            macro = "".join(macro_parts)
        live = {old_scalar(mode, x) for x in live}
        if any(evaluate(macro, x) != old_scalar(mode, x) for x in before):
            raise AssertionError("four-to-three pointwise mismatch")
        parts.append(macro)
        if with_certificate:
            certificate.append({"source": mode, "before": sorted(before),
                                "after": sorted(live), "macro": macro})
    answer = reduce_three("".join(parts))
    return (answer, certificate) if with_certificate else answer


def down_two(live: set[int]) -> str:
    """For x>=1,q>=x, w^q(x)=x-q-1; move the entire live interval across."""
    if not live:
        return ""
    a, c = max(0, 1 - min(live)), max(0, max(live))
    return "u" * a + "w" * (a + c) + "u" * c


def compile_three_to_two(word: str, live: set[int], *, with_certificate=False):
    if any(mode not in THREE_MODES for mode in word):
        raise ValueError("expected a three-mode h word")
    parts, certificate = [], []
    for mode in word:
        before = set(live)
        macro = "u" if mode == "s" else "wu" if mode == "h" else down_two(live)
        live = {scalar(mode, x) for x in live}
        if any(evaluate(macro, x) != scalar(mode, x) for x in before):
            raise AssertionError("three-to-two pointwise mismatch")
        parts.append(macro)
        if with_certificate:
            certificate.append({"source": mode, "before": sorted(before),
                                "after": sorted(live), "macro": macro})
    answer = "".join(parts)
    return (answer, certificate) if with_certificate else answer


def compile_four_to_two(word: str, live: set[int], *, with_certificate=False):
    if with_certificate:
        middle, first = compile_four(word, live, with_certificate=True)
        answer, second = compile_three_to_two(middle, live, with_certificate=True)
        return answer, {"four_to_three": first, "three_to_two": second,
                        "intermediate_word": middle}
    return compile_three_to_two(compile_four(word, live), live)


def factor_two(mapping: dict[int, int]) -> str:
    return compile_four_to_two(factor_four(mapping), set(mapping))


def transition(mode: str, state: tuple, bit: str) -> tuple[tuple, str]:
    if mode == "u":
        return old_transition(mode, state, bit)
    if mode != "w" or bit not in ("0", "1"):
        raise ValueError("expected u/w mode and binary input")
    phase = state[0]
    if phase == "tag":
        return ("tag2", bit), bit
    if phase == "tag2":
        return (("var", 1) if state[1] == bit == "1" else INIT), bit
    slot, done = state[1], finish(state[1])
    if phase == "var":
        return (("copy", slot) if bit == "0" else ("sign", slot)), bit
    if phase == "copy":
        return (("copy", slot) if bit == "1" else done), bit
    if phase == "sign":
        return (("copy", slot), "11") if bit == "1" else (("pending", slot), "")
    if phase == "pending":
        return (done, "010") if bit == "0" else (("second", slot), "")
    if phase == "second":
        return (done, "10") if bit == "0" else (("copy", slot), "01")
    raise ValueError("unreachable scanner state")


def transduce(mode: str, bits: str) -> str:
    state, parts = INIT, []
    for bit in bits:
        state, output = transition(mode, state, bit)
        parts.append(output)
    if state != INIT:
        raise ValueError("incomplete lexical token")
    return "".join(parts)


def table(mode: str) -> dict:
    labels, pending, rows = {INIT: 0}, deque([INIT]), []
    while pending:
        state = pending.popleft()
        for bit in "01":
            nxt, output = transition(mode, state, bit)
            if nxt not in labels:
                labels[nxt] = len(labels)
                pending.append(nxt)
            rows.append([labels[state], int(bit), output, labels[nxt]])
    return {"mode": mode, "states": len(labels), "initial": 0, "accepting": [0],
            "labels": [list(s) for s in labels], "rows": rows,
            "model": "deterministic variable-output binary stream transducer"}


def apply_stream_word(word: str, bits: str) -> str:
    for mode in word:
        bits = transduce(mode, bits)
    return bits


if __name__ == "__main__":
    import argparse
    import json

    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--word", help="source-28 word over s,S,t,k; left to right")
    source.add_argument("--map", help="finite map as a JSON object")
    parser.add_argument("--live", default="[]", help="JSON array of live signed names for --word")
    parser.add_argument("--certificate", action="store_true")
    args = parser.parse_args()
    if args.word is not None:
        live = set(json.loads(args.live))
        if any(type(x) is not int for x in live):
            parser.error("--live requires integer labels")
        source_word = args.word
    else:
        mapping = {int(x): y for x, y in json.loads(args.map).items()}
        if any(type(y) is not int for y in mapping.values()):
            parser.error("--map values must be integers")
        live, source_word = set(mapping), factor_four(mapping)
    result = compile_four_to_two(source_word, live, with_certificate=args.certificate)
    word, certificate = result if args.certificate else (result, None)
    output = {"word": word, "length": len(word), "live": sorted(live),
              "image": {x: evaluate(word, x) for x in sorted(live)}}
    if certificate is not None:
        output["certificate"] = certificate
    print(json.dumps(output, indent=2))
