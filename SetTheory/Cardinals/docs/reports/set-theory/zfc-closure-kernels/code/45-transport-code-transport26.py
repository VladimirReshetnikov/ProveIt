#!/usr/bin/env python3
"""Two fixed free-name maps, complete on every finite set of live names.

First replace source 28's separate swap and contraction modes by
g(0)=1, g(1)=0, g(2)=0, g(z)=z otherwise, keeping shifts s and S.
Then use only u(z)=z+1 and v(z)=g(z)-1; finite-live orbit crossing
simulates decrement, while the word vu equals g globally.
All words act left to right.  Bound de Bruijn variables are always unchanged.

The finite-fiber/permutation factorization used as a four-mode control follows
ProveIt batch 152 source 28 (zfc_contraction_research, stream_renaming.py).
Finite transformation factorization and abstract two-generator existence are
classical.  The explicit simple maps and their support-aware compiler are
the contribution here; global permutations are NOT generated exactly.

This is a reference component, not a complete proof checker or Turing machine.
Python recursion/resource limits are not rejection outcomes of a semidecider.
"""
from __future__ import annotations

from collections import deque

NEW_MODES = frozenset("sSg")
TWO_MODES = frozenset("uv")
OLD_MODES = frozenset("sStk")


def scalar(mode: str, value: int) -> int:
    if mode in ("s", "u"):
        return value + 1
    if mode == "S":
        return value - 1
    if mode == "g":
        return {0: 1, 1: 0, 2: 0}.get(value, value)
    if mode == "v":
        return {0: 0, 1: -1, 2: -1}.get(value, value - 1)
    if mode == "t":
        return 1 - value if value in (0, 1) else value
    if mode == "k":
        return 1 if value == 0 else value
    raise ValueError("unknown map")


def evaluate(word: str, value: int) -> int:
    for mode in word:
        value = scalar(mode, value)
    return value


def shift(amount: int) -> str:
    return "s" * amount if amount >= 0 else "S" * -amount


def reduce_word(word: str) -> str:
    """Only globally valid rewrites: sS=Ss=identity and ggg=g."""
    result: list[str] = []
    for mode in word:
        if mode not in NEW_MODES:
            raise ValueError("expected a three-mode word")
        if result and (result[-1], mode) in (("s", "S"), ("S", "s")):
            result.pop()
        elif mode == "g" and result[-2:] == ["g", "g"]:
            result.pop()
        else:
            result.append(mode)
    return "".join(result)


def downward(j: int) -> str:
    """Globally fix every integer except j, which is sent to j-1."""
    return shift(2 - j) + "gg" + shift(j - 2)


def swap_interval(lo: int, hi: int, i: int) -> str:
    """Swap i and i+1 on [lo,hi]; behavior outside that interval is free.

    Before optional global word reduction this has the exact length
    3m-2+abs(2-lo)+abs(hi-1), m=hi-lo+1.  In particular length=4m-2
    when lo=0 and hi=m-1.  No rank loss occurs on the protected interval.
    """
    if not lo <= i < hi:
        raise ValueError("adjacent endpoints must lie in the interval")
    return (shift(2 - lo) + "gg" + "Sgg" * (i - lo) + "Sg"
            + "Sgg" * (hi - i - 1) + shift(hi - 1))


def swap_live(live: set[int], i: int) -> str:
    """A support-aware adjacent transposition, with a one-g hole shortcut."""
    if not ({i, i + 1} & live):
        return ""
    if i + 2 not in live:
        return reduce_word(shift(-i) + "g" + shift(i))
    lo = min(live | {i})
    hi = max(live | {i + 1})
    return reduce_word(swap_interval(lo, hi, i))


def apply_support(word: str, live: set[int]) -> set[int]:
    for mode in word:
        live = {scalar(mode, x) for x in live}
    return live


def compile_four(word: str, live: set[int], *, with_certificate=False):
    """Preserve a source-28 four-mode word on precisely the supplied names.

    The compiler updates live names after every old command.  A contraction
    0->1 is downward(1) followed by a support-aware swap of 0 and 1.
    Certificates identify each macro's entry/exit live set and exact word.
    """
    if any(mode not in OLD_MODES for mode in word):
        raise ValueError("invalid four-mode word")
    out: list[str] = []
    certificate = []
    for mode in word:
        before = set(live)
        if mode in "sS":
            macro = mode
        elif mode == "t":
            macro = swap_live(live, 0)
        else:
            if 0 not in live:
                macro = ""
            else:
                lower = downward(1)
                lowered = apply_support(lower, live)
                macro = lower + swap_live(lowered, 0)
        live = {scalar(mode, x) for x in live}
        if apply_support(macro, before) != live:
            raise AssertionError("macro support mismatch")
        # Agreement on actual names is stronger than support-set agreement.
        if any(evaluate(macro, x) != scalar(mode, x) for x in before):
            raise AssertionError("macro pointwise mismatch")
        out.append(macro)
        if with_certificate:
            certificate.append({"source": mode, "before": sorted(before),
                                "after": sorted(live), "macro": macro})
    answer = reduce_word("".join(out))
    return (answer, certificate) if with_certificate else answer


def old_adjacent(i: int) -> str:
    return shift(-i) + "t" + shift(i)


def old_swap(a: int, b: int) -> str:
    if a == b:
        return ""
    lo, hi = sorted((a, b))
    edges = list(range(lo, hi)) + list(range(hi - 2, lo - 1, -1))
    return "".join(old_adjacent(i) for i in edges)


def old_inverse(word: str) -> str:
    inv = {"s": "S", "S": "s", "t": "t"}
    return "".join(inv[x] for x in reversed(word))


def old_collapse(a: int, b: int) -> str:
    if a == b:
        return ""
    first = old_swap(a, 0)
    moved_b = a if b == 0 else b
    conjugator = first + old_swap(moved_b, 1)
    return conjugator + "k" + old_inverse(conjugator)


def factor_four(mapping: dict[int, int]) -> str:
    """Standard fiber-collapse then permutation completion; source-28 control."""
    if not mapping:
        return ""
    if any(type(x) is not int or type(y) is not int for x, y in mapping.items()):
        raise ValueError("integer labels required")
    fibers: dict[int, list[int]] = {}
    for x in sorted(mapping):
        fibers.setdefault(mapping[x], []).append(x)
    reps = {y: xs[0] for y, xs in fibers.items()}
    parts = [old_collapse(x, xs[0]) for xs in fibers.values() for x in xs[1:]]
    universe = sorted(set(mapping) | set(mapping.values()))
    perm = {x: y for y, x in reps.items()}
    perm.update(zip(sorted(set(universe) - set(perm)),
                    sorted(set(universe) - set(perm.values()))))
    current = {x: x for x in universe}
    for x in universe:
        old, target = current[x], perm[x]
        if old != target:
            parts.append(old_swap(old, target))
            current = {z: target if v == old else old if v == target else v
                       for z, v in current.items()}
    word = "".join(parts)
    if current != perm or word.count("k") != len(mapping) - len(set(mapping.values())):
        raise AssertionError("factorization error")
    return word


def factor_three(mapping: dict[int, int]) -> str:
    return compile_four(factor_four(mapping), set(mapping))


def down_two(live: set[int]) -> str:
    """Simulate global decrement on a finite support with only u and v.

    v(z)=g(z)-1.  For z>=2 and b>=z-1, v^b(z)=z-b-2.
    Choose a=max(0,2-min(live)), c=max(0,max(live)), b=a+c-1.
    Then u^a v^b u^c equals decrement at each live name; b>=0.
    The exact word length is 2*(a+c)-1.
    """
    if not live:
        return ""
    a = max(0, 2 - min(live))
    c = max(0, max(live))
    b = a + c - 1
    if b < 0:
        raise AssertionError("negative crossing count")
    return "u" * a + "v" * b + "u" * c


def compile_three_to_two(word: str, live: set[int], *, with_certificate=False):
    """Agreement on live names is propagated after every three-mode command."""
    if any(mode not in NEW_MODES for mode in word):
        raise ValueError("expected a three-mode word")
    parts, certificate = [], []
    for mode in word:
        before = set(live)
        macro = "u" if mode == "s" else "vu" if mode == "g" else down_two(live)
        live = {scalar(mode, x) for x in live}
        if any(evaluate(macro, x) != scalar(mode, x) for x in before):
            raise AssertionError("two-mode macro pointwise mismatch")
        parts.append(macro)
        if with_certificate:
            certificate.append({"source": mode, "before": sorted(before),
                                "after": sorted(live), "macro": macro})
    answer = "".join(parts)
    return (answer, certificate) if with_certificate else answer


def factor_two(mapping: dict[int, int]) -> str:
    return compile_three_to_two(factor_three(mapping), set(mapping))


def compile_four_to_two(word: str, live: set[int], *, with_certificate=False):
    """Compile a source-28 word directly; support analysis is off-machine only."""
    if with_certificate:
        middle, first = compile_four(word, live, with_certificate=True)
        answer, second = compile_three_to_two(middle, live, with_certificate=True)
        return answer, {"four_to_three": first, "three_to_two": second,
                        "intermediate_word": middle}
    return compile_three_to_two(compile_four(word, live), live)


# Compatible with source 28: prefix tags 00 bottom,01 implication,10 all,11 R.
# Bound field: 0 1^index 0. Free field: 1 sign 1^magnitude 0, with negative
# z represented by sign1 and magnitude -z-1.  Free maps leave bound fields fixed.
INIT = ("tag",)


def finish(slot: int) -> tuple:
    return ("var", 2) if slot == 1 else INIT


def transition(mode: str, state: tuple, bit: str) -> tuple[tuple, str]:
    """A deterministic variable-output binary stream transducer."""
    if mode == "u":
        mode = "s"
    if mode not in NEW_MODES | {"v"} or bit not in "01":
        raise ValueError("unknown mode or input bit")
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
        if (mode == "s" and bit == "0") or (mode in ("S", "v") and bit == "1"):
            return ("copy", slot), bit + "1"
        if mode == "g" and bit == "1":
            return ("copy", slot), "1"
        return ("pending", slot), ""
    if phase == "pending":
        if mode == "s":
            return ((done, "00") if bit == "0" else (("copy", slot), "1"))
        if mode == "S":
            return ((done, "10") if bit == "0" else (("copy", slot), "0"))
        output = "010" if mode == "g" else "00"
        return ((done, output) if bit == "0" else (("second", slot), ""))
    if phase == "second" and mode in ("g", "v"):
        output = "00" if mode == "g" else "10"
        return ((done, output) if bit == "0" else (("third", slot), ""))
    if phase == "third" and mode in ("g", "v"):
        small = "00" if mode == "g" else "10"
        large = "0111" if mode == "g" else "011"
        return ((done, small) if bit == "0" else (("copy", slot), large))
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


def encode_var(var: tuple) -> str:
    kind, value = var
    if type(value) is not int:
        raise ValueError("integer variable expected")
    if kind == "b" and value >= 0:
        return "0" + "1" * value + "0"
    if kind == "f":
        return "1" + ("0" + "1" * value if value >= 0 else "1" + "1" * (-value - 1)) + "0"
    raise ValueError("invalid variable")


def encode(formula: tuple) -> str:
    tag = formula[0]
    if tag == "bot":
        return "00"
    if tag == "rel":
        return "11" + encode_var(formula[1]) + encode_var(formula[2])
    if tag == "imp":
        return "01" + encode(formula[1]) + encode(formula[2])
    if tag == "all":
        return "10" + encode(formula[1])
    raise ValueError("unknown formula constructor")


def rename(formula: tuple, mapping) -> tuple:
    if formula[0] == "bot":
        return formula
    if formula[0] == "rel":
        return ("rel",) + tuple(("f", mapping(v[1])) if v[0] == "f" else v
                                for v in formula[1:])
    return (formula[0],) + tuple(rename(child, mapping) for child in formula[1:])


def free_names(formula: tuple) -> set[int]:
    if formula[0] == "bot":
        return set()
    if formula[0] == "rel":
        return {v[1] for v in formula[1:] if v[0] == "f"}
    return set().union(*(free_names(child) for child in formula[1:]))


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
    source.add_argument("--map", help='finite map as JSON, e.g. \'{"0":1,"1":0}\'')
    parser.add_argument("--live", default="[]", help="JSON array of live signed names for --word")
    parser.add_argument("--certificate", action="store_true")
    args = parser.parse_args()
    if args.word is not None:
        live = set(json.loads(args.live))
        if any(type(x) is not int for x in live):
            parser.error("--live requires integer labels")
        result = compile_four_to_two(args.word, live, with_certificate=args.certificate)
    else:
        mapping = {int(x): y for x, y in json.loads(args.map).items()}
        if any(type(y) is not int for y in mapping.values()):
            parser.error("--map values must be integers")
        live = set(mapping)
        result = compile_four_to_two(factor_four(mapping), live, with_certificate=args.certificate)
    word, certificate = result if args.certificate else (result, None)
    output = {"word": word, "length": len(word), "live": sorted(live),
              "image": {x: evaluate(word, x) for x in sorted(live)}}
    if certificate is not None:
        output["certificate"] = certificate
    print(json.dumps(output, indent=2))
