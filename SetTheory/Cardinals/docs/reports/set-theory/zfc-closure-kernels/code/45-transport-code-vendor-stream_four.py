#!/usr/bin/env python3
"""Four fixed streaming free-name maps for locally nameless formulas.

This is a reference component, NOT a binary Turing machine or state record.
The transducers read and write binary strings, but may emit zero or several
bits per input bit. Counts of their control states are transducer counts.

Formula tokens: 00 Bottom; 01 implication; 10 universal; 11 relation.
An atom is followed by two variable fields. A bound variable j is 0 1^j 0.
A free integer z is 1 sign 1^m 0, where sign=0,m=z for z>=0, and
sign=1,m=-z-1 otherwise. Formula children follow their prefix token.

Modes: s(z)=z+1; S(z)=z-1; t exchanges 0 and 1; k sends 0 to 1.
Every map fixes bound indices. No traversal of binders is necessary for
these free-name operations. A separate syntax check enforces tree shape
and scope; the finite-state scanner checks only lexical completion.
"""
from __future__ import annotations

from collections import deque
from typing import Any

MODES = ("s", "S", "t", "k")
INIT = ("tag",)


def scalar(mode: str, value: int) -> int:
    if mode == "s":
        return value + 1
    if mode == "S":
        return value - 1
    if mode == "t":
        return 1 - value if value in (0, 1) else value
    if mode == "k":
        return 1 if value == 0 else value
    raise ValueError("unknown mode")


def finish_field(slot: int) -> tuple:
    return ("var", 2) if slot == 1 else INIT


def transition(mode: str, state: tuple, bit: str) -> tuple[tuple, str]:
    """One deterministic input step; output is a (possibly empty) bit word."""
    if mode not in MODES or bit not in ("0", "1"):
        raise ValueError("unknown mode or input bit")
    phase = state[0]
    if phase == "tag":
        return ("tag2", bit), bit
    if phase == "tag2":
        return (("var", 1) if state[1] == bit == "1" else INIT), bit
    slot = state[1]
    done = finish_field(slot)
    if phase == "var":
        return (("copy", slot) if bit == "0" else ("sign", slot)), bit
    if phase == "copy":
        return (("copy", slot) if bit == "1" else done), bit
    if phase == "sign":
        if (mode == "s" and bit == "0") or (mode == "S" and bit == "1"):
            return ("copy", slot), bit + "1"
        if mode in ("t", "k") and bit == "1":
            return ("copy", slot), "1"
        return ("pending", slot), ""
    if phase == "pending":
        if mode == "s":  # negative: -1 -> 0; otherwise delete one magnitude bit
            return ((done, "00") if bit == "0" else (("copy", slot), "1"))
        if mode == "S":  # nonnegative: 0 -> -1; otherwise delete one magnitude bit
            return ((done, "10") if bit == "0" else (("copy", slot), "0"))
        if bit == "0":  # t and k both send 0 to 1
            return done, "010"
        if mode == "k":
            return ("copy", slot), "01"
        return ("second", slot), ""  # t must distinguish 1 from >=2
    if phase == "second" and mode == "t":
        return ((done, "00") if bit == "0" else (("copy", slot), "011"))
    raise ValueError("unreachable scanner state")


def transduce(mode: str, bits: str) -> str:
    state, output = INIT, []
    for bit in bits:
        state, word = transition(mode, state, bit)
        output.append(word)
    if state != INIT:
        raise ValueError("incomplete lexical token")
    return "".join(output)


def table(mode: str) -> dict[str, Any]:
    """Enumerate the reachable finite-state control graph exactly."""
    labels, queue = {INIT: 0}, deque([INIT])
    rows = []
    while queue:
        state = queue.popleft()
        for bit in "01":
            target, word = transition(mode, state, bit)
            if target not in labels:
                labels[target] = len(labels)
                queue.append(target)
            rows.append([labels[state], int(bit), word, labels[target]])
    return {"mode": mode, "states": len(labels), "initial": 0,
            "accepting": [0], "labels": [list(x) for x in labels], "rows": rows,
            "model": "deterministic variable-output binary stream transducer"}


def unary(n: int) -> str:
    if type(n) is not int or n < 0:
        raise ValueError("expected natural number")
    return "1" * n + "0"


def variable(v: tuple) -> str:
    tag, value = v
    if type(value) is not int:
        raise ValueError("variable label must be an integer")
    if tag == "b":
        return "0" + unary(value)
    if tag == "f":
        return "1" + ("0" + unary(value) if value >= 0 else "1" + unary(-value - 1))
    raise ValueError("unknown variable kind")


def encode(formula: tuple) -> str:
    tag = formula[0]
    if tag == "bot":
        return "00"
    if tag == "rel":
        return "11" + variable(formula[1]) + variable(formula[2])
    if tag == "imp":
        return "01" + encode(formula[1]) + encode(formula[2])
    if tag == "all":
        return "10" + encode(formula[1])
    raise ValueError("unknown formula constructor")


def decode(bits: str, depth: int = 0) -> tuple:
    """Parse exactly one formula and reject ill-scoped bound indices."""
    if any(bit not in "01" for bit in bits):
        raise ValueError("nonbinary input")
    pos = 0

    def bit():
        nonlocal pos
        if pos >= len(bits):
            raise ValueError("truncated bitstream")
        result = bits[pos]
        pos += 1
        return result

    def number():
        n = 0
        while bit() == "1":
            n += 1
        return n

    def term(level):
        if bit() == "0":
            j = number()
            if j >= level:
                raise ValueError("unbound de Bruijn index")
            return ("b", j)
        sign, n = bit(), number()
        return ("f", n if sign == "0" else -n - 1)

    def formula(level):
        tag = bit() + bit()
        if tag == "00":
            return ("bot",)
        if tag == "11":
            return ("rel", term(level), term(level))
        if tag == "01":
            return ("imp", formula(level), formula(level))
        return ("all", formula(level + 1))

    answer = formula(depth)
    if pos != len(bits):
        raise ValueError("trailing tokens")
    return answer


def rename(formula: tuple, name_map) -> tuple:
    """Independent structural specification, unrelated to scanner control."""
    tag = formula[0]
    if tag == "bot":
        return formula
    if tag == "rel":
        return (tag,) + tuple(("f", name_map(v[1])) if v[0] == "f" else v
                              for v in formula[1:])
    return (tag,) + tuple(rename(child, name_map) for child in formula[1:])


def free_names(formula: tuple) -> set[int]:
    if formula[0] == "bot":
        return set()
    if formula[0] == "rel":
        return {v[1] for v in formula[1:] if v[0] == "f"}
    return set().union(*(free_names(child) for child in formula[1:]))


def shift_word(amount: int) -> str:
    return ("s" * amount) if amount >= 0 else ("S" * (-amount))


def adjacent_swap(a: int) -> str:
    return shift_word(-a) + "t" + shift_word(a)


def swap_word(a: int, b: int) -> str:
    if a == b:
        return ""
    lo, hi = sorted((a, b))
    edges = list(range(lo, hi)) + list(range(hi - 2, lo - 1, -1))
    return "".join(adjacent_swap(i) for i in edges)


def inverse_permutation(word: str) -> str:
    inverse = {"s": "S", "S": "s", "t": "t"}
    try:
        return "".join(inverse[ch] for ch in reversed(word))
    except KeyError as exc:
        raise ValueError("word contains a noninvertible operation") from exc


def collapse_word(a: int, b: int) -> str:
    """Fix every integer except a, which is sent to b, using exactly one k."""
    if a == b:
        return ""
    first = swap_word(a, 0)
    moved_b = 0 if b == a else a if b == 0 else b
    conjugator = first + swap_word(moved_b, 1)
    return conjugator + "k" + inverse_permutation(conjugator)


def evaluate_word(word: str, value: int) -> int:
    for mode in word:
        value = scalar(mode, value)
    return value


def factor_names(mapping: dict[int, int]) -> str:
    """Realize a finite partial map, with exactly |domain|-|image| k steps.

    Only the supplied domain is prescribed. Other names may move, but only
    finitely many of them. For a formula, supply its actual free-name set.
    """
    if any(type(a) is not int or type(b) is not int for a, b in mapping.items()):
        raise ValueError("integer names required")
    if not mapping:
        return ""
    fibers: dict[int, list[int]] = {}
    for source in sorted(mapping):
        fibers.setdefault(mapping[source], []).append(source)
    reps = {target: sources[0] for target, sources in fibers.items()}
    word = "".join(collapse_word(source, sources[0])
                   for sources in fibers.values() for source in sources[1:])
    universe = sorted(set(mapping) | set(mapping.values()))
    permutation = {rep: target for target, rep in reps.items()}
    unused_domain = sorted(set(universe) - set(permutation))
    unused_range = sorted(set(universe) - set(permutation.values()))
    permutation.update(zip(unused_domain, unused_range))
    current = {a: a for a in universe}
    for a in universe:
        old, desired = current[a], permutation[a]
        if old == desired:
            continue
        word += swap_word(old, desired)
        current = {x: desired if y == old else old if y == desired else y
                   for x, y in current.items()}
    if current != permutation:
        raise AssertionError("internal permutation construction failure")
    if word.count("k") != len(mapping) - len(set(mapping.values())):
        raise AssertionError("wrong contraction count")
    return word


def apply_word(word: str, bits: str) -> str:
    for mode in word:
        bits = transduce(mode, bits)
    return bits
