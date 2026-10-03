#!/usr/bin/env python3
"""Finite radius-two lazy CA for the fixed 15-state, 2-symbol U15 table.

This file is newly authored; it does not execute upstream implementation code.
State IDs: t0=0, t1=1, h(A,0)=2, ..., h(O,1)=31, FL=32, FR=33.
Lazy is -1. Pattern wildcard is -2. The sole final head state is h(J,1)=21.
iter_rules() is the literal, deterministic, finite rule generator.
"""
from __future__ import annotations
from collections import Counter
from dataclasses import dataclass
from itertools import product
from typing import Iterator, Mapping
import argparse
import gzip
import hashlib
import json
from pathlib import Path

Q = "ABCDEFGHIJKLMNO"
LAZY = -1
STAR = -2
FL = 32
FR = 33
HALT = 21
S = tuple(range(34))
TAU = tuple(s for s in S if s != HALT)
# (written bit, head displacement, successor state), or no transition.
DELTA = {
    "A0": (0, 1, "B"), "A1": (1, 1, "A"),
    "B0": (1, 1, "C"), "B1": (1, 1, "A"),
    "C0": (0, -1, "G"), "C1": (0, -1, "E"),
    "D0": (0, -1, "F"), "D1": (1, -1, "E"),
    "E0": (1, 1, "A"), "E1": (1, -1, "D"),
    "F0": (1, -1, "D"), "F1": (1, -1, "D"),
    "G0": (0, -1, "H"), "G1": (1, -1, "G"),
    "H0": (1, -1, "I"), "H1": (1, -1, "G"),
    "I0": (0, 1, "A"), "I1": (1, -1, "J"),
    "J0": (1, -1, "K"), "J1": None,
    "K0": (0, 1, "L"), "K1": (1, 1, "N"),
    "L0": (0, 1, "M"), "L1": (1, 1, "L"),
    "M0": (0, -1, "B"), "M1": (1, 1, "L"),
    "N0": (0, -1, "C"), "N1": (0, 1, "O"),
    "O0": (0, 1, "N"), "O1": (1, 1, "N"),
}


def head(q: str, bit: int) -> int:
    return 2 + 2 * Q.index(q) + bit


def head_parts(state: int) -> tuple[str, int]:
    if not 2 <= state <= 31:
        raise ValueError("Not a headed state")
    return Q[(state - 2) // 2], (state - 2) % 2


def state_name(s: int) -> str:
    if s == LAZY:
        return "lazy"
    if s == STAR:
        return "*"
    if s in (0, 1):
        return f"t{s}"
    if s in (FL, FR):
        return "FL" if s == FL else "FR"
    q, bit = head_parts(s)
    return f"h{q}{bit}"


@dataclass(frozen=True)
class Rule:
    pattern: tuple[int, int, int, int, int]
    output: int
    family: str

    def matches(self, neighborhood: tuple[int, ...]) -> bool:
        return all(a == STAR or a == b for a, b in zip(self.pattern, neighborhood))

    @property
    def inputs(self) -> tuple[tuple[int, int], ...]:
        return tuple((k - 2, s) for k, s in enumerate(self.pattern) if s != STAR)


def iter_rules() -> Iterator[Rule]:
    """Exactly 388146 rules, in a fixed order, using only positive state tests."""
    transitions = [(q, g, DELTA[q + str(g)]) for q in Q for g in (0, 1)
                   if DELTA[q + str(g)] is not None]
    for q, g, (write, direction, nxt) in transitions:
        for a, u, v, b in product(TAU, (0, 1), (0, 1), TAU):
            yield Rule((a, u, head(q, g), v, b), write, "head_center")
    for a, u, v, w, b in product(TAU, (0, 1), (0, 1), (0, 1), TAU):
        yield Rule((a, u, v, w, b), v, "no_head")
    for u, v, b in product((0, 1), (0, 1), TAU):
        yield Rule((STAR, FL, u, v, b), u, "left_adjacent")
    for v, b in product((0, 1), TAU):
        yield Rule((STAR, STAR, FL, v, b), 0, "left_blank")
    for a, u, v in product(TAU, (0, 1), (0, 1)):
        yield Rule((a, u, v, FR, STAR), v, "right_adjacent")
    for a, u in product(TAU, (0, 1)):
        yield Rule((a, u, FR, STAR, STAR), 0, "right_blank")
    for b in TAU:
        yield Rule((STAR, STAR, STAR, FL, b), FL, "left_move")
    for a in TAU:
        yield Rule((a, FR, STAR, STAR, STAR), FR, "right_move")
    for q, g, (write, direction, nxt) in transitions:
        for a, u, v, b in product(TAU, (0, 1), (0, 1), TAU):
            out = head(nxt, v) if direction == -1 else v
            yield Rule((a, u, v, head(q, g), b), out, "head_right")
            out = head(nxt, u) if direction == 1 else u
            yield Rule((a, head(q, g), u, v, b), out, "head_left")


class CompiledRules:
    """Exact pattern-matching engine, including malfunction detection.

    Rules are grouped by their wildcard mask; this merely indexes iter_rules,
    and does not replace the CA rules with a different transition algorithm.
    """
    def __init__(self):
        self.groups: dict[tuple[int, ...], dict[tuple[int, ...], Rule]] = {}
        self.counts: Counter[str] = Counter()
        for rule in iter_rules():
            positions = tuple(i for i, s in enumerate(rule.pattern) if s != STAR)
            key = tuple(rule.pattern[i] for i in positions)
            group = self.groups.setdefault(positions, {})
            if key in group:
                raise AssertionError("Duplicate literal partial-rule pattern")
            group[key] = rule
            self.counts[rule.family] += 1

    def matching(self, neighborhood: tuple[int, ...]) -> list[Rule]:
        out = []
        for pos, group in self.groups.items():
            rule = group.get(tuple(neighborhood[i] for i in pos))
            if rule is not None:
                out.append(rule)
        return out

    def step(self, cells: Mapping[int, int]) -> dict[int, int]:
        if not cells:
            return {}
        out = {}
        # Radius two suffices; every rule has at least one nonwildcard input.
        for x in range(min(cells) - 2, max(cells) + 3):
            neighborhood = tuple(cells.get(x + k, LAZY) for k in range(-2, 3))
            matches = self.matching(neighborhood)
            if len(matches) > 1:
                raise RuntimeError(f"CA malfunction at x={x}: {matches!r}")
            if matches:
                out[x] = matches[0].output
        return out


def initialize(tape: Mapping[int, int], initial_state: str = "A",
               extent: tuple[int, int] | None = None) -> tuple[dict[int, int], int, int]:
    """All unlisted tape cells are zero; the initial head position is zero.

    extent=[a,b] can preserve leading/trailing zeroes in the declared input.
    It must contain 0 and every nonzero tape cell. Its span n=b-a+1 controls
    the size bound. With no extent, use the smallest such interval.
    """
    if initial_state not in Q or any(bit not in (0, 1) for bit in tape.values()):
        raise ValueError("Expected a U15 state and binary tape")
    nonzero = [x for x, bit in tape.items() if bit]
    if extent is None:
        a, b = min([0] + nonzero), max([0] + nonzero)
    else:
        a, b = extent
        if not a <= 0 <= b or any(not a <= x <= b for x in nonzero):
            raise ValueError("Input extent must contain 0 and the nonzero support")
    left, right = min(-3, a - 1), max(3, b + 1)
    cells = {x: tape.get(x, 0) for x in range(left + 1, right)}
    cells[0] = head(initial_state, tape.get(0, 0))
    cells[left], cells[right] = FL, FR
    return cells, left, right


def initialize_word(word: str, initial_state: str = "A"):
    if any(bit not in "01" for bit in word):
        raise ValueError("Expected a binary word")
    return initialize({i: int(bit) for i, bit in enumerate(word)}, initial_state,
                      extent=(0, max(0, len(word) - 1)))



def initialize_pair(ell: str, right_word: str):
    """Report32 tape convention: both sides nearest-head-first, A scans 0.

    ell[i] is at -i-1; right_word[i] is at i+1. The extent preserves all
    supplied digits, including boundary zeros, and the central zero.
    """
    if any(bit not in "01" for bit in ell + right_word):
        raise ValueError("Expected two binary words")
    tape = {-(i + 1): int(bit) for i, bit in enumerate(ell)}
    tape.update({i + 1: int(bit) for i, bit in enumerate(right_word)})
    tape[0] = 0
    return initialize(tape, "A", extent=(-len(ell), len(right_word)))


def parse_pair(serialized: str) -> tuple[str, str]:
    """Parse the finite binary grammar 1^len(ell) 0 ell right_word."""
    if any(bit not in "01" for bit in serialized):
        raise ValueError("Expected binary serialization")
    split = serialized.find("0")
    if split < 0 or len(serialized) - split - 1 < split:
        raise ValueError("Invalid length-prefixed pair")
    payload = serialized[split + 1:]
    return payload[:split], payload[split:]


def serialize_pair(ell: str, right_word: str) -> str:
    if any(bit not in "01" for bit in ell + right_word):
        raise ValueError("Expected two binary words")
    return "1" * len(ell) + "0" + ell + right_word


def initialize_serialized_pair(serialized: str):
    return initialize_pair(*parse_pair(serialized))


def tm_step(tape: dict[int, int], state: str, position: int):
    """One U15 step, or None exactly on J1; tape mutates only on a step."""
    transition = DELTA[state + str(tape.get(position, 0))]
    if transition is None:
        return None
    write, direction, nxt = transition
    tape[position] = write
    return nxt, position + direction


def shutdown_bounds(left: int, right: int, time: int, position: int) -> dict[str, int]:
    """Exact extinction and visited-coordinate bounds for a halt (T,p)."""
    if not left <= -3 or not right >= 3 or abs(position) > time:
        raise ValueError("Parameters incompatible with this initialization")
    dl = position - left + time
    dr = right + time - position
    return {
        "left_halt_distance": dl,
        "right_halt_distance": dr,
        "first_all_lazy_time": time + max(dl, dr),
        "min_active_x": 2 * left - 2 * time - position + 1,
        "max_active_x": 2 * right + 2 * time - position - 1,
        "active_spacetime_cells": ((time + 1) * (right - left + 1 + time)
                                    + dl * (dl - 1) // 2 + dr * (dr - 1) // 2),
    }


def manifest() -> dict:
    counts, arities, incidences = Counter(), Counter(), 0
    output_counts, input_counts = Counter(), Counter()
    offset_input_counts = {k: Counter() for k in range(-2, 3)}
    digest = hashlib.sha256()
    for i, rule in enumerate(iter_rules()):
        counts[rule.family] += 1
        arities[len(rule.inputs)] += 1
        incidences += len(rule.inputs)
        output_counts[rule.output] += 1
        for offset, state in rule.inputs:
            input_counts[state] += 1
            offset_input_counts[offset][state] += 1
        digest.update((json.dumps([i, list(rule.pattern), rule.output],
                                  separators=(",", ":")) + "\n").encode())
    return {
        "name": "U15 Cairns-family lazy cellular automaton",
        "radius": 2,
        "states": {str(s): state_name(s) for s in S},
        "active_state_count": len(S),
        "lazy_state": LAZY,
        "pattern_wildcard": STAR,
        "halting_head_state": HALT,
        "nonfinal_state_count": len(TAU),
        "rule_count": sum(counts.values()),
        "rule_family_counts": dict(counts),
        "rule_input_arity_counts": dict(sorted(arities.items())),
        "one_hot_input_incidences": incidences,
        "one_hot_output_incidences": sum(counts.values()),
        "producer_count_by_state_m_s": {str(s): output_counts[s] for s in S},
        "input_occurrence_count_by_state_f_s": {str(s): input_counts[s] for s in S},
        "input_count_by_offset_and_state": {str(k): {str(s): offset_input_counts[k][s] for s in S}
                                            for k in range(-2, 3)},
        "canonical_integer_rules_jsonl_sha256": digest.hexdigest(),
        "all_lazy_is_fixed": True,
        "all_rules_have_positive_arity": True,
        "initialization": "See initialize() and initialize_word()",
        "proof": "SEMANTICS_AND_BOUNDS.md",
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", type=Path)
    parser.add_argument("--rules-jsonl", type=Path,
                        help="Canonical rows [rule_id,[five pattern IDs],output ID]; .gz allowed")
    args = parser.parse_args()
    result = manifest()
    if args.manifest:
        args.manifest.write_text(json.dumps(result, indent=2) + "\n")
    else:
        print(json.dumps(result, indent=2))
    if args.rules_jsonl:
        opener = gzip.open if args.rules_jsonl.suffix == ".gz" else open
        with opener(args.rules_jsonl, "wt") as f:
            for i, rule in enumerate(iter_rules()):
                f.write(json.dumps([i, list(rule.pattern), rule.output],
                                   separators=(",", ":")) + "\n")


if __name__ == "__main__":
    main()
