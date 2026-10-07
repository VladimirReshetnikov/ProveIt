#!/usr/bin/env python3
"""Exact semantic differential audit of the sparse-slot matching construction.

For each deterministic two-way finite automaton, this program constructs FOUR
local perfect matchings, one per scanned symbol 0, 1, L, R.  It builds the lane
wiring, contracts that wiring inside each individual cell, and multiplies the
resulting Brauer diagrams.  Acceptance of these products is compared with a
direct configuration-by-configuration run of the ORIGINAL automaton.

The test includes all 288 legal one-state machines (all partial transition
functions, both accepting subsets) and 512 reproducibly sampled two-state
machines, on every binary word of length at most five.  Empty input, initial
acceptance, undefined transitions, stay moves, and infinite rejecting runs are
included.  No global configuration graph is used to construct a diagram.

Run:
    python3 -O code/sparse_slots_audit.py \
        --output reproduced/sparse_slots_audit.json

Requires only Python's standard library and the adjacent brauer_audit.py.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
from itertools import product
import json
from pathlib import Path
import random
from typing import Hashable, Iterator, Sequence

from brauer_audit import AuditFailure, multiply, require


SYMBOLS = ("0", "1", "L", "R")
Transition = tuple[int, int] | None  # (destination state, head displacement)
Slot = tuple[int, int, int]  # (head displacement, source state, target state)


@dataclass(frozen=True)
class Machine:
    states: int
    accepting: frozenset[int]
    # Symbol-major, then source state; state 0 is always the initial state.
    transition_rows: tuple[tuple[Transition, ...], ...]

    def transition(self, state: int, symbol: str) -> Transition:
        return self.transition_rows[SYMBOLS.index(symbol)][state]

    def description(self) -> dict[str, object]:
        return {
            "states": self.states,
            "accepting": sorted(self.accepting),
            "transitions": dict(zip(SYMBOLS, self.transition_rows)),
        }


def modified_transition(machine: Machine, state: int, symbol: str) -> Transition:
    """Add f, redirect every accepting state to f by a stay, then sweep right."""
    sink_state = machine.states
    if state == sink_state:
        return None if symbol == "R" else (sink_state, 1)
    if state in machine.accepting:
        return sink_state, 0
    return machine.transition(state, symbol)


def candidate_slots(machine: Machine) -> tuple[Slot, ...]:
    slots = set()
    for state in range(machine.states + 1):
        for symbol in SYMBOLS:
            transition = modified_transition(machine, state, symbol)
            if transition is not None:
                target, direction = transition
                if direction:
                    slots.add((direction, state, target))
    require(bool(slots), "The sink sweep must supply at least one slot")
    require(len(slots) <= 4 * machine.states + 1, "Sparse-slot bound failed")
    return tuple(sorted(slots))


class Wiring:
    """A local degree-two wire graph with numbered exposed boundary ports."""

    def __init__(self, ports: int) -> None:
        self.ports = ports
        self.adjacency: list[list[int]] = [[] for _ in range(ports)]
        self.incidences: dict[Hashable, list[tuple[int, int]]] = {}

    def node(self) -> int:
        self.adjacency.append([])
        return len(self.adjacency) - 1

    def edge(self, a: int, b: int) -> None:
        self.adjacency[a].append(b)
        self.adjacency[b].append(a)

    def incidence(self, vertex: Hashable) -> tuple[int, int]:
        incoming, outgoing = self.node(), self.node()
        self.incidences.setdefault(vertex, []).append((incoming, outgoing))
        return incoming, outgoing

    def cyclic_joins(self) -> None:
        # This insertion order depends only on the symbol, its own transition
        # row, and the globally fixed slot order, never on neighbors or length.
        for incidences in self.incidences.values():
            for i, (incoming, _) in enumerate(incidences):
                next_outgoing = incidences[(i + 1) % len(incidences)][1]
                self.edge(incoming, next_outgoing)

    def contract(self) -> tuple[int, ...]:
        for node, neighbors in enumerate(self.adjacency):
            expected = 1 if node < self.ports else 2
            require(
                len(neighbors) == expected,
                f"Local wiring node {node} has degree {len(neighbors)}, not {expected}",
            )
        visited = set()
        mate = [-1] * self.ports
        for start in range(len(self.adjacency)):
            if start in visited:
                continue
            visited.add(start)
            stack, boundary = [start], []
            while stack:
                node = stack.pop()
                if node < self.ports:
                    boundary.append(node)
                for neighbor in self.adjacency[node]:
                    if neighbor not in visited:
                        visited.add(neighbor)
                        stack.append(neighbor)
            if not boundary:
                continue  # A closed local wire has no effect on the matching.
            require(len(boundary) == 2, f"Bad local path endpoints: {boundary}")
            a, b = boundary
            mate[a], mate[b] = b, a
        require(all(v >= 0 for v in mate), "A local boundary port is unmatched")
        return tuple(mate)


def local_diagram(machine: Machine, symbol: str, slots: Sequence[Slot]) -> tuple[int, ...]:
    """Construct eta(symbol), using no input word or neighboring symbol."""
    k = 2 * len(slots)
    wire = Wiring(2 * k)
    inward_sides = ("right",) if symbol == "L" else (
        ("left",) if symbol == "R" else ("left", "right")
    )

    for side in inward_sides:
        offset = 0 if side == "left" else k
        for index, (direction, source, target) in enumerate(slots):
            source_here = (side == "right" and direction == 1) or (
                side == "left" and direction == -1
            )
            if source_here:
                if modified_transition(machine, source, symbol) == (target, direction):
                    vertex: Hashable = ("state", source)
                else:
                    vertex = ("unused_slot_leaf", side, index)
            else:
                vertex = ("state", target)
            incoming, outgoing = wire.incidence(vertex)
            right_lane, left_lane = offset + 2 * index, offset + 2 * index + 1
            if side == "left":
                wire.edge(right_lane, incoming)
                wire.edge(left_lane, outgoing)
            else:
                wire.edge(right_lane, outgoing)
                wire.edge(left_lane, incoming)

    # Every actual stay edge is internal.  A self-loop still receives TWO
    # distinct incidences, which is essential for the tour convention.
    for source in range(machine.states + 1):
        transition = modified_transition(machine, source, symbol)
        if transition is not None and transition[1] == 0:
            target = transition[0]
            a_in, a_out = wire.incidence(("state", source))
            b_in, b_out = wire.incidence(("state", target))
            wire.edge(a_out, b_in)
            wire.edge(b_out, a_in)

    if symbol == "L":
        incoming, outgoing = wire.incidence(("state", 0))
        wire.edge(0, incoming)
        wire.edge(1, outgoing)
        for port in range(2, k, 2):
            wire.edge(port, port + 1)
    elif symbol == "R":
        incoming, outgoing = wire.incidence(("state", machine.states))
        wire.edge(k, outgoing)
        wire.edge(k + 1, incoming)
        for port in range(k + 2, 2 * k, 2):
            wire.edge(port, port + 1)

    wire.cyclic_joins()
    return wire.contract()


def direct_acceptance(machine: Machine, word: str) -> tuple[bool, str, int]:
    tape = ("L",) + tuple(word) + ("R",)
    position, state, steps = 0, 0, 0
    seen = set()
    while True:
        if state in machine.accepting:
            return True, "accept_initial" if steps == 0 else "accept_later", steps
        configuration = position, state
        if configuration in seen:
            return False, "reject_loop", steps
        seen.add(configuration)
        transition = machine.transition(state, tape[position])
        if transition is None:
            return False, "reject_undefined", steps
        state, direction = transition
        position += direction
        require(0 <= position < len(tape), "Original machine crossed an endmarker")
        steps += 1


def diagram_acceptance(diagrams: dict[str, tuple[int, ...]], word: str) -> bool:
    result = diagrams["L"]
    for symbol in tuple(word) + ("R",):
        result = multiply(result, diagrams[symbol])
    k = len(result) // 2
    test_ports = {0, 1, k, k + 1}
    require(
        all(result[port] in test_ports for port in test_ports),
        "A test wire escaped to an unused outward port",
    )
    crosses = sum(result[port] in {k, k + 1} for port in (0, 1))
    require(crosses in (0, 2), "Exactly one test wire crosses the complete diagram")
    return crosses == 2


def legal_options(states: int, symbol: str) -> tuple[Transition, ...]:
    directions = (0, 1) if symbol == "L" else (
        (-1, 0) if symbol == "R" else (-1, 0, 1)
    )
    return (None,) + tuple((state, direction) for state in range(states) for direction in directions)


def all_one_state_machines() -> Iterator[Machine]:
    for transitions in product(*(legal_options(1, symbol) for symbol in SYMBOLS)):
        for accepting in (frozenset(), frozenset({0})):
            yield Machine(1, accepting, tuple((transition,) for transition in transitions))


def random_machines(states: int, count: int, seed: int) -> Iterator[Machine]:
    generator = random.Random(seed)
    for _ in range(count):
        accepting = frozenset(state for state in range(states) if generator.randrange(2))
        rows = tuple(
            tuple(generator.choice(legal_options(states, symbol)) for _ in range(states))
            for symbol in SYMBOLS
        )
        yield Machine(states, accepting, rows)


def all_words(maximum_length: int) -> tuple[str, ...]:
    return tuple(
        "".join(bits)
        for length in range(maximum_length + 1)
        for bits in product("01", repeat=length)
    )


def audit_family(machines: Iterator[Machine], words: Sequence[str], name: str) -> dict[str, object]:
    machine_count = 0
    outcomes: Counter[str] = Counter()
    widths: Counter[int] = Counter()
    maximum_run_steps = 0
    machine_features: Counter[str] = Counter()
    for machine in machines:
        machine_count += 1
        slots = candidate_slots(machine)
        k = 2 * len(slots)
        widths[k] += 1
        require(k <= 8 * machine.states + 2, "Linear diagram-degree bound failed")
        diagrams = {symbol: local_diagram(machine, symbol, slots) for symbol in SYMBOLS}
        require(all(len(diagram) == 2 * k for diagram in diagrams.values()), "Wrong diagram size")
        flat = tuple(transition for row in machine.transition_rows for transition in row)
        machine_features["has_partial_transition"] += int(None in flat)
        machine_features["has_stay_transition"] += int(any(t is not None and t[1] == 0 for t in flat))
        machine_features["accepting_initial_state"] += int(0 in machine.accepting)
        machine_features["no_accepting_states"] += int(not machine.accepting)
        for word in words:
            expected, outcome, steps = direct_acceptance(machine, word)
            obtained = diagram_acceptance(diagrams, word)
            if expected != obtained:
                failure = {
                    "word": word,
                    "expected": expected,
                    "obtained": obtained,
                    "machine": machine.description(),
                    "slots": slots,
                    "diagrams": diagrams,
                }
                raise AuditFailure("Semantic mismatch: " + json.dumps(failure, sort_keys=True))
            outcomes[outcome] += 1
            maximum_run_steps = max(maximum_run_steps, steps)
        if machine_count % 128 == 0:
            print(f"{name}: {machine_count} machines passed", flush=True)
    require(outcomes["reject_loop"] > 0, f"{name} missed nonaccepting infinite runs")
    require(outcomes["reject_undefined"] > 0, f"{name} missed undefined halts")
    require(outcomes["accept_initial"] > 0, f"{name} missed initial acceptance")
    return {
        "name": name,
        "machines": machine_count,
        "words_per_machine": len(words),
        "machine_word_pairs": machine_count * len(words),
        "local_diagrams_constructed": 4 * machine_count,
        "outcomes": dict(sorted(outcomes.items())),
        "diagram_degrees": dict(sorted(widths.items())),
        "machine_features": dict(sorted(machine_features.items())),
        "maximum_direct_steps": maximum_run_steps,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-word-length", type=int, default=5)
    parser.add_argument("--random-two-state", type=int, default=512)
    parser.add_argument("--seed", type=int, default=20261007)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    require(args.max_word_length >= 0, "Word length must be nonnegative")
    require(args.random_two_state > 0, "Random machine count must be positive")
    words = all_words(args.max_word_length)
    one_state = audit_family(all_one_state_machines(), words, "exhaustive_one_state")
    require(one_state["machines"] == 288, "Wrong number of one-state machines")
    two_state = audit_family(
        random_machines(2, args.random_two_state, args.seed), words, "seeded_two_state"
    )
    families = [one_state, two_state]
    certificate = {
        "status": "pass",
        "method": "symbol-local lane wiring, local contraction, Brauer products, direct run comparison",
        "maximum_word_length": args.max_word_length,
        "random_seed": args.seed,
        "total_machines": sum(int(family["machines"]) for family in families),
        "total_machine_word_pairs": sum(int(family["machine_word_pairs"]) for family in families),
        "total_local_diagrams": sum(int(family["local_diagrams_constructed"]) for family in families),
        "claims_checked": [
            "at most 4*s+1 crossing candidate triples",
            "diagram degree at most 8*s+2",
            "every local wire contracts to a perfect matching",
            "local diagrams depend only on the scanned symbol",
            "product connects the test sides iff original machine accepts",
            "partial transitions, stay moves, rejecting loops, initial acceptance, empty input",
        ],
        "families": families,
    }
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(certificate, indent=2) + "\n", encoding="utf-8")
        print(f"Certificate written to {args.output}", flush=True)
    print(
        f"All {certificate['total_machine_word_pairs']} machine-word comparisons passed; "
        f"{certificate['total_local_diagrams']} local diagrams constructed.",
        flush=True,
    )


if __name__ == "__main__":
    main()
