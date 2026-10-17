"""Conservative reductions of a deterministic two-symbol Turing-machine table.

Input format: ``#! start q`` followed by ``state read write L|R next`` rows.
Each working state must have exactly two rows. One referenced terminal state
has no rows. The tape is bi-infinite and initially zero; entering the terminal
state halts after the current write and move. Counts exclude that terminal.

The graph and partition tests preserve every tape, head position and individual
step. Unreachable states may be dropped. Equal partition signatures permit a
quotient: induct on steps, keeping the tape/head fixed and mapping the state to
its class. Startup reuse has a separate blank-tape argument: if the start state
is never targeted by another reachable state and its initial zero edge leaves
it, an existing state's identical zero edge gives exactly the same first
successor. Thereafter the removed state is never entered.

The optional local-window search is stronger but still conservative. Its finite
abstract graph contains the head-centred radius-r window. Shifting the window
admits BOTH values for the forgotten outside cell. Induction therefore puts
every actual blank-tape configuration in the computed abstract reachable set.
To remove p in favour of q, redirect all targets p to q. For every abstract
window possible at p, run both machines locally and require a common
configuration (original state mapped p->q), after positive numbers of steps
on BOTH sides. Stop before reading outside the known window. All writes stay
inside that window, so a common window and absolute relative head imply equal
whole tapes. Terminal configurations may match regardless of tape/head. For
states other than p, one ordinary step gives the relation automatically.
Each matched block makes positive progress in both runs; induction and
determinism prove equivalence of blank-tape halting, including infinite runs.

These are finite executable checks with the preceding mathematical arguments,
not a proof-assistant verification of this Python implementation. A failed
reduction search is NOT a lower bound on arbitrary equivalent machines.
No external executable code is imported, and the input table is not modified.
"""
from __future__ import annotations

import argparse
from collections import defaultdict, deque
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re


@dataclass(frozen=True)
class Edge:
    write: int
    move: int
    target: int


@dataclass(frozen=True)
class Machine:
    start: int
    halt: int
    rows: dict[tuple[int, int], Edge]

    @property
    def states(self) -> list[int]:
        return sorted({q for q, _ in self.rows})


def parse_table(text: str) -> Machine:
    """Reject partial states, duplicate rows/starts and ambiguous halt states."""
    rows: dict[tuple[int, int], Edge] = {}
    start = None
    for number, raw in enumerate(text.splitlines(), 1):
        line = raw.strip()
        if not line:
            continue
        if line.startswith("#!"):
            match = re.fullmatch(r"#!\s+start\s+([0-9]+)", line)
            if match is None or start is not None:
                raise ValueError(f"line {number}: invalid or duplicate start directive")
            start = int(match[1])
            continue
        if line.startswith("#"):
            continue
        match = re.fullmatch(r"([0-9]+)\s+([01])\s+([01])\s+([LR])\s+([0-9]+)", line)
        if match is None:
            raise ValueError(f"line {number}: expected state read write L|R next")
        q, read, write, direction, target = match.groups()
        key = (int(q), int(read))
        if key in rows:
            raise ValueError(f"line {number}: duplicate transition")
        rows[key] = Edge(int(write), 1 if direction == "R" else -1, int(target))
    if start is None:
        raise ValueError("missing start directive")
    states = {q for q, _ in rows}
    if start not in states:
        raise ValueError("start has no transitions")
    if set(rows) != {(q, b) for q in states for b in (0, 1)}:
        raise ValueError("every working state must have both symbol transitions")
    terminals = {edge.target for edge in rows.values()} - states
    if len(terminals) != 1:
        raise ValueError("expected exactly one referenced terminal state without rows")
    return Machine(start, terminals.pop(), rows)


def graph_reachable(machine: Machine) -> set[int]:
    reached = {machine.start}
    pending = [machine.start]
    while pending:
        q = pending.pop()
        if q == machine.halt:
            continue
        for b in (0, 1):
            n = machine.rows[q, b].target
            if n not in reached:
                reached.add(n)
                pending.append(n)
    return reached


def bisimulation(machine: Machine) -> tuple[list[list[int]], int]:
    states = machine.states + [machine.halt]
    classes = {q: int(q == machine.halt) for q in states}
    rounds = 0
    while True:
        signatures = {}
        refined = {}
        for q in states:
            key = (("halt",) if q == machine.halt else
                   tuple((machine.rows[q, b].write, machine.rows[q, b].move,
                          classes[machine.rows[q, b].target]) for b in (0, 1)))
            refined[q] = signatures.setdefault(key, len(signatures))
        rounds += 1
        # Signatures refine the previous partition; equal class counts suffice.
        stable = len(set(refined.values())) == len(set(classes.values()))
        classes = refined
        if stable:
            groups: dict[int, list[int]] = defaultdict(list)
            for q in states:
                groups[classes[q]].append(q)
            return list(groups.values()), rounds


def startup_reuse(machine: Machine, reachable: set[int]) -> dict:
    incoming = sorted([q, b] for (q, b), e in machine.rows.items()
                      if q != machine.start and q in reachable and e.target == machine.start)
    initial = machine.rows[machine.start, 0]
    candidates = [q for q in machine.states if q != machine.start
                  and machine.rows[q, 0] == initial]
    admissible = not incoming and initial.target != machine.start
    return {"other_reachable_incoming_edges": incoming,
            "initial_zero_edge_leaves_start": initial.target != machine.start,
            "same_zero_edge_states": candidates,
            "safe_replacements": candidates if admissible else []}


def window_reachable(machine: Machine, radius: int) -> dict[int, list[int]]:
    """Overapproximate blank-tape runs; bit i denotes cell i-radius."""
    width = 2 * radius + 1
    full = (1 << width) - 1
    reached = {(machine.start, 0)}
    pending = deque(reached)
    by_state: dict[int, list[int]] = defaultdict(list)
    while pending:
        q, pattern = pending.popleft()
        by_state[q].append(pattern)
        if q == machine.halt:
            continue
        edge = machine.rows[q, (pattern >> radius) & 1]
        written = (pattern & ~(1 << radius)) | (edge.write << radius)
        if edge.move == 1:
            shifted, unknown = written >> 1, 1 << (width - 1)
        else:
            shifted, unknown = (written << 1) & full, 1
        for next_pattern in (shifted, shifted | unknown):
            item = (edge.target, next_pattern)
            if item not in reached:
                reached.add(item)
                pending.append(item)
    return {q: sorted(patterns) for q, patterns in by_state.items()}


def local_trace(machine: Machine, start: int, pattern: int, radius: int,
                bound: int, removed: int | None = None,
                replacement: int | None = None) -> list[tuple[int, int, int]]:
    head, q = 0, start
    result = []
    for _ in range(bound):
        if q == machine.halt or not -radius <= head <= radius:
            break
        position = head + radius
        edge = machine.rows[q, (pattern >> position) & 1]
        pattern = (pattern & ~(1 << position)) | (edge.write << position)
        head += edge.move
        q = replacement if edge.target == removed else edge.target
        result.append((q, head, pattern))
    return result


def local_merge_certificate(machine: Machine, removed: int, replacement: int,
                            windows: list[int], radius: int, bound: int,
                            originals: dict[int, list[tuple[int, int, int]]] | None = None
                            ) -> list[list[int]] | None:
    """Return [window, original steps, reduced steps] for every possible window."""
    certificate = []
    for pattern in windows:
        original = (originals[pattern] if originals is not None else
                    local_trace(machine, removed, pattern, radius, bound))
        targets = {}
        for i, (q, head, tape) in enumerate(original, 1):
            mapped = replacement if q == removed else q
            key = ("halt",) if q == machine.halt else (mapped, head, tape)
            targets.setdefault(key, i)
        reduced = local_trace(machine, replacement, pattern, radius, bound,
                              removed, replacement)
        for j, (q, head, tape) in enumerate(reduced, 1):
            key = ("halt",) if q == machine.halt else (q, head, tape)
            if key in targets:
                certificate.append([pattern, targets[key], j])
                break
        else:
            return None
    return certificate


def local_merge_search(machine: Machine, windows: dict[int, list[int]],
                       radius: int, bound: int) -> dict:
    candidates = []
    attempts = 0
    for removed in machine.states:
        patterns = windows.get(removed, [])
        if not patterns:
            continue
        originals = {p: local_trace(machine, removed, p, radius, bound) for p in patterns}
        for replacement in machine.states:
            if replacement == removed:
                continue
            attempts += 1
            certificate = local_merge_certificate(machine, removed, replacement, patterns,
                                                   radius, bound, originals)
            if certificate is not None:
                candidates.append({"removed": removed, "replacement": replacement,
                                   "window_step_certificate": certificate})
    read_pairs = {(q, (p >> radius) & 1) for q, patterns in windows.items()
                  if q != machine.halt for p in patterns}
    return {"radius": radius, "maximum_steps_per_side": bound,
            "abstract_configurations": sum(map(len, windows.values())),
            "abstractly_possible_transition_pairs": len(read_pairs),
            "abstractly_impossible_transition_pairs": [list(k) for k in sorted(machine.rows)
                                                        if k not in read_pairs],
            "ordered_state_pairs_checked": attempts, "safe_single_state_merges": candidates}


def trace_blank(machine: Machine, fuel: int) -> dict:
    ones: set[int] = set()
    q, head, steps = machine.start, 0, 0
    observed: dict[int, set[int]] = defaultdict(set)
    while steps < fuel and q != machine.halt:
        read = int(head in ones)
        observed[q].add(read)
        edge = machine.rows[q, read]
        if edge.write:
            ones.add(head)
        else:
            ones.discard(head)
        head += edge.move
        q = edge.target
        steps += 1
    configuration = {"state": q, "head": head, "one_cells": sorted(ones)}
    digest = hashlib.sha256(json.dumps(configuration, sort_keys=True,
                                      separators=(",", ":")).encode()).hexdigest()
    return {"requested_steps": fuel, "executed_steps": steps, "halted": q == machine.halt,
            "final_state": q, "final_head": head, "final_ones": len(ones),
            "final_configuration_sha256": digest,
            "observed_states": len(observed),
            "observed_transition_pairs": sum(map(len, observed.values())),
            "finite_prefix_only": True,
            "does_not_establish_future_read_or_marker_invariants": True}


def check_coq_table(machine: Machine, source: str) -> None:
    """Compare parsed tuples only; do not execute or claim to compile Coq."""
    marker = "Definition table254"
    if marker not in source:
        raise ValueError("Coq source has no Definition table254")
    body = source[source.index(marker):].split("].", 1)[0]
    tuples = re.findall(r"\((true|false), ([LR]), ([0-9]+), (true|false), ([LR]), ([0-9]+)\)", body)
    if machine.states != list(range(len(tuples))):
        raise ValueError("Coq table row count/state labels differ")
    for q, row in enumerate(tuples):
        for b in (0, 1):
            write, direction, target = row[3*b:3*b+3]
            if machine.rows[q, b] != Edge(int(write == "true"),
                                         1 if direction == "R" else -1, int(target)):
                raise ValueError(f"Coq row {q}, symbol {b} differs")


def self_test() -> int:
    checked = 0
    sample = "#! start 0\n0 0 1 R 1\n0 1 0 L 2\n1 0 1 R 9\n1 1 0 L 9\n2 0 1 R 9\n2 1 0 L 9\n3 0 0 R 3\n3 1 1 L 3\n"
    m = parse_table(sample)
    if graph_reachable(m) != {0, 1, 2, 9}:
        raise RuntimeError("reachability regression")
    groups, _ = bisimulation(m)
    if [1, 2] not in groups or [3] not in groups:
        raise RuntimeError("partition regression")
    checked += 2
    for bad in (sample + "0 0 1 R 1\n", sample.replace("0 1 0 L 2\n", ""),
                sample + "#! start 1\n", sample.replace("1 R 1", "1 X 1", 1),
                sample.replace("1 R 1", "1 R 8", 1)):
        try:
            parse_table(bad)
        except ValueError:
            checked += 1
        else:
            raise RuntimeError("malformed-table parser regression")
    startup = parse_table("#! start 0\n0 0 1 R 1\n0 1 0 L 2\n1 0 1 R 1\n1 1 0 L 2\n")
    if startup_reuse(startup, graph_reachable(startup))["safe_replacements"] != [1]:
        raise RuntimeError("startup reuse regression")
    checked += 1
    weak = parse_table("#! start 0\n0 0 0 R 1\n0 1 0 R 1\n1 0 0 L 4\n1 1 1 L 4\n2 0 0 L 3\n2 1 0 L 3\n3 0 0 R 4\n3 1 1 R 4\n")
    windows = window_reachable(weak, 1)
    if local_merge_certificate(weak, 0, 2, windows[0], 1, 4) is None:
        raise RuntimeError("positive local merge regression")
    checked += 1
    negative = parse_table("#! start 0\n0 0 0 R 0\n0 1 1 R 0\n1 0 0 R 2\n1 1 1 R 2\n")
    windows = window_reachable(negative, 1)
    if local_merge_certificate(negative, 0, 1, windows[0], 1, 4) is not None:
        raise RuntimeError("nonhalting/halting local merge regression")
    checked += 1
    if not trace_blank(weak, 3)["halted"] or trace_blank(negative, 10)["halted"]:
        raise RuntimeError("simulator regression")
    return checked + 1


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("table", type=Path, nargs="?")
    parser.add_argument("--expected-sha256")
    parser.add_argument("--expected-states", type=int)
    parser.add_argument("--expected-halt", type=int)
    parser.add_argument("--coq-table", type=Path)
    parser.add_argument("--source-url")
    parser.add_argument("--source-commit")
    parser.add_argument("--window-radius", type=int, default=4)
    parser.add_argument("--macro-steps", type=int, default=64)
    parser.add_argument("--trace-steps", type=int, default=0)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    tests = self_test() if args.self_test else None
    if args.table is None:
        if args.self_test:
            print(json.dumps({"self_tests_passed": tests}))
            return
        parser.error("a table path is required")
    if not 0 <= args.window_radius <= 10 or args.macro_steps < 1 or args.trace_steps < 0:
        parser.error("radius must be 0..10, macro steps positive and trace steps nonnegative")
    data = args.table.read_bytes()
    sha256 = hashlib.sha256(data).hexdigest()
    if args.expected_sha256 is not None and sha256 != args.expected_sha256:
        parser.error("table SHA-256 differs from expected pin")
    machine = parse_table(data.decode("utf-8"))
    if args.expected_states is not None and len(machine.states) != args.expected_states:
        parser.error("working state count differs from expected count")
    if args.expected_halt is not None and machine.halt != args.expected_halt:
        parser.error("terminal state differs from expected label")
    if args.coq_table is not None:
        check_coq_table(machine, args.coq_table.read_text())
    reachable = graph_reachable(machine)
    classes, rounds = bisimulation(machine)
    reachable_classes = [g for g in classes if machine.halt not in g and any(q in reachable for q in g)]
    startup = startup_reuse(machine, reachable)
    windows = window_reachable(machine, args.window_radius)
    local = local_merge_search(machine, windows, args.window_radius, args.macro_steps)
    bounds = [len(machine.states), len(reachable - {machine.halt}), len(reachable_classes)]
    if startup["safe_replacements"] or local["safe_single_state_merges"]:
        bounds.append(len(machine.states) - 1)
    result = {"input": {"filename": args.table.name, "sha256": sha256,
                        "expected_sha256_checked": args.expected_sha256 is not None,
                        "source_url": args.source_url, "source_commit": args.source_commit,
                        "coq_literal_table_compared": args.coq_table is not None,
                        "coq_build_reproduced": False},
              "model": {"symbols": 2, "blank_symbol": 0, "start_state": machine.start,
                        "working_states": len(machine.states), "terminal_state": machine.halt,
                        "transition_rows": len(machine.rows), "bi_infinite_tape": True,
                        "terminal_state_excluded_from_count": True},
              "self_tests_passed": tests,
              "state_graph": {"reachable_working_states": len(reachable - {machine.halt}),
                              "unreachable_working_states": sorted(set(machine.states) - reachable)},
              "step_bisimulation": {"refinement_rounds": rounds,
                                    "working_equivalence_classes": len(classes) - 1,
                                    "nontrivial_classes": [g for g in classes if len(g) > 1]},
              "startup_reuse": startup, "local_window_macro_search": local,
              "best_state_count_supported_by_these_checks": min(bounds),
              "global_minimality_claimed": False,
              "full_compiler_or_new_set_theory_calibration_verified": False}
    if args.trace_steps:
        result["finite_blank_tape_prefix"] = trace_blank(machine, args.trace_steps)
    encoded = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded)
    print(encoded, end="")


if __name__ == "__main__":
    main()
