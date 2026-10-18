#!/usr/bin/env python3
"""Rebuild and independently verify the 243 -> 242 branch-borrowing reduction.

Standard library only. This checks a finite sufficient certificate for the
ordinary mathematical proof in report.tex. It is not a proof-assistant kernel.
All simulated local reads must remain inside the explicitly known window;
the exterior tape is therefore arbitrary, not silently filled with zeros.
"""
from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
import hashlib
from itertools import product
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
BASE_SHA = "4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300"
OLD_NEW_SHA = "6b700aa713418cfe347a6ff2d0a92de7c31810d1cf69814b4684c7fb463876a0"
NEW_SHA = "64ddeb2c01c3e9c7feffaffaad87266a270716c9307892a0445bf869b988984d"
PIN = "e58338db7545909907e07a7603e8eb88625c527a"
LEFT_ZERO = {18, 47, 65}


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


@dataclass(frozen=True)
class Edge:
    write: int
    move: int
    target: int


@dataclass
class Machine:
    start: int
    halt: int
    rows: dict[tuple[int, int], Edge]

    @property
    def states(self):
        return {q for q, _ in self.rows}


def parse(data):
    rows, start = {}, None
    for line in data.decode("ascii").splitlines():
        if not line.strip():
            continue
        if line.startswith("#! start "):
            require(start is None, "Duplicate start directive")
            start = int(line.removeprefix("#! start "))
            continue
        if line.startswith("#"):
            continue
        match = re.fullmatch(r"(\d+) ([01]) ([01]) ([LR]) (\d+)", line)
        require(match is not None, "Invalid row: " + line)
        q, r, w, d, t = match.groups()
        key = int(q), int(r)
        require(key not in rows, "Duplicate transition")
        rows[key] = Edge(int(w), 1 if d == "R" else -1, int(t))
    states = {q for q, _ in rows}
    require(start in states, "Missing start state")
    require(set(rows) == {(q, b) for q in states for b in (0, 1)}, "Partial table")
    terminals = {edge.target for edge in rows.values()} - states
    require(len(terminals) == 1, "Expected exactly one target-only halt")
    return Machine(start, terminals.pop(), rows)


def encode(machine):
    lines = [f"#! start {machine.start}"]
    for (q, b), e in sorted(machine.rows.items()):
        lines.append(f"{q} {b} {e.write} {'R' if e.move == 1 else 'L'} {e.target}")
    return ("\n".join(lines) + "\n").encode("ascii")


def derive(old):
    require(old.start == 95 and old.halt == 254 and len(old.states) == 243,
            "Baseline convention mismatch")
    rows = {key: value for key, value in old.rows.items() if key[0] != 15}
    rows[11, 0] = Edge(0, 1, 27)
    rows[27, 1] = Edge(1, 1, 22)
    new = Machine(95, 254, rows)
    order = [95] + sorted(new.states - {95})
    mapping = {q: i for i, q in enumerate(order)} | {254: 242}
    dense = Machine(0, 242, {(mapping[q], b): Edge(e.write, e.move, mapping[e.target])
                           for (q, b), e in rows.items()})
    return new, dense, mapping


def invariant(q, head, tape):
    return (q not in LEFT_ZERO or tape[head - 1] == 0) and (q != 27 or tape[head] == 0)


def finite_step(machine, q, head, tape):
    require(head in tape, "A local trace read outside its known window")
    edge = machine.rows[q, tape[head]]
    out = dict(tape)
    out[head] = edge.write
    return edge.target, head + edge.move, out


def local_trace(machine, q, tape, steps):
    head, tape = 0, dict(tape)
    trace = []
    for _ in range(steps):
        trace.append({"state": q, "head": head, "read": tape[head]})
        q, head, tape = finite_step(machine, q, head, tape)
    return (q, head, tape), trace


def check_certificate(old, new):
    deleted = set(old.rows) - set(new.rows)
    changed = {key for key in new.rows if old.rows[key] != new.rows[key]}
    require(deleted == {(15, 0), (15, 1)}, "Wrong deleted rows")
    require(changed == {(11, 0), (27, 1)}, "Wrong retained-row changes")
    require(len(new.rows) == 484 and len(new.states) == 242, "Wrong state count")
    require(all(e.target != 15 for e in new.rows.values()), "Reference to deleted state")

    incoming = {q: sorted([s, b, e.write, e.move] for (s, b), e in old.rows.items()
                          if e.target == q) for q in (15, 18, 27, 47, 65)}
    require(incoming[15] == [[11, 0, 0, 1]], "Unexpected incoming edge to 15")
    require(incoming[27] == [[18, 0, 0, -1], [47, 0, 0, -1], [65, 0, 0, -1]],
            "Unexpected incoming edge to 27")
    for q in LEFT_ZERO:
        require(all(w == 0 and move == 1 for _, _, w, move in incoming[q]),
                "Zero-left premise is not produced by every predecessor")

    # This Boolean obligation quantifies every state and every relevant local
    # tape assignment. Offsets -2,-1,0,1 cover all premises and conclusions.
    obligations, admitted = 0, 0
    for q in sorted(old.states):
        for bits in product((0, 1), repeat=4):
            tape = dict(zip(range(-2, 2), bits))
            obligations += 1
            if not invariant(q, 0, tape):
                continue
            admitted += 1
            q2, h2, t2 = finite_step(old, q, 0, tape)
            require(invariant(q2, h2, t2), "Invariant is not inductive")
    require(95 not in LEFT_ZERO | {27, 15}, "Initial checkpoint is constrained")

    blocks = []
    for following in (0, 1):
        tape = {0: 0, 1: following}
        a, trace_a = local_trace(old, 11, tape, 2)
        b, trace_b = local_trace(new, 11, tape, 4 if following == 0 else 2)
        require(a == b, "Whole-window block endpoints differ")
        require(a[0] == (21 if following == 0 else 22) and a[1] == 2,
                "Wrong checkpoint endpoint")
        require(a[2] == tape, "A block changes the tape")
        require(all(x["state"] != old.halt for x in trace_a + trace_b), "Internal halt")
        blocks.append({"following_bit": following, "old_steps": 2,
                       "new_steps": len(trace_b), "old_trace": trace_a,
                       "new_trace": trace_b, "endpoint_state": a[0],
                       "head_displacement": a[1], "entire_tape_unchanged": True,
                       "only_read_offsets": [0, 1]})

    ordinary = 0
    for key, edge in old.rows.items():
        q, b = key
        if q == 15 or key == (11, 0):
            continue
        if key == (27, 1):
            require(not invariant(q, 0, {-1: 0, 0: b}), "Dormant row not excluded")
            continue
        require(new.rows[key] == edge and edge.target != 15, "Ordinary step failure")
        ordinary += 1
    require(ordinary == 482, "Wrong ordinary-row census")
    return {"status": "PASS_FINITE_REDUCTION_CERTIFICATE", "source_commit": PIN,
            "baseline_sha256": BASE_SHA, "candidate_old_sha256": OLD_NEW_SHA,
            "candidate_canonical_sha256": NEW_SHA,
            "working_states": 242, "binary_rows": 484, "deleted_state": 15,
            "retained_rows_changed": [[11, 0], [27, 1]],
            "ordinary_equal_rows": ordinary, "incoming_edges": incoming,
            "invariant_offsets": [-2, -1, 0, 1],
            "boolean_obligations": obligations, "admitted_invariant_cases": admitted,
            "blocks": blocks, "checkpoint_exclusion": [15],
            "original_block_lengths": [1, 2], "new_block_lengths": [1, 2, 4],
            "scope": "Finite certificate for an ordinary all-tape positive-block proof; "
                     "not a finite-run argument and not a proof-assistant verification."}


def sparse_step(machine, q, head, ones):
    edge = machine.rows[q, int(head in ones)]
    if edge.write:
        ones.add(head)
    else:
        ones.discard(head)
    return edge.target, head + edge.move


def check_blank(old, new, dense):
    old_steps, new_steps = 0, 0
    q1 = q2 = 95
    h1 = h2 = 0
    t1, t2 = set(), set()
    blocks = Counter()
    target = 407967
    while old_steps < target:
        require((q1, h1, t1) == (q2, h2, t2) and q1 != 15, "Checkpoint mismatch")
        if q1 == 11 and h1 not in t1:
            bit = int(h1 + 1 in t1)
            n1, n2 = 2, 2 if bit else 4
            blocks[f"branch_{bit}"] += 1
        else:
            n1 = n2 = 1
            blocks["ordinary"] += 1
        for _ in range(n1):
            q1, h1 = sparse_step(old, q1, h1, t1)
        for _ in range(n2):
            q2, h2 = sparse_step(new, q2, h2, t2)
        old_steps += n1
        new_steps += n2
    require(old_steps == target and (q1, h1, t1) == (q2, h2, t2), "Final mismatch")
    require(q1 == 96 and h1 == -5 and len(t1) == 351, "Unexpected baseline frame")
    require(new_steps == target + 2 * blocks["branch_0"], "Clock accounting")

    # Independent dense literal interpreter of the CANONICAL candidate.
    origin = new_steps + 1
    cells = bytearray(2 * new_steps + 3)
    q, head = dense.start, origin
    for _ in range(new_steps):
        e = dense.rows[q, cells[head]]
        cells[head] = e.write
        q, head = e.target, head + e.move
    actual = {i - origin for i, bit in enumerate(cells) if bit}
    old_to_new = {95: 0} | {q: i + 1 for i, q in enumerate(sorted(new.states - {95}))}
    require(q == old_to_new[96] and head - origin == -5 and actual == t1,
            "Independent canonical dense replay disagrees")

    header = min(x for x in t1 if x >= -5)
    require({x for x in t1 if x < header} == {-6}, "Unexpected marker or left exterior")
    position, values = header + 1, []
    while position <= max(t1):
        require(position not in t1 and position + 1 in t1, "Malformed unary block")
        position += 1
        start = position
        while position in t1:
            position += 1
        values.append(position - start - 1)
    require(header == 176 and len(values) == 176, "Wrong frame layout")
    require(values[:9] == [0, 0, 0, 3, 0, 0, 3, 0, 0] and values[9:] == [1] * 167,
            "Wrong register or spare data")
    return {"status": "PASS_INDEPENDENT_BLANK_COMPARISON", "old_steps": old_steps,
            "new_steps": new_steps, "block_counts": dict(blocks),
            "old_dispatcher": 96, "new_dispatcher": old_to_new[96], "head": h1,
            "marker": -6, "header": header, "header_distance": 181,
            "physical_registers": values[:9], "logical_registers": [3, 0, 0, 0, 3, 0, 0, 0, 0],
            "spare_count": 167, "spare_values": values[9:], "one_count": len(t1),
            "all_one_positions": sorted(t1), "all_other_cells_zero": True,
            "independent_canonical_dense_replay": True,
            "scope": "Exact finite initialization check; the all-tape theorem is separate."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", action="store_true", help="Regenerate deterministic machine files")
    parser.add_argument("--skip-blank", action="store_true", help="Only check the finite proof certificate")
    args = parser.parse_args()
    raw = (ROOT / "reference/zfc_combined243_old.tm").read_bytes()
    require(sha(raw) == BASE_SHA, "Baseline SHA256 differs")
    old = parse(raw)
    new, canonical, mapping = derive(old)
    outputs = {"zfc242_old.tm": encode(new), "zfc242.tm": encode(canonical),
               "renumbering.json": (json.dumps(mapping, indent=2) + "\n").encode()}
    require(sha(outputs["zfc242_old.tm"]) == OLD_NEW_SHA, "Inherited table hash differs")
    require(sha(outputs["zfc242.tm"]) == NEW_SHA, "Canonical table hash differs")
    for name, data in outputs.items():
        path = ROOT / "machine" / name
        if args.build:
            path.write_bytes(data)
        require(path.read_bytes() == data, "Delivered artifact differs: " + name)
    record = check_certificate(old, new)
    (ROOT / "evidence/reduction-proof.json").write_text(json.dumps(record, indent=2) + "\n")
    if not args.skip_blank:
        blank = check_blank(old, new, canonical)
        (ROOT / "evidence/blank-comparison.json").write_text(json.dumps(blank, indent=2) + "\n")
        print(json.dumps({k: blank[k] for k in ("status", "old_steps", "new_steps", "block_counts")}))
    print(json.dumps({k: record[k] for k in ("status", "working_states", "binary_rows",
                                           "ordinary_equal_rows", "boolean_obligations")}))


if __name__ == "__main__":
    main()
