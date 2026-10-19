#!/usr/bin/env python3
"""Literal-table audit of the compensated fold after the QT loop rotation.

No compiler, simulator package, symbolic register interpreter, inherited
checker, or search code is imported.  The finite window checks imply the
arbitrary-tape local identities in proof/composition_audit.tex.  The finite
invariant check is exhaustive, not a bounded run on selected complete tapes.

Usage:
  python3 -B audit_composition.py BASE245 ROTATION244 COMBINED243 --output audit.json

The old-label machines use start 95 and target-only halt 254.  Raw hashes
pin the baseline and rotation inputs.  The combined input is identified by
its exact transition dictionary, whose construction is checked here.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path

BASE_SHA = "f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267"
ROTATION_SHA = "0160caaf5d6db52eb7eb97a76cb04db4b424eb2bc0d58617818a6c7c6a1fe776"
START, HALT = 95, 254
ROTATION_PATCH = {
    (12, 0): (0, "R", 18),
    (12, 1): (1, "R", 17),
    (17, 1): (0, "L", 20),
}
COMPENSATION_PATCH = {
    (92, 1): (1, "R", 66),
    (104, 1): (1, "R", 92),
    (106, 1): (1, "R", 92),
    (167, 1): (1, "L", 151),
}
INTERIOR = {92, 122}
EXCEPTIONAL = {(81, 1), (104, 1), (106, 1), (167, 1)}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_table(path):
    rows = {}
    start = None
    for line_number, line in enumerate(path.read_text(encoding="ascii").splitlines(), 1):
        if line.startswith("#! start "):
            need(start is None, "duplicate start declaration")
            start = int(line.split()[-1])
        elif line and not line.startswith("#"):
            fields = line.split()
            need(len(fields) == 5, f"malformed row at {line_number}")
            state, read, write, move, target = fields
            state, read, write, target = map(int, (state, read, write, target))
            need(read in (0, 1) and write in (0, 1) and move in ("L", "R"),
                 f"invalid binary transition at {line_number}")
            need((state, read) not in rows, "duplicate transition")
            rows[state, read] = (write, move, target)
    states = {state for state, _ in rows}
    need(start == START and HALT not in states, "wrong start or halt")
    need(set(rows) == {(q, b) for q in states for b in (0, 1)}, "incomplete table")
    need({target for _, _, target in rows.values()} - states == {HALT},
         "unexpected target-only states")
    return rows, states


def patch(table, replacements, removed):
    result = {key: row for key, row in table.items() if key[0] not in removed}
    for key, row in replacements.items():
        need(key in result and result[key] != row, "patch does not change a retained row")
        result[key] = row
    need(not any(row[2] in removed for row in result.values()), "dangling removed state")
    return result


def invariant(state, tape, head=0):
    if state in (68, 122, 167) and tape[head - 1] != 1:
        return False
    if state == 81 and tape[head - 1] == 1 and tape[head - 2] != 1:
        return False
    return True


def invariant_audit(table):
    checked = 0
    offsets = (-3, -2, -1, 0, 1)
    for bits in itertools.product((0, 1), repeat=5):
        tape = dict(zip(offsets, bits))
        for (q, read), (write, move, target) in table.items():
            if read != tape[0] or not invariant(q, tape):
                continue
            after = dict(tape)
            after[0] = write
            head = 1 if move == "R" else -1
            need(invariant(target, after, head), f"noninductive row {(q, read)} on {tape}")
            checked += 1
    return checked


def incoming(table, target):
    return sorted((q, b, *row) for (q, b), row in table.items() if row[2] == target)


def local_trace(table, state, context, duration):
    tape = dict(context)
    head = 0
    trace = []
    for _ in range(duration):
        need(state != HALT, "halt inside exceptional block")
        need(head in tape, "local identity reads unspecified exterior tape")
        read = tape[head]
        write, move, target = table[state, read]
        trace.append([state, head, read, write, move, target])
        tape[head] = write
        head += 1 if move == "R" else -1
        state = target
    return (state, head, tape), trace


def check_local_fold(old, old_states, new, new_states):
    need(new == patch(old, COMPENSATION_PATCH, {122}), "incorrect compensated patch")
    need(new_states == old_states - {122}, "wrong removed-state set")
    need(START not in INTERIOR | {68, 81, 167}, "start is constrained")
    expected_incoming = {
        68: [(52, 1, 1, "R", 68), (123, 1, 1, "R", 68)],
        81: [(68, 1, 1, "R", 81), (123, 0, 0, "R", 81)],
        167: [(145, 1, 1, "R", 167), (148, 1, 1, "R", 167)],
    }
    for table in (old, new):
        for target, expected in expected_incoming.items():
            need(incoming(table, target) == expected, f"wrong predecessor list for {target}")
    need(incoming(old, 122) == [(104, 1, 1, "R", 122), (106, 1, 1, "R", 122)],
         "wrong predecessors of deleted state")

    ordinary = []
    for q in sorted(old_states - INTERIOR):
        for read in (0, 1):
            if (q, read) in EXCEPTIONAL:
                continue
            need(old[q, read] == new[q, read], "unequal ordinary transition")
            need(old[q, read][2] not in INTERIOR, "ordinary transition enters interior")
            ordinary.append([q, read])

    cases = []
    for q in (104, 106):
        for right in (0, 1):
            cases.append(dict(name=f"q{q}_right{right}", state=q,
                              context={0: 1, 1: right}, old_steps=2,
                              new_steps=2 if right else 4,
                              target=66 if right else 25, head=2, changes={}))
    cases.extend([
        dict(name="q167_left1", state=167, context={-1: 1, 0: 1},
             old_steps=2, new_steps=2, target=24, head=-2, changes={}),
        dict(name="q81_left0", state=81, context={-1: 0, 0: 1},
             old_steps=2, new_steps=2, target=107, head=-2, changes={}),
        dict(name="q81_left11", state=81, context={-2: 1, -1: 1, 0: 1},
             old_steps=6, new_steps=4, target=2, head=-2, changes={-1: 0, 0: 0}),
    ])

    # Verify that the guarded cases partition every possible entry under I.
    partition_entries = 0
    for q, read in sorted(EXCEPTIONAL):
        for values in itertools.product((0, 1), repeat=5):
            tape = dict(zip((-3, -2, -1, 0, 1), values))
            if tape[0] != read or not invariant(q, tape):
                continue
            matches = [case for case in cases if case["state"] == q
                       and all(tape[pos] == bit for pos, bit in case["context"].items())]
            need(len(matches) == 1, "local cases are not an exhaustive disjoint partition")
            partition_entries += 1

    details = []
    for case in cases:
        a, trace_a = local_trace(old, case["state"], case["context"], case["old_steps"])
        b, trace_b = local_trace(new, case["state"], case["context"], case["new_steps"])
        final_tape = dict(case["context"])
        final_tape.update(case["changes"])
        need(a == b == (case["target"], case["head"], final_tape), "unequal whole-tape endpoints")
        need(case["target"] not in INTERIOR | {68, 81, 167}, "nonboundary or constrained endpoint")
        need(0 < case["old_steps"] <= 6 and 0 < case["new_steps"] <= 4,
             "nonpositive or excessive duration")
        need(2 * case["old_steps"] <= 3 * case["new_steps"] <= 6 * case["old_steps"],
             "invalid time comparison")
        details.append(dict(**case, old_trace=trace_a, new_trace=trace_b,
                            exterior_never_read=True, same_entire_tape=True))

    return dict(
        old_working_states=len(old_states), new_working_states=len(new_states),
        ordinary_equal_rows=len(ordinary), ordinary_rows=ordinary,
        exhaustive_invariant_transitions_old=invariant_audit(old),
        exhaustive_invariant_transitions_new=invariant_audit(new),
        guarded_partition_assignments=partition_entries,
        local_cases=len(cases), local_details=details,
        old_local_steps=sum(case["old_steps"] for case in cases),
        new_local_steps=sum(case["new_steps"] for case in cases),
        theorem="For every binary tape T and head h: Halt(old,95,h,T) iff Halt(new,95,h,T).",
        time_comparison="On matched complete halting runs: (2/3)*t_old <= t_new <= 2*t_old.",
    )


def audit(base_path, rotation_path, combined_path):
    need(sha(base_path) == BASE_SHA, "wrong pinned baseline bytes")
    need(sha(rotation_path) == ROTATION_SHA, "wrong pinned rotation bytes")
    base, base_states = read_table(base_path)
    rotation, rotation_states = read_table(rotation_path)
    combined, combined_states = read_table(combined_path)
    need(len(base_states) == 245 and len(rotation_states) == 244,
         "wrong input state count")
    need(rotation == patch(base, ROTATION_PATCH, {26}), "incorrect rotation table")
    need(rotation_states == base_states - {26}, "wrong rotation state deletion")
    compensated = patch(base, COMPENSATION_PATCH, {122})
    via_rotation = patch(rotation, COMPENSATION_PATCH, {122})
    via_compensation = patch(compensated, ROTATION_PATCH, {26})
    need(combined == via_rotation == via_compensation, "construction square does not commute")
    need(combined_states == base_states - {26, 122} and len(combined_states) == 243,
         "wrong combined state count")
    result = check_local_fold(rotation, rotation_states, combined, combined_states)
    baseline_fold = check_local_fold(base, base_states, compensated, base_states - {122})
    need(result["ordinary_equal_rows"] == 480 and baseline_fold["ordinary_equal_rows"] == 482,
         "wrong ordinary-row coverage")
    return dict(
        status="PASS_INDEPENDENT_243_COMPOSITION_AUDIT",
        base_sha256=sha(base_path), rotation_sha256=sha(rotation_path),
        combined_sha256=sha(combined_path), start=START, halt=HALT,
        combined_working_states=len(combined_states), combined_transition_rows=len(combined),
        removed_original_states=[26, 122], commuting_patch_square=True,
        baseline_compensation_also_verified=True,
        proof_scope="Local fold is universal on all binary tapes from95; rotation calibration is an inherited separate theorem.",
        formal_status="Finite premises checked here; ordinary induction proof supplied separately; no new proof-assistant endpoint claimed.",
        reduction=result,
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("baseline245", type=Path)
    parser.add_argument("rotation244", type=Path)
    parser.add_argument("combined243", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = audit(args.baseline245, args.rotation244, args.combined243)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: value for key, value in result.items() if key != "reduction"}, indent=2))
    print(json.dumps({key: value for key, value in result["reduction"].items()
                      if key not in ("ordinary_rows", "local_details")}, indent=2))


if __name__ == "__main__":
    main()
