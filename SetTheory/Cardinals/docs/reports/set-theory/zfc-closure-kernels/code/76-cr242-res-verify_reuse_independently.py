#!/usr/bin/env python3
"""Independent literal verifier for the inherited-label 243 -> 242 fold.

No compiler, register macros, abstract interpreter, or discovery code is used.
Every short trace rejects reads outside its stated context. The finite
incoming-edge checks prove the original-machine invariant by induction;
the positive complete blocks give equality of tape, head and control state.
The ordinary stuttering proof is recorded in local_reuse_proof.tex.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

OLD_SHA = "4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300"
NEW_SHA = "6b700aa713418cfe347a6ff2d0a92de7c31810d1cf69814b4684c7fb463876a0"
START, HALT = 95, 254
INTERNAL = {15, 27}
MACROS = {(11, 0), (18, 0), (47, 0), (65, 0)}


def table(path):
    rows, start = {}, None
    for line in path.read_text(encoding="ascii").splitlines():
        if line.startswith("#! start "):
            assert start is None
            start = int(line.split()[-1])
        elif line and not line.startswith("#"):
            q, b, w, move, target = line.split()
            q, b, w, target = map(int, (q, b, w, target))
            assert b in (0, 1) and w in (0, 1) and move in ("L", "R")
            assert (q, b) not in rows
            rows[q, b] = (w, move, target)
    states = {q for q, b in rows}
    assert start == START and HALT not in states
    assert set(rows) == {(q, b) for q in states for b in (0, 1)}
    assert {r[2] for r in rows.values()} - states == {HALT}
    return rows, states


def incoming(rows, q):
    return sorted((*k, *r) for k, r in rows.items() if r[2] == q)


def trace(rows, state, initial_context, duration):
    head, cells, transitions = 0, dict(initial_context), []
    for _ in range(duration):
        assert state != HALT and head in cells, ("unfixed exterior read", state, head)
        bit = cells[head]
        write, move, target = rows[state, bit]
        transitions.append([state, head, bit, write, move, target])
        cells[head] = write
        head += 1 if move == "R" else -1
        state = target
    return (state, head, cells), transitions


def verify(old_path, new_path):
    assert hashlib.sha256(old_path.read_bytes()).hexdigest() == OLD_SHA
    assert hashlib.sha256(new_path.read_bytes()).hexdigest() == NEW_SHA
    old, old_states = table(old_path)
    new, new_states = table(new_path)
    assert len(old_states) == 243 and len(new_states) == 242
    assert new_states == old_states - {15}
    expected_patch = {(11, 0): (0, "R", 27), (27, 1): (1, "R", 22)}
    assert {k: r for k, r in new.items() if old[k] != r} == expected_patch
    assert set(old) - set(new) == {(15, 0), (15, 1)}

    # Original-machine invariant: helpers18/47/65 have a zero immediately
    # left of the head; state27 reads zero. It is vacuous at start95.
    helper_edges = {}
    for q in (18, 47, 65):
        edges = incoming(old, q)
        assert edges and all((w, d) == (0, "R") for _, _, w, d, _ in edges)
        helper_edges[q] = edges
    assert incoming(old, 27) == [
        (18, 0, 0, "L", 27),
        (47, 0, 0, "L", 27),
        (65, 0, 0, "L", 27),
    ]
    assert incoming(old, 15) == [(11, 0, 0, "R", 15)]
    assert START not in INTERNAL | {18, 47, 65}

    ordinary = []
    for q in sorted(old_states - INTERNAL):
        for bit in (0, 1):
            if (q, bit) in MACROS:
                continue
            assert old[q, bit] == new[q, bit]
            assert old[q, bit][2] not in INTERNAL
            ordinary.append([q, bit])
    for machine in (old, new):
        assert {(q, b) for (q, b), (_, _, t) in machine.items()
                if q not in INTERNAL and t in INTERNAL} == MACROS

    cases = [
        ("former15_next_zero", 11, {0: 0, 1: 0}, 2, 4, 21, 2),
        ("former15_next_one", 11, {0: 0, 1: 1}, 2, 2, 22, 2),
        ("old27_from18", 18, {-1: 0, 0: 0}, 2, 2, 32, -2),
        ("old27_from47", 47, {-1: 0, 0: 0}, 2, 2, 32, -2),
        ("old27_from65", 65, {-1: 0, 0: 0}, 2, 2, 32, -2),
    ]
    checked = []
    for name, q, context, old_clock, new_clock, target, offset in cases:
        old_final, old_trace = trace(old, q, context, old_clock)
        new_final, new_trace = trace(new, q, context, new_clock)
        assert old_final == new_final == (target, offset, context)
        assert target not in INTERNAL and 0 < old_clock <= new_clock <= 2 * old_clock
        checked.append(dict(name=name, state=q, context=context,
                            old_steps=old_clock, new_steps=new_clock,
                            target=target, head_offset=offset,
                            old_trace=old_trace, new_trace=new_trace,
                            whole_tape_unchanged=True))
    assert {(q, context[0]) for _, q, context, *_ in cases} == MACROS
    return dict(status="PASS_INDEPENDENT_LOCAL_REUSE_CERTIFICATE",
                old_sha256=OLD_SHA, new_sha256=NEW_SHA,
                old_working_states=243, new_working_states=242,
                old_start=START, new_start=START, common_halt=HALT,
                removed_state=15, reused_state=27,
                changed_retained_rows=sorted(expected_patch),
                ordinary_rows=len(ordinary), local_cases=len(cases),
                invariant_incoming_helper_edges=helper_edges, cases=checked,
                theorem_scope="From old state95, any head and binary tape: halting equivalence.",
                time_bound="For halting runs, T_old <= T_new <= 2*T_old.",
                exact_time="T_new=T_old+2*Z, where Z counts old11/read0 with following bit0.",
                proof_status="Finite literal checks plus ordinary stuttering proof; no kernel proof claimed.")


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("old_table", type=Path)
    ap.add_argument("new_table", type=Path)
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    if not __debug__:
        raise RuntimeError("Assertions must remain enabled; do not use -O.")
    result = verify(args.old_table, args.new_table)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items()
                      if k not in ("cases", "invariant_incoming_helper_edges")}, indent=2))


if __name__ == "__main__":
    main()
