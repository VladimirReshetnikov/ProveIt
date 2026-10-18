#!/usr/bin/env python3
"""Independently check the 245 -> 244 state-elimination stuttering proof.

This checker uses only literal binary transition tables, the finite local
contexts stated in the accompanying proof, and exact finite execution.
It imports no TM simulator, register interpreter, compiler, SMT solver,
symbolic register macros, or search code.

The checked contracts quantify over arbitrary exterior tape cells: a trace
is rejected if it reads a position not fixed by its stated local context.
The simple incoming-edge obligations establish the needed contexts from
start state 95 on every initial tape, including the blank tape.

Run: python verify_local_stuttering.py OLD_TABLE NEW_TABLE --output audit.json
The ordinary mathematical proof converting these finite checks to a
halting equivalence is in ../proof/independent_audit.tex. This is not itself a
proof-assistant kernel theorem.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path


OLD_SHA256 = "f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267"
START = 95
HALT = 254
INTERNAL = {92, 122}
MACRO_ROWS = {(81, 1), (104, 1), (106, 1), (167, 1)}


def load_table(path: Path):
    table, start = {}, None
    for line in path.read_text(encoding="ascii").splitlines():
        if line.startswith("#! start "):
            assert start is None
            start = int(line.split()[-1])
        elif line and not line.startswith("#"):
            fields = line.split()
            assert len(fields) == 5
            q, b, w, direction, target = fields
            q, b, w, target = map(int, (q, b, w, target))
            assert b in (0, 1) and w in (0, 1) and direction in ("L", "R")
            assert (q, b) not in table
            table[q, b] = w, direction, target
    states = {q for q, _ in table}
    assert set(table) == {(q, b) for q in states for b in (0, 1)}
    assert {target for _, _, target in table.values()} - states == {HALT}
    assert start == START and HALT not in states
    return table, states


def incoming(table, target):
    return sorted((q, b, *row) for (q, b), row in table.items() if row[2] == target)


def trace(table, state, context, steps):
    """Run exactly `steps` transitions without inspecting arbitrary exterior."""
    tape = dict(context)
    head = 0
    rows = []
    for tick in range(steps):
        assert head in tape, ("read outside the quantified finite context", state, head)
        bit = tape[head]
        assert bit in (0, 1) and state != HALT
        write, direction, target = table[state, bit]
        rows.append(dict(state=state, head=head, read=bit, write=write,
                         move=direction, target=target))
        tape[head] = write
        head += 1 if direction == "R" else -1
        state = target
    changed = {str(p): bit for p, bit in tape.items() if bit != context[p]}
    return (state, head, tape), dict(steps=steps, rows=rows,
                                    changed_cells=changed,
                                    exterior_never_read=True)


def verify(old_path: Path, new_path: Path):
    assert hashlib.sha256(old_path.read_bytes()).hexdigest() == OLD_SHA256
    old, old_states = load_table(old_path)
    new, new_states = load_table(new_path)
    assert len(old_states) == 245 and len(new_states) == 244
    assert new_states == old_states - {122}
    expected = {
        (92, 1): (1, "R", 66),
        (104, 1): (1, "R", 92),
        (106, 1): (1, "R", 92),
        (167, 1): (1, "L", 151),
    }
    assert {(q, b): row for (q, b), row in new.items()
            if old.get((q, b)) != row} == expected
    assert set(old) - set(new) == {(122, 0), (122, 1)}

    # Inductive local invariant at equal-configuration boundaries:
    # q68: t[-1]=1;
    # q81: t[-1]=0 or (t[-2]=1 and t[-1]=1);
    # q167: t[-1]=1.
    # All of these are vacuous at the common initial state q95.
    forced_incoming = {
        68: [(52, 1, 1, "R", 68), (123, 1, 1, "R", 68)],
        81: [(68, 1, 1, "R", 81), (123, 0, 0, "R", 81)],
        167: [(145, 1, 1, "R", 167), (148, 1, 1, "R", 167)],
    }
    for table in (old, new):
        for target, rows in forced_incoming.items():
            assert incoming(table, target) == rows
    assert START not in INTERNAL | set(forced_incoming)

    # Every unchanged ordinary boundary edge stays within the boundary
    # domain. Each possible edge into an excluded state begins a macro.
    ordinary = []
    for q in sorted(old_states - INTERNAL):
        for bit in (0, 1):
            if (q, bit) in MACRO_ROWS:
                continue
            assert old[q, bit] == new[q, bit]
            assert old[q, bit][2] not in INTERNAL
            ordinary.append((q, bit))
    for table in (old, new):
        for (q, bit), row in table.items():
            if q not in INTERNAL and row[2] in INTERNAL:
                assert (q, bit) in MACRO_ROWS

    # The context cases are an exhaustive, disjoint partition of each
    # macro row under the inductive invariant and the binary alphabet.
    cases = []
    for q in (104, 106):
        for bit in (0, 1):
            cases.append((f"q{q}_next{bit}", q, {0: 1, 1: bit},
                          2, 4 if bit == 0 else 2,
                          25 if bit == 0 else 66, 2, {}))
    cases.extend([
        ("q167_left1", 167, {-1: 1, 0: 1}, 2, 2, 24, -2, {}),
        ("q81_left0", 81, {-1: 0, 0: 1}, 2, 2, 107, -2, {}),
        ("q81_left11", 81, {-2: 1, -1: 1, 0: 1},
         6, 4, 2, -2, {-1: 0, 0: 0}),
    ])
    checked = []
    covered_rows = set()
    for name, q, context, old_steps, new_steps, target, head, changes in cases:
        a, old_trace = trace(old, q, context, old_steps)
        b, new_trace = trace(new, q, context, new_steps)
        final_tape = dict(context)
        final_tape.update(changes)
        assert a == b == (target, head, final_tape)
        assert target not in INTERNAL | set(forced_incoming)
        assert old_steps > 0 and new_steps > 0
        assert 2 * old_steps <= 3 * new_steps and new_steps <= 2 * old_steps
        covered_rows.add((q, context[0]))
        checked.append(dict(name=name, state=q,
                            context={str(k): v for k, v in sorted(context.items())},
                            target=target, head_offset=head,
                            old=old_trace, new=new_trace,
                            same_entire_tape=True,
                            target_satisfies_invariant=True))
    assert covered_rows == MACRO_ROWS

    return dict(
        status="PASS_LOCAL_STUTTERING_CERTIFICATE",
        old_sha256=hashlib.sha256(old_path.read_bytes()).hexdigest(),
        new_sha256=hashlib.sha256(new_path.read_bytes()).hexdigest(),
        old_working_states=len(old_states), new_working_states=len(new_states),
        common_start=START, common_halt=HALT,
        changed_retained_rows=[list(key) for key in sorted(expected)],
        removed_state=122,
        ordinary_equal_rows=len(ordinary), local_cases=len(checked),
        local_old_steps=sum(c[3] for c in cases),
        local_new_steps=sum(c[4] for c in cases),
        invariant_incoming_rows={str(k): v for k, v in forced_incoming.items()},
        local_cases_detail=checked,
        theorem_scope="Same initial tape and head, state 95: halting equivalence on every binary tape.",
        formalization="Finite local lemma and stuttering induction are PA-formalizable; no new kernel replay claimed.",
        running_time_bound="For halting runs: 2*T_old <= 3*T_new and T_new <= 2*T_old.",
        exact_running_time_change="T_new = T_old + 2*A - 2*B; A counts q104/q106 next0 blocks; B counts q81 left11 blocks.",
        no_register_invariant_or_blank_boot_assumption=True,
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("old_table", type=Path)
    parser.add_argument("new_table", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    assert __debug__, "Run without -O: assertions implement the finite checker."
    result = verify(args.old_table, args.new_table)
    encoded = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(encoded)
    print(json.dumps({k: v for k, v in result.items()
                      if k not in ("local_cases_detail", "invariant_incoming_rows")}, indent=2))


if __name__ == "__main__":
    main()
