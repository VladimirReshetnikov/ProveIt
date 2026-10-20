#!/usr/bin/env python3
"""Independent all-tape macro-diamond proof of the two continuation changes.

Old and new machines synchronize on identical state, head and complete tape.
Unchanged rows use a one-step block. Changed rows use the explicitly checked
positive blocks below. Initial tape is arbitrary; the old constant-bit
invariant is derived from an unrestricted start and independently rechecked.
"""
from collections import deque
from pathlib import Path
import hashlib
import json

import argparse, os, sys
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--old', type=Path, required=True)
parser.add_argument('--machines', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
if not __debug__ or sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE'):
    raise RuntimeError('Assertions must remain enabled')


def read(path):
    table = {}
    start = None
    for line in path.read_text().splitlines():
        if line.startswith("#! start "):
            assert start is None
            start = int(line[9:])
        elif line and not line.startswith("#"):
            q, bit, write, direction, target = line.split()
            key = int(q), int(bit)
            assert key not in table
            table[key] = int(write), 1 if direction == "R" else -1, int(target)
    states = {q for q, bit in table}
    assert start == 0 and 254 not in states
    assert set(table) == {(q, b) for q in states for b in (0, 1)}
    assert {z for w, d, z in table.values()} - states == {254}
    return table


def invariant(table, radius=8):
    facts = {0: {}}
    todo = deque([0])
    while todo:
        q = todo.popleft()
        if q == 254:
            continue
        for bit in (0, 1):
            known = facts[q]
            if 0 in known and known[0] != bit:
                continue
            write, direction, target = table[q, bit]
            after = {
                offset - direction: value for offset, value in known.items()
                if -radius <= offset - direction <= radius
            }
            after[-direction] = write
            if target in facts:
                after = {k: v for k, v in after.items() if facts[target].get(k) == v}
            if target not in facts or after != facts[target]:
                facts[target] = after
                todo.append(target)
    states = {q for q, bit in table}
    assert set(facts) == states | {254} and facts[0] == {}
    # This is the proof check; it does not trust the derivation above.
    for q in states:
        for bit in (0, 1):
            before = dict(facts[q])
            if 0 in before and before[0] != bit:
                continue
            before[0] = bit
            write, direction, target = table[q, bit]
            for offset, value in facts[target].items():
                assert (write if offset + direction == 0
                        else before.get(offset + direction)) == value
    return facts


def run(table, q, initial, ticks):
    tape, head, trace = dict(initial), 0, []
    for _ in range(ticks):
        assert q != 254 and head in tape
        before = q, head, tape[head]
        write, direction, target = table[q, tape[head]]
        tape[head] = write
        head += direction
        q = target
        trace.append([*before, write, direction, q])
    assert q != 254
    # Unknown cells were never accessed or written, so they remain identical.
    return (q, head, tape), trace


old_path = args.old
old = read(old_path)
facts = invariant(old)
assert facts[103][-1] == 1
out = []
for name in ("row103", "row157", "both"):
    new_path = args.machines / name / "k221.native.tm"
    new = read(new_path)
    assert set(new) == set(old)
    changed = {row for row in old if old[row] != new[row]}
    expected = {(103, 1), (157, 1)} if name == "both" else {
        (103 if name == "row103" else 157, 1)}
    assert changed == expected
    cases = []
    specs = []
    if (103, 1) in changed:
        assert new[103, 1] == (0, -1, 142)
        specs.append((103, {-1: 1, 0: 1}, 2, 2, "old inductive left bit 1"))
    if (157, 1) in changed:
        assert new[157, 1] == (1, -1, 187)
        specs += [
            (157, {-1: 0, 0: 1}, 2, 2, "left bit 0"),
            (157, {-1: 1, 0: 1}, 1, 3, "left bit 1"),
        ]
    for q, initial, old_ticks, new_ticks, guard in specs:
        a, ta = run(old, q, initial, old_ticks)
        b, tb = run(new, q, initial, new_ticks)
        assert a == b
        cases.append({
            "entry_state": q, "known_patch": initial, "guard": guard,
            "old_steps": old_ticks, "new_steps": new_ticks,
            "old_trace": ta, "new_trace": tb,
            "common_endpoint": a,
        })
    out.append({
        "variant": name,
        "status": "ALL_TAPE_POSITIVE_MACRO_DIAMONDS_PASS",
        "old_sha256": hashlib.sha256(old_path.read_bytes()).hexdigest(),
        "new_sha256": hashlib.sha256(new_path.read_bytes()).hexdigest(),
        "old_rows": len(old), "new_rows": len(new),
        "unchanged_rows": len(old) - len(changed),
        "diamonds": cases,
    })
receipt = {
    "status": "ALL_THREE_ALTERNATE_K221_TABLES_PROVED_HALTING_EQUIVALENT",
    "scope": (
        "Every initial binary tape and integer head position from state0. "
        "Synchronization has identical state, head and whole tape. "
        "Every old block consumes one or two transitions, every new block "
        "one to three, no interior halt. Constant-bit invariant rechecked "
        "inductive from an unrestricted start. Ordinary executable proof, "
        "not a proof-assistant theorem."
    ),
    "old_invariant_facts": sum(map(len, facts.values())),
    "old_state103_facts": facts[103],
    "variants": out,
    "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
}
args.output.write_text(json.dumps(receipt, indent=2) + "\n")
print(json.dumps({k: v for k, v in receipt.items() if k != "variants"}, indent=2))
