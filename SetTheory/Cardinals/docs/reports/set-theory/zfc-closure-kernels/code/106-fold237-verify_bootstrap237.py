#!/usr/bin/env python3
"""Independently rebuild237 and verify its exact blank startup.

The local all-tape proof is supplied separately. This check exhausts the
finite startup with two tape representations and canonical state labels.
"""

from collections import Counter
from pathlib import Path
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parent
OLD_HASH = "069942be27db9736875ea042320e51ac3b1eac7116cbe01cdce520fa6056f78c"
NEW_HASH = "a3c4407f30e2e2139af87c6a91948c518134855841a28eb85b1d81bcfd026c9a"
CAN_HASH = "7eda1da1fcda629cae86d22b01d3faf419552cf04ed4179f0c045ad0adf2c1a6"
STEPS = 409835


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def parse(raw):
    result = {}
    for line in raw.decode("ascii").splitlines():
        if not line or line.startswith("#"):
            continue
        q, b, w, d, t = line.split()
        q, b, w, t = map(int, (q, b, w, t))
        assert b in (0, 1) and w in (0, 1) and d in ("L", "R")
        assert (q, b) not in result
        result[q, b] = w, 1 if d == "R" else -1, t
    return result


def encode(table, start):
    return (f"#! start {start}\n" + "".join(
        f"{q} {b} {w} {'R' if d == 1 else 'L'} {t}\n"
        for (q, b), (w, d, t) in sorted(table.items())
    )).encode("ascii")


def sparse_step(table, state, head, tape):
    w, d, t = table[state, int(head in tape)]
    if w:
        tape.add(head)
    else:
        tape.discard(head)
    return t, head + d


def main():
    assert __debug__ and not sys.flags.optimize, "Run without -O/-OO"
    oldraw = (ROOT / "inputs" / "zfc_composed238_old.tm").read_bytes()
    assert digest(oldraw) == OLD_HASH
    old = parse(oldraw)
    assert len(old) == 476
    phi = lambda q: 98 if q == 235 else q
    new = {(q, b): (w, d, phi(t)) for (q, b), (w, d, t) in old.items() if q != 235}
    new[98, 0] = (0, -1, 240)
    new[240, 1] = (1, -1, 87)
    working = {q for q, b in new}
    assert len(working) == 237 and len(new) == 474
    assert set(new) == {(q, b) for q in working for b in (0, 1)}
    assert {t for w, d, t in new.values()} - working == {254}
    newraw = encode(new, 95)
    assert digest(newraw) == NEW_HASH
    assert (ROOT / "zfc_composed237_old.tm").read_bytes() == newraw
    changed = {key for key in new if new[key] != old[key]}
    assert changed == {(98, 0), (139, 1), (156, 1), (240, 1)}

    order = [95] + sorted(working - {95})
    numbering = {q: i for i, q in enumerate(order)} | {254: 237}
    canonical = {(numbering[q], b): (w, d, numbering[t]) for (q, b), (w, d, t) in new.items()}
    canraw = encode(canonical, 0)
    assert digest(canraw) == CAN_HASH
    assert (ROOT / "zfc_composed237.tm").read_bytes() == canraw
    assert set(canonical) == {(q, b) for q in range(237) for b in (0, 1)}
    pending, reachable = [95], set()
    while pending:
        state = pending.pop()
        if state in reachable:
            continue
        reachable.add(state)
        if state != 254:
            pending.extend(new[state, bit][2] for bit in (0, 1))
    assert reachable == working | {254}

    old_state = new_state = 95
    old_head = new_head = 0
    old_tape, new_tape, visits = set(), set(), Counter()
    for tick in range(STEPS):
        assert (old_state, old_head, old_tape) == (new_state, new_head, new_tape), ("before", tick)
        visits[old_state, int(old_head in old_tape)] += 1
        old_state, old_head = sparse_step(old, old_state, old_head, old_tape)
        new_state, new_head = sparse_step(new, new_state, new_head, new_tape)
        assert (old_state, old_head, old_tape) == (new_state, new_head, new_tape), ("after", tick)
    assert (new_state, new_head, len(new_tape)) == (96, -5, 351)
    assert all(visits[key] == 0 for key in changed | {(235, 0), (235, 1)})

    # Independent dense representation and canonical control labels.
    offset = STEPS + 1
    tape = bytearray(2 * STEPS + 3)
    position, state = offset, 0
    for _ in range(STEPS):
        w, d, following = canonical[state, tape[position]]
        tape[position] = w
        position += d
        state = following
    dense_ones = {i - offset for i, b in enumerate(tape) if b}
    assert (state, position - offset, dense_ones) == (numbering[new_state], new_head, new_tape)

    header = min(p for p in new_tape if p >= new_head)
    assert min(new_tape) == new_head - 1
    values, position = [], header + 1
    while position <= max(new_tape):
        assert position not in new_tape and position + 1 in new_tape
        first = position + 1
        position = first
        while position in new_tape:
            position += 1
        values.append(position - first - 1)
    physical_map = (6, 2, 0, 4, 3, 7, 8, 5, 1)
    logical = [values[j] for j in physical_map]
    assert logical == [3, 0, 0, 0, 3, 0, 0, 0, 0]
    assert len(values[9:]) == 167 and set(values[9:]) == {1}
    result = {
        "status": "PASS_TABLE_CONSTRUCTION_ALL_BOOT_CHECKPOINTS_AND_DENSE_CANONICAL",
        "working_states": 237, "transition_rows": 474,
        "old238_sha256": OLD_HASH, "inherited237_sha256": NEW_HASH,
        "canonical237_sha256": CAN_HASH,
        "source_sites_sha256": digest((ROOT / "inputs" / "sites_logical.json").read_bytes()),
        "all_working_states_graph_reachable": True,
        "retained_row_changes": [{"state": q, "read": b, "old": old[q, b], "new": new[q, b]} for q, b in sorted(changed)],
        "deleted_state": 235, "steps": STEPS,
        "distinct_checkpoints_compared": STEPS + 1,
        "comparison_includes_complete_tape": True,
        "new_fold_changed_or_deleted_row_visits": {f"{q}/{b}": visits[q, b] for q, b in sorted(changed | {(235, 0), (235, 1)})},
        "final_state_old": new_state, "final_state_canonical": state,
        "head": new_head, "marker": new_head - 1,
        "header": header, "header_distance": header - new_head,
        "pc": "", "logical_registers": logical,
        "physical_registers": values[:9], "spare_values": values[9:],
        "all_one_positions": sorted(new_tape), "all_other_cells_zero": True,
        "one_count": len(new_tape), "complete_configuration_matches_composed238": True,
    }
    target = ROOT / "evidence" / "bootstrap237.json"
    target.parent.mkdir(exist_ok=True)
    target.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k not in ("all_one_positions", "spare_values")}, indent=2))


if __name__ == "__main__":
    main()
