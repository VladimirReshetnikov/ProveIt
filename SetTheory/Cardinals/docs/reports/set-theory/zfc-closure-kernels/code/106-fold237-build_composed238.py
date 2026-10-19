#!/usr/bin/env python3
"""Construct and check the exact 238-state composition.

This checker uses only Python's standard library. It independently checks the
literal table edits, totality, canonical numbering, a finite tape invariant,
four exact local blocks, every old startup checkpoint, and a separately
implemented dense simulation of the canonical machine. Universal source
runtime correctness and source calibration are separate certificates.
"""

from collections import Counter
from pathlib import Path
import hashlib
import itertools
import json
import sys


ROOT = Path(__file__).resolve().parent
INPUT = ROOT / "inputs" / "zfc_boundary239_old.tm"
SITES = ROOT / "inputs" / "sites_logical.json"
OLD_SHA = "d061770f487937f9da652919c9bc9bb79bc9bf137ca41dd7a08eb5ecda8e7719"
SITES_SHA = "7fd152d1f5371d2a561d4ad1870d241683b010ce7b7a27399b95363a4537cfb6"
FINAL_SHA = "069942be27db9736875ea042320e51ac3b1eac7116cbe01cdce520fa6056f78c"
CANONICAL_SHA = "909f29c493e0ccc5d6a481fd7a20a9a82eb934ab2aa7df17b5ec3789255a8c08"
START, DISPATCH, HALT = 95, 96, 254
BOOT_OLD_STEPS, BOOT_NEW_STEPS = 409691, 409835
PHY = (6, 2, 0, 4, 3, 7, 8, 5, 1)


def require(condition, detail):
    if not condition:
        raise AssertionError(detail)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def parse(data):
    table = {}
    for line in data.decode("ascii").splitlines():
        if not line or line.startswith("#"):
            continue
        parts = line.split()
        require(len(parts) == 5, ("Malformed transition", line))
        q, b, w, direction, target = parts
        q, b, w, target = map(int, (q, b, w, target))
        require((q, b) not in table, ("Duplicate transition", q, b))
        require(b in (0, 1) and w in (0, 1) and direction in ("L", "R"), line)
        table[q, b] = (w, 1 if direction == "R" else -1, target)
    states = {q for q, b in table}
    require(set(table) == {(q, b) for q in states for b in (0, 1)}, "Partial table")
    require({target for w, d, target in table.values()} - states == {HALT}, "Wrong halt")
    return table


def encode(table, start):
    return ("#! start " + str(start) + "\n" + "".join(
        f"{q} {b} {w} {'R' if d == 1 else 'L'} {target}\n"
        for (q, b), (w, d, target) in sorted(table.items())
    )).encode("ascii")


def phi(q):
    return 80 if q == 169 else q


def invariant(q, head, tape):
    return (
        (q != 67 or tape[head - 1] == 0)
        and (q != 80 or (tape[head - 1] == 1 and tape[head - 2] == 0))
        and (q != 91 or (tape[head - 1] == 1 and tape[head - 2] == 1 and tape[head - 3] == 0))
        and (q != 169 or tape[head - 1] == 0)
    )


def local(table, state, tape, steps):
    tape, head, trace = dict(tape), 0, []
    for _ in range(steps):
        require(head in tape, ("An exterior cell would be read", state, head))
        require(state != HALT, "Interior halt")
        b = tape[head]
        w, d, target = table[state, b]
        trace.append([state, head, b, w, d, target])
        tape[head], state, head = w, target, head + d
    return (state, head, tape), trace


def sparse_step(table, state, head, ones):
    w, d, target = table[state, int(head in ones)]
    if w:
        ones.add(head)
    else:
        ones.discard(head)
    return target, head + d


def dense_run(canonical, steps):
    # Independent representation and step loop. The allocation exceeds the
    # maximum possible displacement of any run of the specified length.
    offset = steps + 1
    tape = bytearray(2 * steps + 3)
    position, state = offset, 0
    for _ in range(steps):
        write, direction, following = canonical[state, tape[position]]
        tape[position] = write
        position += direction
        state = following
    return state, position - offset, {i - offset for i, bit in enumerate(tape) if bit}


def main():
    require(__debug__ and not sys.flags.optimize, "Run without -O or -OO")
    old_bytes = INPUT.read_bytes()
    require(sha(old_bytes) == OLD_SHA, "The 239-state boundary input changed")
    require(sha(SITES.read_bytes()) == SITES_SHA, "The calibrated boundary source changed")
    old = parse(old_bytes)
    require(len(old) == 478, "Expected 239 working states")
    require(old[80, 0] == (0, 1, 25), "Unexpected 80/0")
    require(old[91, 1] == (0, -1, 50), "Unexpected 91/1")
    require(old[147, 0] == (0, 1, 169), "Unexpected 147/0")
    require(old[169, 0] == (0, 1, 57) and old[169, 1] == (0, 1, 56), "Unexpected deleted rows")

    new = {(q, b): (w, d, phi(target)) for (q, b), (w, d, target) in old.items() if q != 169}
    new[80, 0] = (0, -1, 106)
    new[91, 1] = (1, -1, 167)
    changed = [key for key in sorted(new) if new[key] != old[key]]
    require(changed == [(80, 0), (91, 1), (147, 0)], "Unexpected retained-row changes")
    working = {q for q, b in new}
    require(len(working) == 238 and len(new) == 476, "Incorrect state count")
    require(set(new) == {(q, b) for q in working for b in (0, 1)}, "New table is partial")
    require({t for w, d, t in new.values()} - working == {HALT}, "Incorrect final halt")
    final_bytes = encode(new, START)
    require(sha(final_bytes) == FINAL_SHA, "Unexpected inherited-label output hash")
    (ROOT / "zfc_composed238_old.tm").write_bytes(final_bytes)

    order = [START] + sorted(working - {START})
    numbering = {q: i for i, q in enumerate(order)} | {HALT: 238}
    canonical = {(numbering[q], b): (w, d, numbering[t]) for (q, b), (w, d, t) in new.items()}
    require(set(canonical) == {(q, b) for q in range(238) for b in (0, 1)}, "Incorrect renumbering")
    canonical_bytes = encode(canonical, 0)
    require(sha(canonical_bytes) == CANONICAL_SHA, "Unexpected canonical output hash")
    (ROOT / "zfc_composed238.tm").write_bytes(canonical_bytes)
    for (q, b), (w, d, t) in new.items():
        require(canonical[numbering[q], b] == (w, d, numbering[t]), "Noncommuting relabel")
    reached, pending = set(), [START]
    while pending:
        q = pending.pop()
        if q in reached:
            continue
        reached.add(q)
        if q != HALT:
            pending.extend(new[q, b][2] for b in (0, 1))
    require(reached == working | {HALT}, "Unexpected graph-unreachable state")
    write_json(ROOT / "renumbering238.json", {"old_to_new": numbering, "new_to_old": order + [HALT]})

    incoming = {
        q: [[p, b, w, d] for (p, b), (w, d, target) in sorted(old.items()) if target == q]
        for q in (67, 80, 91, 169)
    }
    require(incoming == {
        67: [[52, 0, 0, 1], [124, 0, 0, 1]],
        80: [[67, 1, 1, 1]],
        91: [[80, 1, 1, 1]],
        169: [[147, 0, 0, 1]],
    }, "Boundary source changed the invariant's predecessor inventory")
    invariant_cases = 0
    for bits in itertools.product((0, 1), repeat=9):
        tape = dict(zip(range(-4, 5), bits))
        require(invariant(START, 0, tape), "Initial invariant failed")
        for state in {q for q, b in old}:
            if not invariant(state, 0, tape):
                continue
            w, d, target = old[state, tape[0]]
            updated = dict(tape)
            updated[0] = w
            require(invariant(target, d, updated), ("Invariant closure failed", state, tape))
            invariant_cases += 1

    specifications = [
        (80, 0, {-1: 1}, 5, [80, 106, 92, 107, 125, 25]),
        (169, 0, {-1: 0}, 3, [80, 106, 93, 57]),
        (169, 1, {-1: 0, 1: 1}, 5, [80, 91, 167, 151, 173, 56]),
        (91, 1, {-3: 0, -2: 1, -1: 1}, 9, [91, 167, 151, 24, 36, 54, 71, 82, 94, 50]),
    ]
    block_records = []
    for state, read, guard, duration, path in specifications:
        admitted, example = 0, None
        for bits in itertools.product((0, 1), repeat=5):
            tape = dict(zip(range(-3, 2), bits))
            if tape[0] != read or any(tape[p] != b for p, b in guard.items()):
                continue
            goal, old_trace = local(old, state, tape, 1)
            actual, new_trace = local(new, phi(state), tape, duration)
            require(actual == (phi(goal[0]), goal[1], goal[2]), ("Block mismatch", state, read, tape))
            require([row[0] for row in new_trace] + [actual[0]] == path, "Path changed")
            admitted += 1
            example = {"old": old_trace, "new": new_trace}
        require(admitted > 0, "Empty local guard")
        block_records.append({
            "old_state": state, "read": read, "guard": guard,
            "old_steps": 1, "new_steps": duration, "path": path,
            "finite_assignments": admitted, "footprint": [-3, 1],
            "all_exterior_cells_unread_and_unchanged": True, "example": example,
        })
    exceptions = {(q, b) for q, b, g, d, p in specifications}
    commuting = 0
    for (q, b), (w, d, target) in old.items():
        if (q, b) not in exceptions:
            require(new[phi(q), b] == (w, d, phi(target)), ("Ordinary row failed", q, b))
            commuting += 1
    require(commuting == 474, "Incorrect ordinary-row census")

    old_state = new_state = START
    old_head = new_head = 0
    old_ones, new_ones = set(), set()
    new_clock, visits, guard_visits = 0, Counter(), 0
    durations = {(q, b): d for q, b, g, d, p in specifications}
    for tick in range(BOOT_OLD_STEPS):
        require((phi(old_state), old_head, old_ones) == (new_state, new_head, new_ones), ("Checkpoint before", tick))
        key = old_state, int(old_head in old_ones)
        if key == (169, 1):
            require(old_head + 1 in old_ones, ("Startup right-neighbor guard failed", tick))
            guard_visits += 1
        visits[key] += 1
        duration = durations.get(key, 1)
        old_state, old_head = sparse_step(old, old_state, old_head, old_ones)
        for _ in range(duration):
            new_state, new_head = sparse_step(new, new_state, new_head, new_ones)
        new_clock += duration
        require((phi(old_state), old_head, old_ones) == (new_state, new_head, new_ones), ("Checkpoint after", tick))
    require((old_state, old_head, len(old_ones)) == (DISPATCH, -5, 351), "Incorrect old startup endpoint")
    require(new_clock == BOOT_NEW_STEPS, "Incorrect new startup duration")
    require(new_clock == BOOT_OLD_STEPS + 4 * visits[80, 0] + 2 * visits[169, 0] + 4 * visits[169, 1] + 8 * visits[91, 1], "Clock equation failed")
    dense = dense_run(canonical, new_clock)
    require(dense == (numbering[new_state], new_head, new_ones), "Dense canonical startup disagrees")

    header = min(p for p in new_ones if p >= new_head)
    require(min(new_ones) == new_head - 1, "Unexpected left exterior")
    values, position = [], header + 1
    while position <= max(new_ones):
        require(position not in new_ones and position + 1 in new_ones, "Malformed register block")
        first = position + 1
        position = first
        while position in new_ones:
            position += 1
        values.append(position - first - 1)
    logical = [values[i] for i in PHY]
    require(logical == [3, 0, 0, 0, 3, 0, 0, 0, 0], "Incorrect source seed")
    require(len(values[9:]) == 167 and set(values[9:]) == {1}, "Incorrect spare list")
    evidence = ROOT / "evidence"
    evidence.mkdir(exist_ok=True)
    write_json(evidence / "local_fold238.json", {
        "status": "PASS_EXACT_FINITE_PREMISES",
        "input239_sha256": OLD_SHA, "output238_sha256": FINAL_SHA,
        "source_sha256": SITES_SHA,
        "initial_state_avoids_guarded_controls_on_every_tape": True,
        "incoming": incoming, "invariant_boolean_cases": invariant_cases,
        "invariant": {"67": "left=0", "80": "left=1, two-left=0", "91": "left=1, two-left=1, three-left=0", "169": "left=0"},
        "blocks": block_records, "ordinary_commuting_old_rows": commuting,
        "block_clock_minimum": 1, "block_clock_maximum": 9,
        "separate_runtime_premise": "Whenever old state169 reads1, the immediately right-hand cell is1. This checker proves the premise during the exact finite startup. A separate universal symbolic certificate is needed for valid runtime frames.",
        "interpretation": "The finite tests enumerate every Boolean assignment on all read and invariant cells. No block reads or writes the exterior. Thus they verify universal local identities on infinite binary tapes under the stated guards."
    })
    write_json(evidence / "bootstrap238.json", {
        "status": "PASS_ALL_OLD_CHECKPOINTS_AND_INDEPENDENT_DENSE_CANONICAL_RUN",
        "old_steps": BOOT_OLD_STEPS, "new_steps": new_clock,
        "distinct_old_checkpoints_compared": BOOT_OLD_STEPS + 1,
        "comparison_includes_complete_tape": True,
        "exceptional_visits": {f"{q}/{b}": visits[q, b] for q, b in sorted(exceptions)},
        "next_one_guard_visits": guard_visits,
        "final_state_old": new_state, "final_state_canonical": numbering[new_state],
        "head": new_head, "marker": new_head - 1,
        "header": header, "header_distance": header - new_head,
        "source_pc": "", "logical_registers": logical,
        "physical_registers": values[:9], "spare_values": values[9:],
        "all_one_positions": sorted(new_ones), "all_other_cells_zero": True,
        "one_count": len(new_ones),
    })
    result = {
        "status": "PASS_CONSTRUCTION_LOCAL_BLOCKS_AND_FINITE_STARTUP",
        "working_states": len(working), "transition_rows": len(new),
        "binary_symbols": [0, 1], "move_set": ["L", "R"],
        "start_canonical": 0, "halt_canonical": 238, "dispatcher_canonical": numbering[DISPATCH],
        "all_working_states_graph_reachable": True,
        "source239_sha256": OLD_SHA, "source_sites_sha256": SITES_SHA,
        "inherited_label_sha256": sha(final_bytes), "canonical_sha256": sha(canonical_bytes),
        "deleted_state": 169, "state_map": {"169": 80, "other": "identity"},
        "retained_row_changes": [{"state": q, "read": b, "old": old[q, b], "new": new[q, b]} for q, b in changed],
        "unchanged_retained_rows": len(new) - len(changed),
        "invariant_boolean_cases": invariant_cases, "local_blocks": len(block_records),
        "ordinary_commuting_old_rows": commuting,
        "startup_old_steps": BOOT_OLD_STEPS, "startup_new_steps": new_clock,
        "universal_runtime": "evidence/universal_runtime238.json (separate checker)",
    }
    write_json(evidence / "construction238.json", result)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
