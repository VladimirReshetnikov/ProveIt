#!/usr/bin/env python3
"""Replay the stated 876-action finite loader-entry screen.

This checks a bounded acceptance condition, not arbitrary execution times.
The table must be the exact published native219 table. The surviving CD0
positive-input entry is then refuted by a concrete zero-input frame.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
PHYSICAL = (6, 2, 0, 4, 3, 7, 8, 5, 1)


def read_table(path):
    table = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        q, b, w, d, z = line.split()
        table[int(q), int(b)] = (int(w), 1 if d == "R" else -1, int(z))
    return table


def frame(pc, regs, gap, spares, origin=0):
    physical = [0] * 9
    for logical, index in enumerate(PHYSICAL):
        physical[index] = regs[logical]
    ones = {origin - 1, origin + 64 + gap}
    ones.update(origin + i for i, c in enumerate(pc) if c == "1")
    cursor = origin + 65 + gap
    for value in physical + [1] * spares:
        cursor += 1
        ones.update(range(cursor, cursor + value + 1))
        cursor += value + 1
    return ones


def increment(pc):
    if not pc:
        return "", 1
    value = int(pc, 2) + 1
    return format(value % (1 << len(pc)), "0" + str(len(pc)) + "b"), value >> len(pc)


def expected(pc, op, arg, regs, gap, spares):
    regs = regs[:]
    delta = 0
    if op == "CI":
        regs[arg] += 1
        spares += 1
        nxt, shift = increment(pc)
    elif regs[arg]:
        regs[arg] -= 1
        delta = 1
        nxt, shift = increment(pc)
    else:
        nxt, shift = increment(pc[:pc.rfind("0")])
    return 84, -shift, frame(nxt, regs, gap + delta + shift, spares, -shift)


def run(table, site, action, regs, stop_wrong_dispatch=False):
    pc, op, arg = site
    native = dict(table)
    for i, bb in enumerate(pc):
        q = 84 if i == 0 else 1000 + i
        for bit in (0, 1):
            native[q, bit] = (bit, 1, 254)
        native[q, int(bb)] = action if i == len(pc) - 1 else (int(bb), 1, 1001 + i)
    ones = frame(pc, regs, 3, 3)
    wanted = expected(pc, op, arg, regs, 3, 3)
    q, head = 84, 0
    for tick in range(12000):
        if tick and (q, head, ones) == wanted:
            return dict(accepted=True, steps=tick)
        if stop_wrong_dispatch and tick > len(pc) and q == 84:
            return dict(accepted=False, reason="wrong_dispatch", steps=tick,
                        actual_state=q, actual_head=head, wanted_state=wanted[0],
                        wanted_head=wanted[1], actual_ones=sorted(ones),
                        wanted_ones=sorted(wanted[2]))
        if q == 254:
            return dict(accepted=False, reason="halt", steps=tick)
        w, d, q = native[q, int(head in ones)]
        if w:
            ones.add(head)
        else:
            ones.discard(head)
        head += d
    return dict(accepted=False, reason="bounded_filter_not_met", steps=12000)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--table", type=Path, required=True)
    ap.add_argument("--output", type=Path, default=HERE / "loader_entry_scope.json")
    args = ap.parse_args()
    digest = hashlib.sha256(args.table.read_bytes()).hexdigest()
    assert digest == "b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26"
    table = read_table(args.table)
    states = sorted({q for q, bit in table})
    assert len(states) == 219
    regs = [2, 0, 3, 1, 2, 1, 0, 2, 1]
    records = []
    for site in (("00", "CI", 0), ("11110", "CD", 0)):
        survivors = []
        for act in itertools.product((0, 1), (-1, 1), states):
            if run(table, site, act, regs)["accepted"]:
                survivors.append(act)
        assert survivors == ([] if site[1] == "CI" else [(0, 1, 8)])
        record = dict(site=site, tested_actions=4 * len(states), finite_survivors=survivors)
        if survivors:
            zero = run(table, site, survivors[0], [0] * 9, True)
            assert zero["reason"] == "wrong_dispatch" and zero["steps"] == 160
            assert zero["actual_head"] == 0 and zero["wanted_head"] == -1
            record["zero_branch_counterexample"] = zero
        records.append(record)
    result = dict(
        status="FIXED_BOUNDED_ENTRY_SCREEN_REPRODUCED",
        table_sha256=digest,
        nonhalting_target_states=219, finite_step_limit=12000,
        finite_registers=regs, gap=3, spares=[1, 1, 1],
        records=records,
        scope=("All 876 one-row actions are tested under the stated finite "
               "acceptance condition. No action passes it and the zero-branch "
               "counterexample. This does not rule out entries taking longer "
               "than the filter limit, changed runtime rows, or other addresses."),
    )
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "records"}, indent=2))


if __name__ == "__main__":
    main()
