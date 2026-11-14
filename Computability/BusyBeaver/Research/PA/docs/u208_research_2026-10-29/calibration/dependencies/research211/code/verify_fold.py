#!/usr/bin/env python3
"""Complete incoming-edge and opaque-exterior certificate for the final fold.

All checks are explicit and remain enabled under Python -O. This is a finite
structural checker supporting the written induction proof, not a PA kernel.
"""
from pathlib import Path
import copy
import json
from core import census, read_table, require, write_json

ROOT = Path(__file__).resolve().parents[1]
KEEP, DROP, HELPER, LEFT, RIGHT = 220, 181, 129, 158, 204


def incoming(table, target):
    return sorted((q, b, w, d) for (q, b), (w, d, z) in table.items() if z == target)


def trace(table, state, cells, count):
    head, tape, log = 0, dict(cells), []
    for _ in range(count):
        require(state != 254, "Interior halt")
        require(head in tape, "An opaque exterior cell was read")
        bit = tape[head]
        write, move, target = table[state, bit]
        log.append([state, head, bit, write, move, target])
        tape[head] = write
        head += move
        state = target
    return (state, head, tape), log


def certify(old, new):
    census(old, 212, 254)
    census(new, 211, 254)
    require(set(old) - set(new) == {(DROP, 0), (DROP, 1)}, "Deleted-state domain")
    require(not set(new) - set(old), "Unexpected new row")
    require(old[KEEP, 0] == (0, 1, 218), "Left-tag zero row")
    require(old[DROP, 0] == (0, 1, 147), "Right-tag zero row")
    require(old[KEEP, 1] == old[DROP, 1] == (1, 1, 176), "Common one row")
    require(incoming(old, KEEP) == [(216, 0, 0, 1)], "Complete left-tag census")
    require(incoming(old, DROP) == [(185, 1, 1, 1)], "Complete right-tag census")
    require(0 not in (KEEP, DROP), "Tagged state is initial")
    require(len({KEEP, DROP, HELPER, LEFT, RIGHT}) == 5, "Circular helpers")
    require(new[HELPER, 0] == (0, 1, LEFT), "Final zero helper")
    require(new[HELPER, 1] == (1, 1, RIGHT), "Final one helper")
    require(new[LEFT, 0] == (0, 1, 218), "Final left helper result")
    require(new[RIGHT, 0] == (0, 1, 147), "Final right helper result")
    require(new[KEEP, 0] == (0, -1, HELPER), "Backward selector entry")
    rename = lambda q: KEEP if q == DROP else q
    for (q, bit), (write, move, target) in old.items():
        if q in (KEEP, DROP):
            continue
        require(new[q, bit] == (write, move, rename(target)),
                f"Ordinary row fails to commute: {q}/{bit}")
    require(new[KEEP, 1] == old[KEEP, 1], "Changed common branch")
    cases = []
    for old_state, tag in ((KEEP, 0), (DROP, 1)):
        for bit in (0, 1):
            tape = {-1: tag, 0: bit}
            old_end, old_log = trace(old, old_state, tape, 1)
            new_count = 3 if bit == 0 else 1
            new_end, new_log = trace(new, KEEP, tape, new_count)
            require(new_end == (rename(old_end[0]), old_end[1], old_end[2]),
                    "Whole-tape local identity")
            require(old_end[2] == tape, "Local block changed tape")
            cases.append({"old_state": old_state, "tag": tag, "read": bit,
                          "old_steps": 1, "new_steps": new_count,
                          "old_trace": old_log, "new_trace": new_log,
                          "endpoint_state": old_end[0], "endpoint_head": old_end[1]})
    return cases


def main():
    old = read_table(ROOT / "machine/rotated212.native.tm")
    new = read_table(ROOT / "machine/u211.native.tm")
    cases = certify(old, new)
    mutations = []
    # Corrupt both tables where appropriate, so a nominal patch check alone
    # cannot accept damaged incoming tags or damaged helper semantics.
    for name, row, component in [
        ("left entry tag", (216, 0), 0),
        ("right entry tag", (185, 1), 0),
        ("left entry direction", (216, 0), 1),
        ("right entry direction", (185, 1), 1),
        ("helper zero write", (129, 0), 0),
        ("helper one write", (129, 1), 0),
        ("left result write", (158, 0), 0),
        ("right result direction", (204, 0), 1),
        ("common result write", (220, 1), 0),
    ]:
        a, b = dict(old), dict(new)
        for table in (a, b):
            action = list(table[row])
            action[component] = 1 - action[component] if component == 0 else -action[component]
            table[row] = tuple(action)
        try:
            certify(a, b)
        except ValueError:
            mutations.append(name)
        else:
            raise ValueError("Mutation incorrectly accepted: " + name)
    for name, row, action in [
        ("backward selector move", (220, 0), (0, 1, 129)),
        ("ordinary target", (0, 0), (1, 1, 66)),
        ("circular helper", (129, 0), (0, 1, 220)),
    ]:
        damaged = {**new, row: action}
        try:
            certify(old, damaged)
        except ValueError:
            mutations.append(name)
        else:
            raise ValueError("Mutation incorrectly accepted: " + name)
    result = {"status": "UNIVERSAL_LOCAL_FOLD_PASS", "cases": cases,
              "old_states": 212, "new_states": 211,
              "incoming_keep": incoming(old, KEEP), "incoming_drop": incoming(old, DROP),
              "ordinary_rows_checked": 420, "mutations_rejected": mutations,
              "time_identity": "T_new = T_old + 2*k; T_old <= T_new <= 3*T_old",
              "scope": "All common initial tapes from state 0, for the final fold only. "
                       "The source-address rotations use a different simulation relation."}
    write_json(ROOT / "evidence/fold.json", result)
    print(json.dumps({k: v for k, v in result.items() if k != "cases"}, indent=2))


if __name__ == "__main__":
    main()
