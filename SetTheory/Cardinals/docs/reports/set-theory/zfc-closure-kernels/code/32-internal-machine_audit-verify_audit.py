#!/usr/bin/env python3
"""Verify finite results about the attributed public ZF253 machine.

This is a standard-library executable audit, not a Coq or Lean kernel proof.
No long blank-tape run is used as a consistency-equivalence certificate.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
DATA = HERE / "data"
TABLE_SHA = "84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95"
PROGRAM_SHA = "1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746"


def require(condition, explanation):
    if not condition:
        raise ValueError(explanation)


def read_table(path: Path, states: int):
    result = {}
    start = None
    for line in path.read_text().splitlines():
        if line.startswith("#! start "):
            require(start is None, "duplicate start declaration")
            start = int(line.split()[-1])
        elif line and not line.startswith("#"):
            q, bit, write, direction, target = line.split()
            key = int(q), int(bit)
            row = int(write), direction, int(target)
            require(key not in result, "duplicate transition")
            require(row[0] in (0, 1) and direction in ("L", "R"), "invalid action")
            require(0 <= row[2] <= states, "invalid target")
            result[key] = row
    require(start == 0, "wrong start state")
    require(set(result) == {(q, b) for q in range(states) for b in (0, 1)},
            "table must contain exactly two rows for every working state")
    return result


def refinement(table, labels):
    states = len(labels) - 1
    signatures = [tuple((w, direction, labels[target])
                        for w, direction, target in (table[q, 0], table[q, 1]))
                  for q in range(states)]
    signatures.append(("terminal",))
    classes = {}
    result = []
    for signature in signatures:
        if signature not in classes:
            classes[signature] = len(classes)
        result.append(classes[signature])
    return result


def execute(table, state, head, ones, steps):
    tape = set(ones)
    for _ in range(steps):
        key = state, int(head in tape)
        require(key in table, "unexpected earlier halt in finite witness")
        write, direction, state = table[key]
        if write:
            tape.add(head)
        else:
            tape.discard(head)
        head += 1 if direction == "R" else -1
    return {"steps": steps, "state": state, "head": head, "ones": sorted(tape)}


def instruction_paths():
    data = (DATA / "Prog254.v").read_bytes()
    require(hashlib.sha256(data).hexdigest() == PROGRAM_SHA, "register-program hash mismatch")
    body = data.decode().split("Definition p254_tab", 1)[1].split("[", 1)[1].split("].", 1)[0]
    edge = r"(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)"
    nodes = re.findall(r"\((" + edge + r"),\s*(" + edge + r")\)", body)
    require(len(nodes) == 6459, "wrong decoder node count")
    todo = [("CN 0", "")]
    leaves = []
    while todo:
        node, path = todo.pop()
        require(len(path) <= 34, "unexpected long path or cycle")
        kind, *argument = node.split()
        if kind == "CN":
            left, right = nodes[int(argument[0])]
            todo.extend(((right, path + "1"), (left, path + "0")))
        else:
            leaves.append((path, node))
    require(len(leaves) == 6460, "wrong instruction-site count")
    return leaves


def main():
    table_bytes = (DATA / "published_zfc253.tm").read_bytes()
    require(hashlib.sha256(table_bytes).hexdigest() == TABLE_SHA, "published table hash mismatch")
    table = read_table(DATA / "published_zfc253.tm", 253)
    certificate = json.loads((DATA / "noquotient253_certificate.json").read_text())
    require(certificate["machine_sha256"] == TABLE_SHA, "certificate attached to another machine")
    labels = [0] * 253 + [1]
    counts = [1]
    for expected in certificate["rounds"]:
        labels = refinement(table, labels)
        require(labels == expected, "partition certificate mismatch")
        counts.append(len(set(labels[:253])))
    require(counts == certificate["working_class_counts"], "partition count mismatch")
    require(counts == [1, 14, 60, 128, 195, 228, 235, 242, 247, 249, 251, 252, 253, 253],
            "unexpected distinguishing-depth profile")
    require(len(set(labels)) == 254, "some working states or the halt state still coincide")
    for item in certificate["last_split_witnesses"]:
        left, right = item["states"]
        separated = False
        for character in item["word"]:
            bit = int(character)
            action_left, action_right = table[left, bit], table[right, bit]
            if action_left[:2] != action_right[:2] or ((action_left[2] == 253) != (action_right[2] == 253)):
                separated = True
                break
            left, right = action_left[2], action_right[2]
        require(separated, "claimed distinguishing word does not distinguish the states")

    rejected = read_table(DATA / "rejected_detector252.tm", 252)
    rename = lambda q: q - int(q > 31)
    expected = {(rename(q), bit): (write, direction, rename(32 if (q, bit) == (30, 0) else target))
                for (q, bit), (write, direction, target) in table.items() if q != 31}
    require(rejected == expected, "rejected table is not the advertised one-state detector deletion")
    witness = json.loads((DATA / "detector252_counterexample.json").read_text())
    initial = witness["initial"]
    for name, selected, initial_state in (
            ("published_gate", table, initial["published_state"]),
            ("published_dispatch", table, initial["published_state"]),
            ("rejected_gate", rejected, initial["rejected_state"]),
            ("rejected_dispatch", rejected, initial["rejected_state"])):
        desired = witness[name]
        computed = execute(selected, initial_state, initial["head"], initial["ones"], desired["steps"])
        require(computed == desired, "counterexample endpoint differs: " + name)
    good, bad = witness["published_dispatch"], witness["rejected_dispatch"]
    require(good["head"] == 0 and good["state"] == 33, "published dispatch endpoint differs")
    require(bad["head"] == 11 and bad["state"] == 32, "rejected dispatch endpoint differs")
    require(min(bad["ones"]) < bad["head"] - 1,
            "rejected dispatch unexpectedly satisfies the blank-left-exterior invariant")

    leaves = instruction_paths()
    max_zero_run = max(max(map(len, path.split("1"))) for path, _ in leaves)
    trailing_seven = [(path, operation) for path, operation in leaves if path.endswith("0000000")]
    require(max_zero_run == 7 and len(trailing_seven) == 18, "zero-run census mismatch")
    require(all(operation.startswith("CD ") for _, operation in trailing_seven),
            "unexpected non-decrement instruction among the eighteen sites")
    require((witness["path"], "CD 1") in leaves, "counterexample is not an actual instruction site")

    summary = {
        "published_table_sha256": TABLE_SHA,
        "working_states": 253,
        "transition_rows": len(table),
        "partition_counts": counts,
        "first_discrete_round": 12,
        "last_split_states": [89, 152],
        "last_split_word": "101000000000",
        "instruction_sites": len(leaves),
        "maximum_zero_run": max_zero_run,
        "seven_trailing_zeros_sites": len(trailing_seven),
        "rejected_table_sha256": hashlib.sha256((DATA / "rejected_detector252.tm").read_bytes()).hexdigest(),
        "published_dispatch_step_head": [238, 0],
        "rejected_dispatch_step_head": [205, 11],
        "scope": "Finite source, quotient and invariant checks; no local Coq build and no new blank-tape consistency record."
    }
    (HERE / "audit_summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
