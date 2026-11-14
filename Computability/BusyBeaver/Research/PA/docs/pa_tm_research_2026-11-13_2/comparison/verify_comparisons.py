#!/usr/bin/env python3
"""Verify selected archive tables without executing any submitted code.

Checks byte identity, complete binary tables, graph reachability, rooted graph
classes and explicit row conjugacies. Does not prove halting equivalence.
"""
from collections import defaultdict
from hashlib import sha256
from pathlib import Path
import argparse
import json


def need(condition, message):
    if not condition:
        raise ValueError(message)


def parse(data, start, halt, count):
    rows = {}
    for line in data.decode("ascii").splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        q, bit, write, direction, target = line.split()
        q, bit, write, target = map(int, (q, bit, write, target))
        need((q, bit) not in rows, "duplicate row")
        need(bit in (0, 1) and write in (0, 1), "nonbinary row")
        need(direction in ("L", "R"), "nonunit move")
        rows[q, bit] = write, direction, target
    states = {q for q, _ in rows}
    need(len(states) == count and start in states, "state count or start")
    need(set(rows) == {(q, b) for q in states for b in (0, 1)}, "incomplete table")
    need({t for w, d, t in rows.values()} - states == {halt}, "halt labels")
    order, labels, canonical = [start], {start: 0}, []
    for q in order:
        for bit in (0, 1):
            write, direction, target = rows[q, bit]
            if target != halt and target not in labels:
                labels[target] = len(order)
                order.append(target)
            canonical.append((write, direction, -1 if target == halt else labels[target]))
    need(len(order) == count, "graph-unreachable working state")
    return rows, labels, canonical


def check(root, manifest, count):
    entries = manifest["tables"]
    groups = defaultdict(list)
    parsed = {}
    for entry in entries:
        data = (root / entry["local_file"]).read_bytes()
        need(sha256(data).hexdigest() == entry["sha256"], "table hash: " + entry["local_file"])
        rows, labels, canonical = parse(data, entry["start"], entry["halt"], count)
        key = sha256(json.dumps(canonical, separators=(",", ":")).encode()).hexdigest()
        need(key == entry["canonical_sha256"], "graph hash: " + entry["local_file"])
        groups[key].append(entry)
        parsed[entry["local_file"]] = (rows, labels)
    conjugacies = equations = 0
    for group in groups.values():
        representative = group[0]
        rr, rl = parsed[representative["local_file"]]
        inverse = {number: state for state, number in rl.items()}
        for entry in group[1:]:
            rows, labels = parsed[entry["local_file"]]
            mapping = {state: inverse[number] for state, number in labels.items()}
            mapping[entry["halt"]] = representative["halt"]
            need(mapping[entry["start"]] == representative["start"], "start conjugacy")
            for (state, bit), (write, direction, target) in rows.items():
                need(rr[mapping[state], bit] == (write, direction, mapping[target]), "row conjugacy")
                equations += 1
            conjugacies += 1
    return {"working_states": count, "presentations": len(entries), "rooted_classes": len(groups),
            "explicit_conjugacies": conjugacies, "row_equations": equations,
            "classes": [[e["name"] for e in group] for group in groups.values()]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    a = json.loads((args.root / "portable196_catalog.json").read_text())
    b = json.loads((args.root / "portable208_catalog.json").read_text())
    result = {"196": check(args.root, a, 196), "208": check(args.root, b, 208),
              "scope": "Exact rooted table structure only; candidate status is inherited, not certified here."}
    need(result["196"]["presentations"] == result["196"]["rooted_classes"] == 18, "196 census")
    need(result["208"]["presentations"] == 27 and result["208"]["rooted_classes"] == 20, "208 census")
    need(result["208"]["explicit_conjugacies"] == 7 and result["208"]["row_equations"] == 2912, "208 conjugacy census")
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    print(text)


if __name__ == "__main__":
    main()
