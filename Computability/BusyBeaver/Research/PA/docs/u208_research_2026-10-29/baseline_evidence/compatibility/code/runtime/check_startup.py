#!/usr/bin/env python3
"""Independent literal-table/startup audit; imports no project runtime code."""
import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path

def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def load_table(path):
    result = {}
    for line in path.read_text().splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        fields = line.split()
        require(len(fields) == 5, "Bad transition arity")
        q, read, write, target = map(int, (fields[0], fields[1], fields[2], fields[4]))
        require(q >= 0 and target >= 0, "Negative state")
        require(read in (0, 1) and write in (0, 1), "Nonbinary transition")
        require(fields[3] in ("L", "R"), "Illegal movement")
        require((q, read) not in result, "Duplicate transition")
        result[q, read] = (write, -1 if fields[3] == "L" else 1, target)
    return result


def decode_root(state, head, ones):
    """Decode an exact root frame with no residual code bits."""
    if state != 84 or not ones or min(ones) != head - 1:
        return None
    right = sorted(x for x in ones if x >= head)
    if not right or right[0] < head + 64:
        return None
    marker = right[0]
    position = marker + 1
    physical = []
    last = max(ones)
    while position <= last:
        if position in ones or position + 1 not in ones:
            return None
        position += 1
        start = position
        while position in ones:
            position += 1
        physical.append(position - start - 1)
    if len(physical) < 10:
        return None
    permutation = (6, 2, 0, 4, 3, 7, 8, 5, 1)
    logical = [physical[i] for i in permutation]
    if any(logical[i] != 0 for i in (1, 2, 5)):
        return None
    return {"gap": marker - head - 64, "registers": logical,
            "spares": physical[9:]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--table", required=True, type=Path)
    parser.add_argument("--sites", required=True, type=Path)
    parser.add_argument("--startup", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args()
    transitions = load_table(args.table)
    working = {q for q, _ in transitions}
    require(0 in working, "Missing start")
    require(len(transitions) == 2 * len(working), "Not two rows per state")
    require(all((q, b) in transitions for q in working for b in (0, 1)),
            "Missing binary row")
    outside = {target for _, _, target in transitions.values()} - working
    require(outside == {254}, "Unexpected external target")
    block_rows = {
        (64, 0): (0, 1, 74), (74, 1): (1, 1, 64), (64, 1): (1, 1, 64),
        (0, 0): (1, 1, 94), (94, 1): (0, 1, 0), (0, 1): (1, 1, 0),
        (40, 1): (1, -1, 54), (54, 1): (1, -1, 54), (54, 0): (0, -1, 40),
        (97, 1): (1, -1, 97), (97, 0): (1, -1, 113), (113, 1): (0, -1, 97),
    }
    require(all(transitions.get(key) == row for key, row in block_rows.items()),
            "A literal row in the four induction block schemas changed")
    reachable = {0}
    todo = [0]
    while todo:
        q = todo.pop()
        for read in (0, 1):
            target = transitions[q, read][2]
            if target in working and target not in reachable:
                reachable.add(target)
                todo.append(target)

    sites = json.loads(args.sites.read_text())
    leaves = set()
    prefixes = set()
    for row in sites:
        require(isinstance(row, list) and len(row) == 3, "Invalid site row")
        pc, op, arg = row
        require(isinstance(pc, str) and 0 < len(pc) <= 64
                and set(pc) <= {"0", "1"}, "Invalid site path")
        require(pc not in leaves, "Duplicate leaf")
        leaves.add(pc)
        prefixes.update(pc[:i] for i in range(len(pc)))
        require(op in {"CI", "CD", "CB", "CC", "CH"}, "Invalid site operation")
        if op == "CH":
            require(arg is None, "Halt argument")
        elif op in {"CI", "CD"}:
            require(type(arg) is int and 0 <= arg < 9, "Invalid register")
        else:
            require(type(arg) is int and arg >= 1, "Invalid loop index")
    require(not leaves & prefixes, "Prefix collision")
    require(all(p + b in leaves | prefixes for p in prefixes for b in ("0", "1")),
            "Incomplete source tree")
    require(len(prefixes) == len(leaves) - 1, "Not a full binary tree")

    expected = json.loads(args.startup.read_text())
    require(expected.get("status") == "CALIBRATED_DIRTY_ROOT_SEED",
            "Supplied receipt does not assert a calibrated root")
    require(type(expected.get("steps")) is int and expected["steps"] >= 0,
            "Invalid startup step count")
    q = head = 0
    ones = set()
    first_root = None
    trace = expected["trace"]
    for tick in range(expected["steps"] + 1):
        decoded = decode_root(q, head, ones)
        if decoded is not None and first_root is None:
            first_root = tick
        if tick == expected["steps"]:
            break
        read = int(head in ones)
        require((q, read) in transitions, "Premature halt")
        write, direction, target = transitions[q, read]
        require(trace[tick] == [q, head, read, write, direction, target],
                "Published startup trace disagrees with literal execution")
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        q, head = target, head + direction
    require(first_root == expected["steps"], "Not the first calibrated root")
    require(q == expected["state"] and head == expected["head"], "Wrong final head/state")
    require(sorted(ones) == expected["one_cells"], "Wrong final complete tape")
    require(decoded is not None, "Final frame is not a calibrated root")
    require(all(decoded[k] == expected[k] for k in ("gap", "registers", "spares")),
            "Wrong decoded startup register frame")
    require(len(trace) == expected["steps"], "Wrong trace length")
    report = {
        "status": "INDEPENDENT_LITERAL_STARTUP_PASS",
        "table_sha256": hashlib.sha256(args.table.read_bytes()).hexdigest(),
        "sites_sha256": hashlib.sha256(args.sites.read_bytes()).hexdigest(),
        "startup_receipt_sha256": hashlib.sha256(args.startup.read_bytes()).hexdigest(),
        "reviewer_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "working_states": len(working), "transition_rows": len(transitions),
        "graph_reachable_working_states": len(reachable),
        "halt_label": 254, "start_label": 0,
        "site_count": len(sites), "full_binary_prefix_tree": True,
        "maximum_depth": max(map(len, leaves)),
        "operation_counts": dict(Counter(row[1] for row in sites)),
        "expected_symbolic_cases": sum(2 if row[1] == "CD" else 1 for row in sites),
        "startup_steps": expected["steps"], "first_calibrated_root": first_root,
        "startup_state": q, "startup_head": head,
        "startup_gap": decoded["gap"], "startup_registers": decoded["registers"],
        "spare_count": len(decoded["spares"]),
        "spare_values": dict(Counter(decoded["spares"])),
        "every_startup_trace_row_replayed": True,
        "complete_finite_support_compared": True,
        "four_induction_block_schema_rows_match": True,
        "scope": "Independent finite literal replay and table/site census; does not rerun or replace arbitrary-register symbolic verification."
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
