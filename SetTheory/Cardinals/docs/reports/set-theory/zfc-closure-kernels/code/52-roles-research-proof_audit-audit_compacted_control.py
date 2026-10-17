#!/usr/bin/env python3
"""Independent finite control audit for the allocated DAG no-op compaction.

Reimplements path arithmetic without importing either transformation module.
Checks the initial control, every retained leaf and guard, all halt labels,
physical data operands, and absence of nonzero unconsumed path suffixes.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def expand(data: dict) -> dict[str, tuple]:
    nodes = {int(k): tuple(tuple(x) for x in v) for k, v in data["nodes"].items()}
    leaves: dict[str, tuple] = {}

    def visit(edge: tuple, path: str, active: frozenset[int]) -> None:
        if edge[0] != "N":
            assert edge[0] in {"I", "D", "B", "C", "H"}
            leaves[path] = edge
            return
        node = edge[1]
        assert node not in active, ("cyclic_decoder_DAG", node)
        assert len(nodes[node]) == 2
        for bit, child in enumerate(nodes[node]):
            visit(child, path + str(bit), active | {node})

    visit(tuple(data["root"]), "", frozenset())
    return leaves


def increment(bits: str) -> str:
    value = list(bits)
    carry = True
    for i in range(len(value) - 1, -1, -1):
        if not carry:
            break
        if value[i] == "0":
            value[i], carry = "1", False
        else:
            value[i] = "0"
    return "".join(value)


def strip(bits: str, matching_bit: str, count: int) -> str:
    remaining = list(bits)
    while count > 0 and remaining:
        if remaining.pop() == matching_bit:
            count -= 1
    return "".join(remaining)


def successor(path: str, operation: tuple, guard: bool | None) -> str | None:
    kind = operation[0]
    if kind == "H":
        return None
    operand = operation[1]
    if kind == "I" or kind == "D" and guard is False:
        return increment(path)
    if kind == "D":
        assert guard is True
        return increment(strip(path, "0", 1))
    if kind == "B":
        return increment(strip(path, "0", operand))
    assert kind == "C"
    return strip(path, "1", operand)


def decode(pc: str | None, leaves: dict[str, tuple]) -> str | None:
    if pc is None:
        return None
    path = ""
    maximum = max(map(len, leaves))
    while path not in leaves:
        assert len(path) <= maximum, ("decoder_did_not_terminate", pc)
        path += pc[len(path)] if len(path) < len(pc) else "0"
    assert "1" not in pc[len(path) :], ("dirty_unconsumed_control", pc, path)
    return path


def closure(pc: str | None, leaves: dict[str, tuple]) -> str | None:
    visited = set()
    leaf = decode(pc, leaves)
    while leaf is not None and leaves[leaf] == ("B", 0):
        assert leaf not in visited, ("epsilon_cycle", leaf)
        visited.add(leaf)
        leaf = decode(increment(leaf), leaves)
    return leaf


def main() -> None:
    if not __debug__:
        raise SystemExit("run with assertions enabled")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("allocated", type=Path)
    parser.add_argument("compacted", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    old_raw, new_raw = args.allocated.read_bytes(), args.compacted.read_bytes()
    old_data, new_data = json.loads(old_raw), json.loads(new_raw)
    old, new = expand(old_data), expand(new_data)
    mapping = new_data["original_to_new"]
    old_nops = {p for p, op in old.items() if op == ("B", 0)}
    assert set(mapping) <= set(old)
    assert set(old) - set(mapping) <= old_nops
    assert set(mapping.values()) == set(new)
    assert len(mapping.values()) == len(set(mapping.values()))

    old_start, new_start = closure("", old), closure("", new)
    assert old_start is not None and new_start == mapping[old_start]
    checks = halt_sites = 0
    for path, op in old.items():
        if path in old_nops:
            continue
        new_path = mapping[path]
        new_op = new[new_path]
        if op[0] in {"I", "D", "H"}:
            assert op == new_op, ("physical_operand_or_halt_changed", path, op, new_op)
        else:
            assert op[0] in {"B", "C"} and new_op[0] in {"B", "C"}
        if op[0] == "H":
            halt_sites += 1
        for guard in (True, False) if op[0] == "D" else (None,):
            old_target = closure(successor(path, op, guard), old)
            new_target = closure(successor(new_path, new_op, guard), new)
            expected = None if old_target is None else mapping[old_target]
            assert new_target == expected, ("control_mismatch", path, guard, expected, new_target)
            checks += 1
    assert halt_sites == sum(op[0] == "H" for op in new.values()) == 1

    result = {
        "status": "PASS exact independent control-compaction audit",
        "allocated_sha256": hashlib.sha256(old_raw).hexdigest(),
        "compacted_sha256": hashlib.sha256(new_raw).hexdigest(),
        "old_instruction_leaves": len(old),
        "new_instruction_leaves": len(new),
        "old_noop_leaves": len(old_nops),
        "removed_noop_leaves": len(set(old) - set(mapping)),
        "guarded_successor_checks": checks,
        "initial_control_matches": True,
        "unique_halt_preserved": True,
        "data_operands_unchanged": True,
        "all_decoded_control_suffixes_clean": True,
        "scope": "Exact finite source control and operands; binary backend simulation is separate.",
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
