#!/usr/bin/env python3
"""Replay a source-level counterexample to deleting the shared gm rule.

This is an exact finite witness against a universal source contract.  It does
not assert that the chosen entry frame is reached from the blank tape, and it
does not decide the blank-tape halting behavior of the 244-state mutation.
Only Python's standard library is required; do not run with -O.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path


def increment(path):
    j = path.rfind("0")
    return path[:j] + "1" + "0" * (len(path) - j - 1) if j >= 0 else "0" * len(path)


def strip(path, bit, count):
    while path and count:
        count -= path[-1] == bit
        path = path[:-1]
    return path


def decode(sites):
    """Build a prefix decoder and independently require a complete binary tree."""
    root = {}
    for i, (path, op, reg) in enumerate(sites):
        assert path and set(path) <= {"0", "1"}
        node = root
        for c in path:
            assert "leaf" not in node
            node = node.setdefault(c, {})
        assert not node
        node["leaf"] = (i, path, op, reg)
    def close(node):
        if "leaf" in node:
            assert set(node) == {"leaf"}
            _, _, op, reg = node["leaf"]
            return ("L", op, reg)
        assert set(node) == {"0", "1"}
        return ("N", close(node["0"]), close(node["1"]))
    tree = close(root)
    def lookup(path):
        node = root
        pos = 0
        while "leaf" not in node:
            bit = path[pos] if pos < len(path) else "0"
            node = node[bit]
            pos += 1
        assert set(path[pos:]) <= {"0"}
        return node["leaf"]
    return tree, lookup


def run(sites, start, stop, registers, limit=10000):
    _, lookup = decode(sites)
    pc, values, trace = start, list(registers), []
    for tick in range(limit + 1):
        index, path, op, reg = lookup(pc)
        trace.append(dict(step=tick, index=index, pc=path, op=op, register=reg,
                          logical_registers=list(values)))
        if path == stop:
            return dict(steps=tick, final=list(values), trace=trace)
        if op == "CI":
            values[reg] += 1
            pc = increment(path)
        elif op == "CD":
            if values[reg]:
                values[reg] -= 1
                pc = increment(path)
            else:
                pc = increment(strip(path, "0", 1))
        elif op == "CB":
            pc = increment(strip(path, "0", reg))
        elif op == "CC":
            pc = strip(path, "1", reg)
        else:
            raise AssertionError(("unexpected halt before tail exit", index, path))
    raise AssertionError("counterexample exceeded its explicit replay limit")


def audit(original_path, mutant_path):
    before = json.loads(original_path.read_text())
    after = json.loads(mutant_path.read_text())
    original, _ = decode(before)
    mutant, _ = decode(after)
    assert len(before) == 6460 and len(after) == 6448
    # Do not infer unique source occurrence from a unique incoming TM edge.
    gm = ("N", ("N", ("L", "CD", 6),
                ("N", ("L", "CI", 5), ("L", "CC", 2))), ("L", "CI", 5))
    occurrences = []
    def edit(node, path=""):
        if node == gm:
            occurrences.append(path)
            return ("L", "CI", 5)
        if node[0] == "L":
            return node
        return ("N", edit(node[1], path + "0"), edit(node[2], path + "1"))
    assert edit(original) == mutant
    assert occurrences == ["11101001001011000011", "1110100100101110011",
                           "1110100101100011", "111110011"]
    start, stop = before[6275][0], before[6311][0]
    assert start == "1110100100101011111110" and stop == "111010010011"
    seed = [3, 7, 0, 2, 2, 0, 0, 0, 0]
    old_result, new_result = (run(sites, start, stop, seed) for sites in (before, after))
    assert old_result["steps"] == 58 and old_result["final"] == [3, 0, 0, 0, 0, 0, 0, 0, 0]
    assert new_result["steps"] == 41 and new_result["final"] == [3, 7, 0, 0, 0, 0, 0, 0, 0]
    return dict(status="EXACT_SOURCE_COUNTEREXAMPLE_VERIFIED",
                scope="The universal AX freshness-tail contract fails; blank reachability is not asserted.",
                original_sha256=hashlib.sha256(original_path.read_bytes()).hexdigest(),
                mutant_sha256=hashlib.sha256(mutant_path.read_bytes()).hexdigest(),
                original_leaves=len(before), mutant_leaves=len(after),
                removed_gm_occurrences=occurrences, start_pc=start, stop_pc=stop,
                register_order=["N", "T", "W", "A", "D", "H", "X", "Y", "L"],
                initial=seed, original=old_result, mutant=new_result)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--original", type=Path, default=Path(__file__).with_name("original_sites.json"))
    p.add_argument("--mutant", type=Path, default=Path(__file__).with_name("mutant_sites.json"))
    p.add_argument("--output", type=Path)
    a = p.parse_args()
    result = audit(a.original, a.mutant)
    if a.output:
        a.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k not in ("original", "mutant")}, indent=2))
    print("Original:", result["original"]["steps"], "steps ->", result["original"]["final"])
    print("Mutant:", result["mutant"]["steps"], "steps ->", result["mutant"]["final"])


if __name__ == "__main__":
    assert __debug__, "Assertions are required; do not use -O."
    main()
