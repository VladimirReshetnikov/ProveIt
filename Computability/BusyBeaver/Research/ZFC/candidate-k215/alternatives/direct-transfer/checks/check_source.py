#!/usr/bin/env python3
"""Independent dual-CFG source audit and direct-transfer corroboration."""
from __future__ import annotations

import json
import sys
from math import isqrt
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import source_language as sl
from common import PINS, cli, pinned, require, sha, write_json


def unpair(n):
    s = (isqrt(8 * n + 1) - 1) // 2
    y = n - s * (s + 1) // 2
    return s - y, y


def transfer(graph, top, stack, offset, cache):
    regs = [19, top, stack, 0, offset, cache, 0, 0, 23]
    pc, steps = 4697, 0
    while pc != 0:
        require(4697 <= pc < 4732, "S escaped its body")
        effect, targets = graph[pc]
        op = effect[0]
        if op == "halt":
            return None, steps
        if op == "increment":
            regs[effect[1]] += 1
            pc = targets[0]
        elif op == "decrement":
            r = effect[1]
            positive = regs[r] > 0
            regs[r] -= int(positive)
            pc = targets[int(positive)]
        else:
            require(op == "identity", "Unknown effect")
            pc = targets[0]
        steps += 1
        require(steps < 100000, "Finite S corroboration exceeded limit")
    return regs, steps


def run(root, work):
    """Audit both exact CFG resolvers and the direct single-guard S contract."""
    root, work = Path(root), Path(work)
    work.mkdir(parents=True, exist_ok=True)
    raw = pinned(root, "source/st215.sites.json")
    rows = json.loads(raw)
    tree = sl.tree(rows)
    graph, count = sl.graph_arithmetic(rows)
    require(graph == sl.graph_intervals(rows), "Independent source CFGs disagree")
    require(sl.boundary(tree) == (0, 0, True), "Source is not closed")
    metrics = sl.metrics(tree)
    require(metrics == {"dag_nodes": 201, "leaf_occurrences": 4732,
                        "maximum_depth": 44, "maximum_zero_run": 6}, "Source metrics")
    require(count == 6151, "Guarded primitive census")
    require(rows[4696] == ["00111", "CC", 3], "Return context")
    require(graph[4696] == [["identity"], [0]], "AX/MP return does not reach root")
    require(rows[4697] == ["010", "CD", 1], "Clear-top context")
    require(graph[4697] == [["decrement", 1], [4699, 4698]], "Clear-top graph")
    require(rows[4717] == ["11101", "CH", None], "Single-guard halt")

    comparisons = {}
    for name in ("simple", "context-root"):
        key = "inputs/" + name + ".sites.json"
        old = json.loads(pinned(root, key))
        oldgraph, _ = sl.graph_arithmetic(old)
        require(oldgraph == sl.graph_intervals(old), "Reference CFG disagreement")
        require(graph == oldgraph, "Complete ordinal CFG changed")
        changes = [i for i, (a, b) in enumerate(zip(rows, old)) if a[1:] != b[1:]]
        require(changes == ([4696] if name == "simple" else []), "Instruction-word changes")
        comparisons[name] = {
            "source_sha256": PINS[key], "same_complete_ordinal_CFG": True,
            "changed_addresses": sum(a[0] != b[0] for a, b in zip(rows, old)),
            "changed_opcode_operands": changes,
        }

    trials = max_steps = 0
    for top in range(6):
        for stack in range(100):
            for offset in (0, 3, 12):
                for cache in range(8):
                    actual, steps = transfer(graph, top, stack, offset, cache)
                    max_steps = max(max_steps, steps)
                    if cache == 1:
                        require(actual is None, "S failed to halt on cache1")
                    else:
                        x, v = unpair(stack)
                        require(actual == [19, cache, v, 0, offset, x, 0, 0, 23],
                                "S violated its contract")
                    trials += 1

    result = {
        "status": "SOURCE_CONTROL_AND_DIRECT_TRANSFER_PASS",
        "source_sha256": sha(raw), "metrics": metrics,
        "source_boundary": list(sl.boundary(tree)),
        "arithmetic_and_interval_CFG_equal": True,
        "source_successor_checks": count,
        "comparisons": comparisons,
        "ordinary_command_return": {"ordinal": 4696, "address": "00111", "target": 0},
        "direct_transfer_entry": {"ordinal": 4697, "address": "010"},
        "finite_transfer_corroboration": {
            "trials": trials, "maximum_primitive_steps": max_steps,
            "contract": "halts iff incoming cache=1; otherwise (h,unpair(w).right,d,unpair(w).left)",
            "scope": "Finite corroboration only; the all-natural command proof and physical simulation are separate.",
        },
        "credit_theorem": "ordinary S=0, MP=1, AX>=2 schedule; exact conservative d(1)=2",
    }
    write_json(work / "source.json", result)
    return result


if __name__ == "__main__":
    cli(run)

