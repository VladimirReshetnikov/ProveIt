#!/usr/bin/env python3
"""Check unchanged source semantics and the complete blank initializer.

The initializer is run until the first dispatcher configuration satisfying the
full canonical frame with header distance at least 56. It is not stopped merely
on the first visit to the dispatcher. Every old/new transition and entire finite
one-cell set are compared. Unlisted cells are the infinite zero exterior.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import source_language as source

ROOT = Path(__file__).resolve().parents[1]
DISPATCH = 84
HALT = 254
HEADER_BASE = 56
PHYSICAL_ORDER = (6, 2, 0, 4, 3, 7, 8, 5, 1)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def encoded(data):
    return (json.dumps(data, separators=(",", ":")) + "\n").encode("ascii")


def table(path):
    result = {}
    starts = []
    for line in path.read_text().splitlines():
        if line.startswith("#! start "):
            starts.append(int(line[9:]))
            continue
        if not line or line.startswith("#"):
            continue
        q, b, w, direction, target = line.split()
        q, b, w, target = map(int, (q, b, w, target))
        require((q, b) not in result, "Duplicate transition")
        require(b in (0, 1) and w in (0, 1), "Nonbinary transition")
        require(direction in ("L", "R"), "Invalid direction")
        result[q, b] = w, -1 if direction == "L" else 1, target
    require(starts == [0], "The initial state is not exactly 0")
    states = {q for q, b in result}
    require(set(result) == {(q, b) for q in states for b in (0, 1)},
            "Incomplete transition table")
    require({target for w, d, target in result.values()} - states == {HALT},
            "The table has an undefined target or wrong halt")
    return result


def decode_frame(state, head, ones, rows, leaves, maximum_depth):
    """Recognize the complete canonical tape, with arbitrary register values.

    Its word is 0^infinity,1,pc,0^gap,1,B(v0)...B(v8),B(spare0),...,
    0^infinity, where B(v)=0 1^(v+1), at least one spare is present, pc is
    a source leaf, and the header is at distance at least HEADER_BASE.
    """
    if state != DISPATCH or not ones or min(ones) != head - 1:
        return None
    pc = ""
    for index in range(maximum_depth):
        pc += str(int(head + index in ones))
        if pc in leaves:
            break
    if pc not in leaves:
        return None
    later = [position for position in ones if position >= head + len(pc)]
    if not later:
        return None
    header = min(later)
    if header - head < HEADER_BASE:
        return None
    values = []
    position = header + 1
    rightmost = max(ones)
    while position <= rightmost:
        if position in ones:
            return None
        position += 1
        length = 0
        while position in ones:
            length += 1
            position += 1
        if length == 0:
            return None
        values.append(length - 1)
    if len(values) < 10:
        return None
    ordinal = leaves[pc]
    require(rows[ordinal][0] == pc, "Leaf/ordinal lookup mismatch")
    logical = [values[index] for index in PHYSICAL_ORDER]
    return {
        "state": state, "head": head, "header": header,
        "header_distance": header - head,
        "source_ordinal": ordinal, "source_address": pc,
        "logical_registers": logical, "physical_registers": values[:9],
        "spares": values[9:], "one_cells": sorted(ones),
        "one_cell_count": len(ones), "zero_exterior": True,
    }


def startup(old, new, rows, maximum_steps=1_000_000):
    leaves = {path: i for i, (path, _, _) in enumerate(rows)}
    maximum_depth = max(map(len, leaves))
    old_q = new_q = old_head = new_head = 0
    old_ones, new_ones = set(), set()
    digest_old, digest_new = hashlib.sha256(), hashlib.sha256()
    visited = set()
    dispatcher_visits = 0
    changed_rows = {key for key in set(old) | set(new) if old.get(key) != new.get(key)}
    for count in range(maximum_steps + 1):
        require((old_q, old_head, old_ones) == (new_q, new_head, new_ones),
                ("Blank configurations differ", count))
        if old_q == DISPATCH:
            dispatcher_visits += 1
        frame = decode_frame(old_q, old_head, old_ones, rows, leaves, maximum_depth)
        other = decode_frame(new_q, new_head, new_ones, rows, leaves, maximum_depth)
        require(frame == other, "Canonical frame recognition differs")
        if frame is not None:
            require(count == 48140, "Unexpected first canonical frame time")
            require(frame["state"] == 84 and frame["head"] == -2,
                    "Unexpected dispatcher/head")
            require(frame["source_ordinal"] == 136 and
                    frame["source_address"] == "001100110101010",
                    "Unexpected canonical source entry")
            require(frame["logical_registers"] == [1, 0, 13, 0, 0, 1, 0, 0, 1],
                    "Unexpected initial logical registers")
            require(frame["spares"] == [1] * 43, "Unexpected spare-list frame")
            require(frame["one_cell_count"] == 120 and frame["header"] == 54,
                    "Unexpected whole-tape frame")
            require(digest_old.digest() == digest_new.digest(), "Trace digests differ")
            require(not visited & changed_rows, "Initializer visits a modified row")
            frame.update({
                "steps": count,
                "first_frame_with_header_distance_at_least_56": True,
                "dispatcher_visits_including_endpoint": dispatcher_visits,
                "entire_trace_equal": True, "entire_tape_equal": True,
                "trace_sha256": digest_old.hexdigest(),
                "changed_row_visits": 0,
                "distinct_rows_visited": len(visited),
            })
            return frame
        require(count < maximum_steps, "No canonical frame within the safety limit")
        require(old_q != HALT and new_q != HALT, "Initializer halts")
        old_bit = int(old_head in old_ones)
        new_bit = int(new_head in new_ones)
        old_action = old[old_q, old_bit]
        new_action = new[new_q, new_bit]
        require(old_bit == new_bit and old_action == new_action,
                ("Literal blank traces differ", count))
        visited.add((old_q, old_bit))
        for digest, q, head, bit_value, action in (
                (digest_old, old_q, old_head, old_bit, old_action),
                (digest_new, new_q, new_head, new_bit, new_action)):
            write, direction, target = action
            digest.update(f"{count} {q} {head} {bit_value} {write} {direction} {target}\n".encode())
        old_write, old_direction, old_q = old_action
        new_write, new_direction, new_q = new_action
        if old_write:
            old_ones.add(old_head)
        else:
            old_ones.discard(old_head)
        if new_write:
            new_ones.add(new_head)
        else:
            new_ones.discard(new_head)
        old_head += old_direction
        new_head += new_direction
    raise ValueError("Unreachable initializer-loop exit")


def source_bridge(rows, graph):
    """Finite inherited source suffix; this is not its unbounded safety proof."""
    ordinal = 106
    registers = [1, 0, 4, 0, 0, 1, 0, 0, 1]
    trace = []
    for index in range(141):
        before = [ordinal, registers.copy()]
        op, arg = rows[ordinal][1:]
        targets = graph[ordinal][1]
        if op == "CI":
            registers[arg] += 1
            ordinal = targets[0]
        elif op == "CD":
            positive = registers[arg] > 0
            registers[arg] -= int(positive)
            ordinal = targets[int(positive)]
        elif op in ("CB", "CC"):
            ordinal = targets[0]
        else:
            raise ValueError("Finite source prefix unexpectedly halts")
        trace.append([*before, ordinal, registers.copy()])
    require((ordinal, registers) == (136, [1, 0, 13, 0, 0, 1, 0, 0, 1]),
            "Finite source bridge does not match the literal entry")
    return {"seed_ordinal": 106, "seed_registers": [1, 0, 4, 0, 0, 1, 0, 0, 1],
            "source_steps": 141, "final_ordinal": ordinal, "final_registers": registers,
            "trace_sha256": sha(encoded(trace)),
            "scope": "Finite source calculation; protected-tail soundness is inherited."}


def check(output):
    old_source_path = ROOT / "inputs/u209.sites.json"
    new_source_path = ROOT / "machine/sites.json"
    old_raw, new_raw = old_source_path.read_bytes(), new_source_path.read_bytes()
    require(old_raw == new_raw, "Source bytes changed")
    old_rows, new_rows = json.loads(old_raw), json.loads(new_raw)
    old_tree, new_tree = source.tree(old_rows), source.tree(new_rows)
    old_graph, old_resolved = source.graph_arithmetic(old_rows)
    new_graph, new_resolved = source.graph_arithmetic(new_rows)
    require(old_graph == source.graph_intervals(old_rows) == new_graph ==
            source.graph_intervals(new_rows), "Source control-flow resolver disagreement")
    metrics = source.metrics(new_tree)
    require(source.metrics(old_tree) == metrics, "Source metrics changed")
    require(metrics == {"dag_nodes": 197, "leaf_occurrences": 3909,
                        "maximum_depth": 42, "maximum_zero_run": 6},
            "Unexpected source metrics")
    require(old_rows == new_rows, "Ordered source primitives changed")
    edges = sum(len(targets) for effect, targets in new_graph)
    require(edges == 5083, "Unexpected control-edge count")
    cases = len(new_rows) + sum(op == "CD" for path, op, arg in new_rows)
    require(cases == 5084, "Unexpected guarded primitive count")
    old_path = ROOT / "inputs/u209.native.tm"
    new_path = ROOT / "machine/u208.native.tm"
    old_table, new_table = table(old_path), table(new_path)
    require(len(old_table) == 418 and len(new_table) == 416, "Unexpected table sizes")
    frame = startup(old_table, new_table, new_rows)
    result = {
        "status": "UNCHANGED_SOURCE_AND_EXACT_STARTUP_PASS",
        "source_bytes_unchanged": True, "changed_source_addresses": 0,
        "source_primitives": len(new_rows), "guarded_primitive_cases": cases,
        "control_edges": edges, "source_metrics": metrics,
        "arithmetic_and_interval_cfg_agree": True,
        "arithmetic_successor_checks_including_initial": new_resolved,
        "source_cfg_sha256": sha(encoded(new_graph)),
        "source_word_sha256": sha(encoded([[op, arg] for path, op, arg in new_rows])),
        "startup": frame, "finite_source_bridge": source_bridge(new_rows, new_graph),
        "input_sha256": {
            "inputs/u209.native.tm": sha(old_path.read_bytes()),
            "inputs/u209.sites.json": sha(old_raw),
            "machine/u208.native.tm": sha(new_path.read_bytes()),
            "machine/sites.json": sha(new_raw),
        },
        "scope": "Exact unchanged source/CFG and finite literal blank initialization. "
                 "No grouped-prefix claim, no unbounded nonhalting inference; universal "
                 "runtime and inherited source/theory calibration are separate.",
    }
    output = Path(output)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2) + "\n")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "build/source_startup.json")
    args = parser.parse_args()
    result = check(args.output)
    print(json.dumps({"status": result["status"], "source_primitives": result["source_primitives"],
                      "control_edges": result["control_edges"], "source_metrics": result["source_metrics"],
                      "startup_steps": result["startup"]["steps"],
                      "first_canonical_frame": result["startup"]["first_frame_with_header_distance_at_least_56"],
                      "startup_one_cells": result["startup"]["one_cell_count"],
                      "entire_trace_equal": result["startup"]["entire_trace_equal"]}, indent=2))


if __name__ == "__main__":
    main()
