#!/usr/bin/env python3
"""Exact native/canonical blank startup, delta trace, and source AX-prefix match."""
from __future__ import annotations

import gzip
import io
import json
import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import source_language as sl
from common import (canonical_table, check_census, cli, compact, encode_table,
                    parse_table, pinned, require, sha, write_json)

BINARY_STEPS = 70506
SOURCE_STEPS = 177
SOURCE_ORDINAL = 58
ADDRESS = "00110010010110010"
LOGICAL = [1, 0, 0, 0, 0, 0, 0, 18, 0]
AX_SEED = [1, 0, 2, 0, 0, 0, 0, 0, 0]


def gzip_bytes(raw):
    # GzipFile, unlike gzip.compress(mtime=0) on some Python releases, always
    # writes the portable OS=255 header. There is no filename or timestamp.
    buffer = io.BytesIO()
    with gzip.GzipFile(filename="", mode="wb", fileobj=buffer, mtime=0) as out:
        out.write(raw)
    return buffer.getvalue()


def expected_frame():
    physical = [None] * 9
    for i, j in enumerate((6, 2, 0, 4, 3, 7, 8, 5, 1)):
        physical[j] = LOGICAL[i]
    head = -2
    ones = {-3, 62} | {head + i for i, b in enumerate(ADDRESS) if b == "1"}
    pos = 63
    for value in physical + [0] * 63:
        ones.update(range(pos + 1, pos + value + 2))
        pos += value + 2
    require(len(ones) == 100, "Whole-frame one-cell count")
    return ones


def replay(table, start, steps, record=False):
    q, head, ones = start, 0, set()
    trace = bytearray()
    for tick in range(steps):
        read = int(head in ones)
        written, move, target = table[q, read]
        if record:
            # One complete delta per TM transition: tick, old state/head,
            # read symbol, written symbol, movement, new state.
            trace.extend(compact([tick, q, head, read, written, move, target]))
        if written:
            ones.add(head)
        else:
            ones.discard(head)
        q, head = target, head + move
    return (q, head, ones), bytes(trace)


def replay_delta(table, raw):
    q, head, ones = 0, 0, set()
    count = 0
    for line in raw.splitlines():
        tick, oldq, oldhead, read, written, move, target = json.loads(line)
        require((tick, oldq, oldhead, read) ==
                (count, q, head, int(head in ones)), "Delta precondition mismatch")
        require(table[q, read] == (written, move, target), "Delta/table mismatch")
        if written:
            ones.add(head)
        else:
            ones.discard(head)
        q, head = target, head + move
        count += 1
    require(count == BINARY_STEPS, "Delta transition count")
    return q, head, ones


def source_prefix(graph, rows):
    ordinal, regs = 25, AX_SEED.copy()
    trace = []
    for step in range(SOURCE_STEPS):
        before = regs.copy()
        old_ordinal = ordinal
        effect, targets = graph[ordinal]
        if effect[0] == "increment":
            regs[effect[1]] += 1
            ordinal = targets[0]
        elif effect[0] == "decrement":
            r = effect[1]
            positive = regs[r] > 0
            regs[r] -= int(positive)
            ordinal = targets[int(positive)]
        else:
            require(effect == ["identity"], "Unexpected halt in AX prefix")
            ordinal = targets[0]
        trace.append({
            "step": step, "ordinal": old_ordinal, "site": rows[old_ordinal],
            "before": before, "next_ordinal": ordinal, "after": regs.copy(),
        })
    require(ordinal == SOURCE_ORDINAL and regs == LOGICAL, "AX-prefix endpoint")
    return trace


def run(root, work):
    """Replay both labelings, save/replay all 70,506 deltas, and match177 source steps."""
    root, work = Path(root), Path(work)
    work.mkdir(parents=True, exist_ok=True)
    source_raw = pinned(root, "source/dr215.sites.json")
    table_raw = pinned(root, "machine/dr215.native.tm")
    rows = json.loads(source_raw)
    graph, _ = sl.graph_arithmetic(rows)
    require(graph == sl.graph_intervals(rows), "Independent source CFGs disagree")
    require(rows[SOURCE_ORDINAL][0] == ADDRESS, "Expected source address")
    table, start = parse_table(table_raw)
    check_census(table, start)
    require(start == 0 and table[198, 0] == (0, -1, 40), "Start/refill convention")

    endpoint, delta = replay(table, start, BINARY_STEPS, record=True)
    expected = (84, -2, expected_frame())
    require(endpoint == expected, "Complete native blank frame differs")
    trace_file = work / "blank-delta.jsonl.gz"
    trace_file.write_bytes(gzip_bytes(delta))
    restored = gzip.decompress(trace_file.read_bytes())
    require(restored == delta, "Compressed delta roundtrip")
    require(replay_delta(table, restored) == expected, "Saved delta replay differs")

    canonical, canonical_start, mapping = canonical_table(table, start)
    canonical_raw = (root / "machine/dr215.tm").read_bytes()
    require(parse_table(canonical_raw) == (canonical, canonical_start), "Canonical table mismatch")
    canonical_endpoint, _ = replay(canonical, canonical_start, BINARY_STEPS)
    require(canonical_endpoint == (mapping[84], -2, expected[2]), "Canonical blank replay differs")

    trace = source_prefix(graph, rows)
    source_trace = compact(trace)
    (work / "AX-prefix.json").write_bytes(source_trace)
    require(json.loads((work / "AX-prefix.json").read_bytes()) == trace, "Saved source trace differs")
    result = {
        "status": "EXACT_BLANK_FRAME_DELTA_AND_AX_PREFIX_PASS",
        "source_sha256": sha(source_raw), "native_table_sha256": sha(table_raw),
        "canonical_table_sha256": sha(encode_table(canonical, canonical_start)),
        "states": 215, "rows": 430, "start": 0,
        "native_halt": 254, "canonical_halt": 215,
        "binary_steps": BINARY_STEPS, "native_dispatcher": 84,
        "canonical_dispatcher": mapping[84], "head": -2, "header": 62, "gap": 0,
        "source_address": ADDRESS, "source_ordinal": SOURCE_ORDINAL,
        "logical_registers": LOGICAL, "spares": [0] * 63,
        "one_cells": sorted(expected[2]),
        "delta_trace": {
            "file": "blank-delta.jsonl.gz", "format": "JSON lines [tick,state,head,read,write,move,target]",
            "transitions": BINARY_STEPS, "uncompressed_sha256": sha(delta),
            "saved_trace_replayed": True,
        },
        "AX_entry": 25, "AX_seed": AX_SEED,
        "AX_primitive_steps": SOURCE_STEPS,
        "AX_trace": {"file": "AX-prefix.json", "sha256": sha(source_trace)},
        "proof_bridge": "AX completion leaves ten theorem heads above opaque tail2; ordinary schedule has exact conservative d(1)=2, hence margin8",
        "scope": "Finite exact startup and source-prefix certificate; all-natural runtime and command proofs are separate.",
    }
    write_json(work / "bootstrap.json", result)
    return result


if __name__ == "__main__":
    cli(run)
