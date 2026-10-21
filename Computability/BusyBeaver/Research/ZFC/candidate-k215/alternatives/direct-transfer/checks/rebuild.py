#!/usr/bin/env python3
"""Deterministic ST215 reconstruction from the pinned composite-transfer parent.

No optimizer, allocation search, network, or third-party package is used.
The four source stages are literal tree transformations. The table change
is the exact fourteen-row delta to the same pinned parent native table.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import source_language as sl
from common import (PINS, canonical_table, check_census, cli, compact,
                    encode_table, parse_table, pinned, require, sha, write_json)

PATCH = (
    (84, 0, 0, 1, 214),
    (84, 1, 1, 1, 188),
    (134, 1, 1, 1, 310),
    (188, 0, 0, 1, 20),
    (188, 1, 1, 1, 38),
    (198, 0, 0, -1, 40),
    (214, 0, 0, 1, 312),
    (214, 1, 1, 1, 122),
    (310, 0, 0, 1, 201),
    (310, 1, 1, -1, 73),
    (311, 0, 0, 1, 95),
    (311, 1, 1, 1, 111),
    (312, 0, 0, 1, 311),
    (312, 1, 1, 1, 134),
)


def dual_graph(rows):
    first, count = sl.graph_arithmetic(rows)
    require(first == sl.graph_intervals(rows), "Source CFG resolvers disagree")
    return first, count


def reconstruct_source(parent):
    transfer = sl.subtree(parent, "111")
    drop, nip = transfer[0]
    require(transfer[1] == nip, "Parent transfer is not DROP;NIP;NIP")
    require(len(sl.sites(drop)) == len(sl.sites(nip)) == 26, "Parent command sizes")
    load = drop[1]
    require(len(sl.sites(load)) == 7, "Cache-copy loop size")
    clear = (("CD", 1), ("CC", 1))
    direct = ((clear, load), nip)
    require(len(sl.sites(direct)) == 35, "Direct transfer size")
    simple = sl.replace(parent, "111", direct)

    selector = sl.subtree(simple, "110")
    require(sl.subtree(selector, "11") == ("CB", 1), "Selector return")
    selector = sl.replace(selector, "11", ("CB", 2))
    moved_clear = sl.replace(simple, "11", ((selector, clear), (load, nip)))
    scheduler, (read, dispatch) = moved_clear
    context = ((scheduler, read), dispatch)
    require(sl.subtree(context, "10011") == ("CB", 2), "Context return")
    context = sl.replace(context, "10011", ("CC", 3))

    # The new step fixes both physical contexts simultaneously while retaining
    # the literal instruction word and every ordinal register-program edge.
    a, ((b, c), d) = context
    final = (((a, b), c), d)
    stages = {
        "simple": simple,
        "moved_clear": moved_clear,
        "context_root": context,
        "st215": final,
    }
    reference, _ = dual_graph(sl.sites(simple))
    for name, tree in stages.items():
        require(dual_graph(sl.sites(tree))[0] == reference, "CFG changed: " + name)
    require([row[1:] for row in sl.sites(context)] ==
            [row[1:] for row in sl.sites(final)], "Final rotation changed instruction word")
    return stages


def run(root, work):
    """Reconstruct and compare the exact source, native table, and canonical table."""
    root, work = Path(root), Path(work)
    work.mkdir(parents=True, exist_ok=True)
    parent_source = pinned(root, "inputs/transfer-parent.sites.json")
    stages = reconstruct_source(sl.tree(json.loads(parent_source)))
    simple = compact(sl.sites(stages["simple"]))
    context = compact(sl.sites(stages["context_root"]))
    source = compact(sl.sites(stages["st215"]))
    require(simple == pinned(root, "inputs/simple.sites.json"), "Simple stage differs")
    require(context == pinned(root, "inputs/context-root.sites.json"), "Context stage differs")
    require(source == pinned(root, "source/st215.sites.json"), "Final source differs")

    parent_rows, parent_start = parse_table(pinned(root, "inputs/transfer-parent.native.tm"))
    require(parent_start == 0, "Parent start state")
    table = dict(parent_rows)
    changes = []
    for q, b, w, d, z in PATCH:
        require(table[q, b] != (w, d, z), "Redundant patch row")
        changes.append({"row": [q, b], "before": list(table[q, b]), "after": [w, d, z]})
        table[q, b] = w, d, z
    raw = encode_table(table, 0)
    require(raw == pinned(root, "machine/st215.native.tm"), "Final native table differs")
    check_census(table, 0)
    require(len(changes) == 14, "Fourteen-row delta")

    canonical, start, mapping = canonical_table(table, 0)
    canonical_raw = encode_table(canonical, start)
    packaged_canonical = (root / "machine/st215.tm").read_bytes()
    require(parse_table(packaged_canonical) == (canonical, start), "Canonical table differs")
    require(start == 0, "Canonical start")

    (work / "rebuilt-st215.sites.json").write_bytes(source)
    (work / "rebuilt-st215.native.tm").write_bytes(raw)
    (work / "rebuilt-st215.tm").write_bytes(canonical_raw)
    write_json(work / "native-to-canonical.json", mapping)
    result = {
        "status": "DETERMINISTIC_RECONSTRUCTION_PASS",
        "input_sha256": {name: PINS[name] for name in (
            "inputs/transfer-parent.sites.json", "inputs/transfer-parent.native.tm",
            "inputs/simple.sites.json", "inputs/context-root.sites.json")},
        "source_sha256": sha(source), "native_table_sha256": sha(raw),
        "canonical_table_sha256": sha(canonical_raw),
        "states": 215, "rows": 430, "start": 0,
        "native_halt": 254, "canonical_halt": 215,
        "stages": {name: sl.metrics(tree) for name, tree in stages.items()},
        "all_stage_CFGs_equal": True,
        "table_changes_from_parent": changes,
    }
    write_json(work / "rebuild.json", result)
    return result


if __name__ == "__main__":
    cli(run)

