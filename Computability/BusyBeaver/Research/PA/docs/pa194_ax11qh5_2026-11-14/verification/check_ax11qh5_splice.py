#!/usr/bin/env python3
"""Check the exact QH5 -> AX11QH5 resolved instruction-graph splice."""
import argparse
import hashlib
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def targets(row):
    if row[0] in ("inc", "dec"):
        return row[2:]
    if row[0] == "jump":
        return row[1:]
    return []


def project(row, relocation):
    if row[0] in ("inc", "dec"):
        return row[:2] + [relocation(t) for t in row[2:]]
    if row[0] == "jump":
        return ["jump", relocation(row[1])]
    return row


def verify(old_dir, new_dir):
    old_bytes = (old_dir / "instructions.json").read_bytes()
    new_bytes = (new_dir / "instructions.json").read_bytes()
    old, new = json.loads(old_bytes), json.loads(new_bytes)
    require(len(old) == 3714 and len(new) == 3732, "exact source sizes")
    entry, old_exit, new_exit = 3613, 3614, 3632
    require(old[entry] == ["jump", 3702], "old AX return")
    relocate = lambda i: i if i <= entry else i + 18
    for i, row in enumerate(old):
        if i != entry:
            require(new[relocate(i)] == project(row, relocate), ("outside source row", i))
    # The added block is precisely the old, already used stack-push source
    # occurrence at ordinals 50..68, with its normal exit 69 relocated to 3632.
    for i in range(19):
        require(new[entry + i] == project(old[50 + i], lambda t: t - 50 + entry),
                ("exact inserted push", i))
    for i, row in enumerate(new):
        if not entry <= i < new_exit:
            require(not any(entry < t < new_exit for t in targets(row)),
                    ("external entry into splice interior", i))
    require(new[new_exit] == project(old[old_exit], relocate), "full MP-reader continuation")
    old_nodes = json.loads((old_dir / "nodes.json").read_text())
    new_nodes = json.loads((new_dir / "nodes.json").read_text())
    require(old_nodes == new_nodes, "fixed source nodes unchanged")
    require(new_nodes["node163"] == ["node6", "node54"], "no-push MP source")
    require(new_nodes["node170"] == [["node36", ["node167", "node145"]], "node57"], "cache-only Shift source")
    return {
        "status": "PASS", "old_sites": 3714, "new_sites": 3732,
        "unchanged_sites_with_relocated_targets": 3713,
        "old_AX_return_site": entry, "old_AX_return_target": 3702,
        "new_push_interval_half_open": [entry, new_exit],
        "reference_push_interval_half_open": [50, 69],
        "new_exit_is_old_full_MP_reader": True,
        "outside_entry_to_splice_interior": False,
        "fixed_source_nodes_equal": True,
        "old_instructions_sha256": hashlib.sha256(old_bytes).hexdigest(),
        "new_instructions_sha256": hashlib.sha256(new_bytes).hexdigest(),
        "scope": "Complete resolved instruction-graph equality outside one exact 19-site push replacing one jump; not by itself a physical simulation."
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--old", type=Path, required=True)
    parser.add_argument("--new", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = verify(args.old, args.new)
    output = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(output)
    print(output)
