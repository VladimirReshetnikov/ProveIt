#!/usr/bin/env python3
"""Rebuild and independently identify the complete 238-state machine.

Uses Python's standard library. Writes only into the supplied output directory.
Input identities, every changed row, relabeling and the entire initialized tape
are checked. These finite calculations do not decide consistency.
"""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
BASE_SHA = "d061770f487937f9da652919c9bc9bb79bc9bf137ca41dd7a08eb5ecda8e7719"
OLD_SHA = "069942be27db9736875ea042320e51ac3b1eac7116cbe01cdce520fa6056f78c"
CANON_SHA = "909f29c493e0ccc5d6a481fd7a20a9a82eb934ab2aa7df17b5ec3789255a8c08"
SITES_SHA = "7fd152d1f5371d2a561d4ad1870d241683b010ce7b7a27399b95363a4537cfb6"
BOOT = 409835
PHY = (6, 2, 0, 4, 3, 7, 8, 5, 1)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse(path, inherited_start=None):
    rows, start = {}, None
    for line in path.read_text(encoding="ascii").splitlines():
        if line.startswith("#! start "):
            require(start is None, "Duplicate start directive")
            start = int(line.split()[-1])
        elif line and not line.startswith("#"):
            q, b, w, d, n = line.split()
            q, b, w, n = map(int, (q, b, w, n))
            require((q, b) not in rows, "Duplicate row")
            require(b in (0, 1) and w in (0, 1) and d in ("L", "R"), "Nonbinary row")
            rows[q, b] = (w, 1 if d == "R" else -1, n)
    if start is None:
        require(inherited_start is not None, "Missing start convention")
        start = inherited_start
    states = {q for q, b in rows}
    require(start in states, "Missing start state")
    require(set(rows) == {(q, b) for q in states for b in (0, 1)}, "Partial table")
    return rows, start


def encode(rows, start):
    return ("#! start " + str(start) + "\n" + "".join(
        f"{q} {b} {w} {'R' if d == 1 else 'L'} {n}\n"
        for (q, b), (w, d, n) in sorted(rows.items()))).encode("ascii")


def sparse(rows, start, steps):
    q, h, ones, used = start, 0, set(), Counter()
    low = high = 0
    for tick in range(steps):
        read = int(h in ones)
        used[q, read] += 1
        write, move, target = rows[q, read]
        if write:
            ones.add(h)
        else:
            ones.discard(h)
        q, h = target, h + move
        low, high = min(low, h), max(high, h)
    return q, h, ones, used, (low, high)


def dense(rows, start, steps):
    origin = steps + 2
    position, q = origin, start
    tape = bytearray(2 * origin + 1)
    for _ in range(steps):
        write, move, target = rows[q, tape[position]]
        tape[position] = write
        position, q = position + move, target
    return q, position - origin, {i - origin for i, bit in enumerate(tape) if bit}


def verify(output):
    baseline = ROOT / "reference/boundary239_old.tm"
    require(sha(baseline) == BASE_SHA, "Wrong Boundary239 input bytes")
    old, start = parse(baseline, inherited_start=95)
    require(len(old) == 478 and start == 95, "Wrong input convention")
    changes = {
        (80, 0): ((0, 1, 25), (0, -1, 106)),
        (91, 1): ((0, -1, 50), (1, -1, 167)),
        (147, 0): ((0, 1, 169), (0, 1, 80)),
    }
    new = dict(old)
    for key, (before, after) in changes.items():
        require(new[key] == before, "Patch precondition failed")
        new[key] = after
    removed = {b: new.pop((169, b)) for b in (0, 1)}
    require(len(new) == 476, "Wrong final row count")
    require(169 not in {n for w, d, n in new.values()}, "Dangling reference")
    working = {q for q, b in new}
    require(len(working) == 238 and 254 not in working, "Wrong working state count")
    require({n for w, d, n in new.values()} - working == {254}, "Wrong halt outcome")
    raw = encode(new, 95)
    require(hashlib.sha256(raw).hexdigest() == OLD_SHA, "Unexpected inherited table")
    require(raw == (ROOT / "machines/zfc_combined238_old.tm").read_bytes(), "Published table differs")
    order = [95] + sorted(working - {95})
    phi = {q: i for i, q in enumerate(order)} | {254: 238}
    canonical = {(phi[q], b): (w, d, phi[n]) for (q, b), (w, d, n) in new.items()}
    canonical_raw = encode(canonical, 0)
    require(hashlib.sha256(canonical_raw).hexdigest() == CANON_SHA, "Unexpected canonical table")
    require(canonical_raw == (ROOT / "machines/zfc_combined238.tm").read_bytes(), "Canonical bytes differ")
    saved = json.loads((ROOT / "machines/renumbering.json").read_text())
    require({int(q): n for q, n in saved["old_to_new"].items()} == phi, "Renumbering mismatch")
    require(saved["new_to_old"] == order + [254], "Inverse mismatch")
    require((phi[95], phi[96], phi[254]) == (0, 84, 238), "Distinguished states mismatch")
    reached, stack = set(), [0]
    while stack:
        q = stack.pop()
        if q in reached:
            continue
        reached.add(q)
        if q != 238:
            stack.extend(canonical[q, b][2] for b in (0, 1))
    require(reached == set(range(239)), "A graph state is unreachable")

    sites_file = ROOT / "machines/sites_logical.json"
    require(sha(sites_file) == SITES_SHA, "Wrong source bytes")
    sites = json.loads(sites_file.read_text())
    require(sites == json.loads((ROOT / "reference/source/formalism/extra/boundary224_sites.json").read_text()), "Source certificate endpoint differs")
    require(json.loads((ROOT / "reference/source/formalism/extra/baseline_sites.json").read_text()) ==
            json.loads((ROOT / "reference/source/baseline/rotation240/sites_logical.json").read_text()),
            "Source certificate input does not match Lean source input")
    leaves = {p for p, op, arg in sites}
    prefixes = {p[:i] for p in leaves for i in range(len(p))}
    require(len(leaves) == len(sites) == 6455, "Duplicate or missing leaf")
    require(not (leaves & prefixes), "Not prefix-free")
    require(all(p + b in leaves | prefixes for p in prefixes for b in "01"), "Incomplete binary source tree")
    require(max(map(len, leaves)) == 48, "Unexpected source depth")
    require(sum(2 if op == "CD" else 1 for p, op, arg in sites) == 8386, "Guard census")
    require(all(0 <= arg < 9 for p, op, arg in sites if op in ("CI", "CD")), "Source uses spare as register")

    a, b, c = sparse(new, 95, BOOT), dense(new, 95, BOOT), dense(canonical, 0, BOOT)
    require(a[:3] == b, "Sparse/dense startup disagree")
    require(c == (phi[b[0]], b[1], b[2]), "Canonical startup differs")
    prior = json.loads((ROOT / "reference/source/candidate239/blank_prefix.json").read_text())
    require(b == (96, -5, set(prior["all_one_positions"])), "Complete calibrated tape differs")
    q, h, ones = b
    require(min(ones) == h - 1, "Wrong marker or nonzero left exterior")
    header = min(x for x in ones if x >= h)
    values, position = [], header + 1
    while position <= max(ones):
        require(position not in ones and position + 1 in ones, "Bad unary block")
        begin = position + 1
        position = begin
        while position in ones:
            position += 1
        values.append(position - begin - 1)
    logical = [values[j] for j in PHY]
    require((q, h, header, len(ones)) == (96, -5, 176, 351), "Frame census mismatch")
    require(logical == [3, 0, 0, 0, 3, 0, 0, 0, 0], "Wrong logical seed")
    require(values[9:] == [1] * 167, "Wrong spare suffix")
    output.mkdir(parents=True, exist_ok=True)
    frame = {
        "status": "EXACT_238_SPARSE_DENSE_CANONICAL_BOOT_PASS", "steps": BOOT,
        "initial_state": 0, "initial_head": 0, "initial_tape": "all zero",
        "final_state": 84, "final_state_old": q, "final_head": h,
        "pc": "", "marker": h - 1, "header": header,
        "header_distance": header - h, "extra_gap": header - h - 64,
        "physical_registers": values[:9], "logical_registers": logical,
        "spare_values": values[9:], "one_count": len(ones),
        "all_one_positions": sorted(ones), "all_other_cells_zero": True,
        "head_range": a[4], "working_states": 238,
    }
    result = {
        "status": "EXACT_238_CONSTRUCTION_AND_INITIALIZATION_PASS",
        "working_states": 238, "transition_rows": 476, "symbols": [0, 1],
        "moves": ["L", "R"], "start": 0, "dispatcher": 84, "halt": 238,
        "all_working_states_graph_reachable": True,
        "canonical_sha256": CANON_SHA, "inherited_sha256": OLD_SHA,
        "base_boundary239_sha256": BASE_SHA, "source_sha256": SITES_SHA,
        "changed_retained_rows": [
            {"state": q, "read": bit, "old": list(before), "new": list(after)}
            for (q, bit), (before, after) in sorted(changes.items())],
        "deleted_state": 169, "deleted_rows": removed, "unchanged_retained_rows": 473,
        "source_leaves": 6455, "source_guards": 8386, "maximum_source_depth": 48,
        "boot_steps": BOOT, "boot_one_cells": len(ones),
        "checker_sha256": sha(Path(__file__)),
        "scope": "Finite construction, graph census, exact source identity and whole blank startup. Unbounded runtime and logical calibration are separate proof layers.",
    }
    (output / "construction.json").write_text(json.dumps(result, indent=2) + "\n")
    (output / "blank_prefix.json").write_text(json.dumps(frame, indent=2) + "\n")
    (output / "zfc_combined238.tm").write_bytes(canonical_raw)
    (output / "zfc_combined238_old.tm").write_bytes(raw)
    return result


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output-dir", type=Path, required=True)
    args = ap.parse_args()
    if not __debug__ or sys.flags.optimize:
        raise SystemExit("Run with assertions enabled; do not use -O or -OO.")
    print(json.dumps(verify(args.output_dir), indent=2))
