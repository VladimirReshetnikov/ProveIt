#!/usr/bin/env python3
"""Deterministically construct the published 237-state table from composed238.

Python 3.10+ standard library only. No proof search or numerical simulation is
performed here: the local proof and startup checks are separate programs.
"""

from pathlib import Path
import argparse
import hashlib
import json
import re
import sys


ROOT = Path(__file__).resolve().parent
INPUT_SHA256 = "069942be27db9736875ea042320e51ac3b1eac7116cbe01cdce520fa6056f78c"
OLD_SHA256 = "a3c4407f30e2e2139af87c6a91948c518134855841a28eb85b1d81bcfd026c9a"
CANONICAL_SHA256 = "7eda1da1fcda629cae86d22b01d3faf419552cf04ed4179f0c045ad0adf2c1a6"
NUMBERING_SHA256 = "d62a4e8444742714b34c3c23c582919c74b28a1c5869dff857d26ca51267c035"


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def parse(raw):
    rows, starts = {}, []
    for line in raw.decode("ascii").splitlines():
        if line.startswith("#! start "):
            starts.append(int(line[len("#! start "):]))
        elif not line or line.startswith("#"):
            continue
        else:
            match = re.fullmatch(r"(\d+) ([01]) ([01]) ([LR]) (\d+)", line)
            require(match is not None, ("Malformed row", line))
            q, b, w, d, t = match.groups()
            q, b, w, t = map(int, (q, b, w, t))
            require((q, b) not in rows, ("Duplicate row", q, b))
            rows[q, b] = (w, d, t)
    require(starts == [95], "The inherited start must be 95")
    working = {q for q, b in rows}
    require(len(working) == 238, "Expected 238 working states")
    require(set(rows) == {(q, b) for q in working for b in (0, 1)}, "Partial table")
    require({t for w, d, t in rows.values()} - working == {254}, "Wrong halt")
    return rows


def encode(rows, start):
    return (f"#! start {start}\n" + "".join(
        f"{q} {b} {w} {d} {t}\n"
        for (q, b), (w, d, t) in sorted(rows.items())
    )).encode("ascii")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input238", type=Path, default=ROOT / "zfc_composed238_old.tm")
    parser.add_argument("--output-dir", type=Path, default=ROOT / "rebuilt237")
    args = parser.parse_args()
    require(sys.version_info >= (3, 10), "Python 3.10 or newer is required")
    require(__debug__ and not sys.flags.optimize, "Run without -O or -OO")
    raw = args.input238.read_bytes()
    require(digest(raw) == INPUT_SHA256, "The composed238 input bytes changed")
    old = parse(raw)
    phi = lambda q: 98 if q == 235 else q
    new = {(q, b): (w, d, phi(t)) for (q, b), (w, d, t) in old.items() if q != 235}
    new[98, 0] = (0, "L", 240)
    new[240, 1] = (1, "L", 87)
    changed = sorted(key for key in new if new[key] != old[key])
    require(changed == [(98, 0), (139, 1), (156, 1), (240, 1)], "Unexpected edits")
    states = {q for q, b in new}
    require(len(states) == 237 and len(new) == 474, "Incorrect final count")
    require(set(new) == {(q, b) for q in states for b in (0, 1)}, "Partial final table")
    require({t for w, d, t in new.values()} - states == {254}, "Wrong final halt")
    old_bytes = encode(new, 95)
    require(digest(old_bytes) == OLD_SHA256, "Unexpected inherited-label table")
    order = [95] + sorted(states - {95})
    numbering = {q: i for i, q in enumerate(order)} | {254: 237}
    canonical = {(numbering[q], b): (w, d, numbering[t]) for (q, b), (w, d, t) in new.items()}
    require(set(canonical) == {(q, b) for q in range(237) for b in (0, 1)}, "Bad relabeling")
    canonical_bytes = encode(canonical, 0)
    require(digest(canonical_bytes) == CANONICAL_SHA256, "Unexpected canonical table")
    numbering_bytes = (json.dumps({"old_to_new": numbering, "new_to_old": order + [254]}, indent=2) + "\n").encode("utf-8")
    require(digest(numbering_bytes) == NUMBERING_SHA256, "Unexpected numbering bytes")
    reachable, pending = set(), [95]
    while pending:
        q = pending.pop()
        if q in reachable:
            continue
        reachable.add(q)
        if q != 254:
            pending.extend(new[q, b][2] for b in (0, 1))
    require(reachable == states | {254}, "Unexpected graph-unreachable state")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    files = {
        "zfc_composed237_old.tm": old_bytes,
        "zfc_composed237.tm": canonical_bytes,
        "renumbering.json": numbering_bytes,
    }
    for name, contents in files.items():
        (args.output_dir / name).write_bytes(contents)
    print(json.dumps({
        "status": "PASS_DETERMINISTIC_237_CONSTRUCTION",
        "working_states": 237, "rows": 474,
        "start": 0, "dispatcher": numbering[96], "halt": 237,
        "all_working_states_graph_reachable": True,
        "input238_sha256": INPUT_SHA256,
        "files": {name: digest(contents) for name, contents in files.items()},
    }, indent=2))


if __name__ == "__main__":
    main()
