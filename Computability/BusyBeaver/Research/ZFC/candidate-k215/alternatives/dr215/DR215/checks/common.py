"""Small standard-library helpers shared by the DR215 finite checks."""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True

PINS = {'inputs/st215.sites.json': '212cf0ffde43c1cc22c183dd8bf0b3a699396f96c9942ee92a7cc372cd273ca9', 'inputs/st215.native.tm': 'd5237504325eee96b0040d4d9574731a1caf4bcda3d6a49e94827d9532a664e1', 'source/dr215.sites.json': '74d21758da7e932de766bee079adf11a7917c03a1957b1111abc6463d70eb332', 'machine/dr215.native.tm': 'fac930e9bc89fed41b631de2f12ef4e48e1c8625ef31ef093d4f14b340f113ad'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def compact(value):
    return (json.dumps(value, separators=(",", ":")) + "\n").encode("ascii")


def pinned(root, relative):
    raw = (Path(root) / relative).read_bytes()
    require(sha(raw) == PINS[relative], "Wrong SHA-256: " + relative)
    return raw


def write_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="ascii")


def parse_table(raw):
    rows, start = {}, None
    for line in raw.decode("ascii").splitlines():
        if line.startswith("#! start "):
            require(start is None, "Duplicate start declaration")
            start = int(line.split()[-1])
        if not line or line.startswith("#"):
            continue
        fields = line.split()
        require(len(fields) == 5, "Malformed table row")
        q, b, w, direction, z = fields
        q, b, w, z = map(int, (q, b, w, z))
        require((q, b) not in rows, "Duplicate table row")
        require(b in (0, 1) and w in (0, 1), "Nonbinary symbol")
        require(direction in ("L", "R"), "Invalid direction")
        rows[q, b] = w, (-1 if direction == "L" else 1), z
    require(start is not None, "Missing start declaration")
    return rows, start


def encode_table(rows, start=0):
    lines = ["#! start " + str(start)]
    for (q, b), (w, d, z) in sorted(rows.items()):
        lines.append(f"{q} {b} {w} {'R' if d == 1 else 'L'} {z}")
    return ("\n".join(lines) + "\n").encode("ascii")


def check_census(rows, start, halt=254):
    states = {q for q, _ in rows}
    require(len(rows) == 430 and len(states) == 215, "State/row census")
    require(start in states, "Missing start state")
    require(all((q, b) in rows for q in states for b in (0, 1)), "Missing row")
    require({z for _, _, z in rows.values()} - states == {halt}, "Halt census")
    return sorted(states)


def canonical_table(rows, start=0):
    states = check_census(rows, start)
    mapping = {q: i for i, q in enumerate(states)}
    mapping[254] = 215
    canonical = {
        (mapping[q], b): (w, d, mapping[z])
        for (q, b), (w, d, z) in rows.items()
    }
    return canonical, mapping[start], mapping


def cli(run):
    parser = argparse.ArgumentParser(description=run.__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--work", type=Path)
    args = parser.parse_args()
    work = args.work or Path(tempfile.mkdtemp(prefix="dr215-check-"))
    result = run(args.root.resolve(), work.resolve())
    print(json.dumps(result, indent=2))

