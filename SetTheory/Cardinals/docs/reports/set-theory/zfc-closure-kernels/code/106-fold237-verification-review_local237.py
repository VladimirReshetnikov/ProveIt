#!/usr/bin/env python3
"""Independent symbolic review of the 235-to-98 fold, without startup replay.

Invariant closure is checked by entailment between finite partial assignments,
not by enumerating Boolean windows. All unchecked tape cells remain arbitrary.
"""
import argparse
import hashlib
import json
from pathlib import Path


def read_table(path):
    rows = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        q, b, w, d, z = line.split()
        if d not in ("L", "R") or b not in ("0", "1") or w not in ("0", "1"):
            raise ValueError("invalid row")
        key = int(q), int(b)
        if key in rows:
            raise ValueError("duplicate row")
        rows[key] = int(w), -1 if d == "L" else 1, int(z)
    states = {q for q, _ in rows}
    if set(rows) != {(q, b) for q in states for b in (0, 1)}:
        raise ValueError("incomplete table")
    if {z for _, _, z in rows.values()} - states != {254}:
        raise ValueError("incorrect halt")
    return rows


def check(old_path, new_path):
    old, new = read_table(old_path), read_table(new_path)
    if len(old) != 476 or len(new) != 474:
        raise ValueError("incorrect sizes")
    phi = lambda q: 98 if q == 235 else q
    invariant = {98: {-1: 0}, 139: {-1: 1}, 156: {-1: 1},
                 235: {-2: 1, -1: 1}, 240: {-1: 0}}
    if invariant.get(95, {}):
        raise ValueError("non-vacuous start constraint")
    incoming = {q: [] for q in invariant}
    for (q, b), (w, d, z) in old.items():
        known = {**invariant.get(q, {}), 0: b}
        known[0] = w
        for k, value in invariant.get(z, {}).items():
            if known.get(d + k) != value:
                raise ValueError(("invariant not entailed", q, b, z, d + k, value))
        if z in incoming:
            incoming[z].append([q, b, w, d])

    specs = [(98, 0, {-1: 0, 0: 0}, 3),
             (235, 0, {-2: 1, -1: 1, 0: 0}, 5),
             (240, 1, {-1: 0, 0: 1}, 3)]
    special = {(q, b) for q, b, _, _ in specs}
    ordinary = 0
    for (q, b), (w, d, z) in old.items():
        if (q, b) not in special:
            if new.get((phi(q), b)) != (w, d, phi(z)):
                raise ValueError(("ordinary row mismatch", q, b))
            ordinary += 1
    proofs = []
    for q, b, bits, duration in specs:
        if any(invariant.get(q, {}).get(k) != value
               for k, value in bits.items() if k != 0) or bits[0] != b:
            raise ValueError("block guard is not entailed by the invariant and read bit")
        state, head, final_bits, trace = phi(q), 0, dict(bits), []
        for _ in range(duration):
            if head not in final_bits:
                raise ValueError("read outside resolved guard")
            read = final_bits[head]
            w, d, z = new[state, read]
            if w != read:
                raise ValueError("unexpected tape write")
            trace.append([state, head, read, z])
            state, head = z, head + d
        ow, od, oz = old[q, b]
        if ow != b or (state, head) != (phi(oz), od):
            raise ValueError("endpoint disagreement")
        if any(x[0] == 254 for x in trace):
            raise ValueError("interior halt")
        proofs.append({"old_row": [q, b], "duration": duration,
                       "unchanged_entire_tape": True, "trace": trace,
                       "endpoint": [state, head]})
    return {"status": "PASS_INDEPENDENT_237_LOCAL_REVIEW",
            "old_sha256": hashlib.sha256(old_path.read_bytes()).hexdigest(),
            "new_sha256": hashlib.sha256(new_path.read_bytes()).hexdigest(),
            "invariant_row_implications": len(old),
            "invariant_method": "entailment of partial cell assignments",
            "incoming": incoming,
            "ordinary_rows": ordinary, "blocks": proofs,
            "arbitrary_initial_tape_and_head": True, "start": 95,
            "halt": 254, "minimum_block_length": 1,
            "maximum_block_length": 5,
            "scope": "Local all-tape simulation; no new source or bootstrap replay"}


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("old", type=Path)
    p.add_argument("new", type=Path)
    p.add_argument("--output", type=Path)
    a = p.parse_args()
    result = json.dumps(check(a.old, a.new), indent=2) + "\n"
    if a.output:
        a.output.write_text(result)
    print(result, end="")
