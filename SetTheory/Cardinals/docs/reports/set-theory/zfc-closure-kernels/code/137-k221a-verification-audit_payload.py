#!/usr/bin/env python3
"""Third-party structural and startup audit; imports no release checker."""
from collections import deque
from hashlib import sha256
from io import BytesIO
from pathlib import Path
from zipfile import ZipFile
import argparse
import json


def require(ok, message):
    if not ok:
        raise ValueError(message)


def parse(raw, halt):
    rows, starts = {}, []
    for line in raw.decode("ascii").splitlines():
        if line.startswith("#! start "):
            starts.append(int(line.removeprefix("#! start ")))
        elif line and not line.startswith("#"):
            q, b, w, direction, z = line.split()
            q, b, w, z = map(int, (q, b, w, z))
            require((q, b) not in rows, "Duplicate row")
            require(b in (0, 1) and w in (0, 1) and direction in ("L", "R"), "Bad row")
            rows[q, b] = w, -1 if direction == "L" else 1, z
    states = {q for q, b in rows}
    require(starts == [0], "Wrong start declaration")
    require(len(states) == 221 and len(rows) == 442, "Wrong cardinality")
    require(set(rows) == {(q, b) for q in states for b in (0, 1)}, "Not total")
    require({z for w, d, z in rows.values()} - states == {halt}, "Wrong terminal set")
    require(halt not in states, "Halt has rows")
    order, visited = [0], {0}
    for q in order:
        for b in (0, 1):
            z = rows[q, b][2]
            if z in states and z not in visited:
                visited.add(z)
                order.append(z)
    require(visited == states, "Working state graph is not accessible")
    return rows, order


def replay_dense(rows, expected):
    # Independently represented, dynamically extended dense tape, not a set of ones.
    tape, origin, head, state = [0], 0, 0, 0
    target_state = expected["state"]
    target_ones = expected["one_cells"]
    for count in range(1, 2_000_001):
        require((state, tape[head - origin]) in rows, "Premature halt")
        w, d, state = rows[state, tape[head - origin]]
        tape[head - origin] = w
        head += d
        if head < origin:
            tape[:0] = [0] * 1024
            origin -= 1024
        elif head - origin >= len(tape):
            tape.extend([0] * 1024)
        if state == target_state and head == expected["head"]:
            ones = [i + origin for i, b in enumerate(tape) if b]
            if ones == target_ones:
                return {"steps": count, "state": state, "head": head,
                        "one_count": len(ones), "one_cells": ones, "all_other_cells": 0}
    raise ValueError("Initialization endpoint not reached")


def derive_constants(rows, radius=8):
    # Forward abstract interpretation, followed by a distinct obligation check.
    states = {q for q, b in rows}
    known = {q: None for q in states | {254}}
    known[0] = {}
    pending = deque([0])
    while pending:
        q = pending.popleft()
        if q == 254:
            continue
        for b in (0, 1):
            if known[q].get(0, b) != b:
                continue
            w, d, z = rows[q, b]
            after = {k-d: v for k, v in known[q].items()
                     if -radius <= k-d <= radius and k != 0}
            after[-d] = w
            old = known[z]
            new = after if old is None else {k: v for k, v in old.items() if after.get(k) == v}
            if new != old:
                known[z] = new
                pending.append(z)
    require(all(x is not None for x in known.values()), "Not all states covered")
    require(known[0] == {}, "Initial tape constrained")
    for (q, b), (w, d, z) in rows.items():
        if known[q].get(0, b) != b:
            continue
        for k, value in known[z].items():
            pre = k + d
            require((w if pre == 0 else known[q].get(pre)) == value,
                    "Invariant not inductive")
    return known


def block(rows, state, patch, length):
    head, tape = 0, dict(patch)
    for _ in range(length):
        require(state != 254 and head in tape, "Block halted or read unknown exterior")
        w, d, state = rows[state, tape[head]]
        tape[head] = w
        head += d
    require(state != 254, "Unexpected halting endpoint")
    return state, head, tape


def archive_chain(raw, label):
    result = [{"archive": label, "sha256": sha256(raw).hexdigest()}]
    with ZipFile(BytesIO(raw)) as z:
        nested = [n for n in z.namelist() if n.endswith(".zip")]
        for n in nested:
            result += archive_chain(z.read(n), label + "::" + n)
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    root = args.root
    archive = (root / "vendor/K221_Construction_2026-10-20.zip").read_bytes()
    require(sha256(archive).hexdigest() == "a06c99b775193d9642a2734b7dd5fe7b72736fbdf9d9d8be438321d5e5d57ba4",
            "Wrong baseline archive")
    base = "K221_Construction_2026-10-20/"
    with ZipFile(BytesIO(archive)) as z:
        old_raw = z.read(base + "machine/k221.native.tm")
        old, _ = parse(old_raw, 254)
        baseline_receipt = json.loads(z.read(base + "machine/canonicalization.json"))
        require(z.read(base + "machine/sites221.json") == (root / "machine/sites221.json").read_bytes(),
                "Source differs from baseline")
    invariant = derive_constants(old)
    require(invariant[103].get(-1) == 1, "Critical left-neighbor invariant missing")
    records = []
    for name in ("row103", "row157", "both"):
        folder = root / "machine" / name
        native_bytes = (folder / "k221.native.tm").read_bytes()
        canonical_bytes = (folder / "k221.tm").read_bytes()
        native, order = parse(native_bytes, 254)
        canonical, canonical_order = parse(canonical_bytes, 221)
        require(canonical_order == list(range(221)), "Canonical labels not BFS order")
        mapping = {q: i for i, q in enumerate(order)}
        mapping[254] = 221
        require(canonical == {(mapping[q], b): (w, d, mapping[z])
                              for (q, b), (w, d, z) in native.items()}, "Bijection mismatch")
        receipt = json.loads((folder / "canonicalization.json").read_text())
        require(mapping == {int(k): v for k, v in receipt["native_to_canonical"].items()},
                "Published forward map mismatch")
        require({v: k for k, v in mapping.items()} ==
                {int(k): v for k, v in receipt["canonical_to_native"].items()},
                "Published inverse map mismatch")
        require(receipt["native_sha256"] == sha256(native_bytes).hexdigest(), "Native hash mismatch")
        require(receipt["canonical_sha256"] == sha256(canonical_bytes).hexdigest(), "Canonical hash mismatch")
        desired = {(103, 1), (157, 1)} if name == "both" else {(int(name[3:]), 1)}
        require({key for key in old if old[key] != native[key]} == desired, "Unexpected edits")
        diagrams = []
        for q, patch, old_steps, new_steps in [
            (103, {-1: 1, 0: 1}, 2, 2),
            (157, {-1: 0, 0: 1}, 2, 2),
            (157, {-1: 1, 0: 1}, 1, 3),
        ]:
            if (q, 1) not in desired:
                continue
            require(block(old, q, patch, old_steps) == block(native, q, patch, new_steps),
                    "Whole-tape positive diagram failed")
            diagrams.append([q, patch[-1], old_steps, new_steps])
        for field in ("head", "one_cells", "logical_registers", "physical_registers", "spares", "extra_gap"):
            require(receipt["startup"][field] == baseline_receipt["startup"][field],
                    "Complete startup differs from baseline: " + field)
        expectation = {"state": 84, "head": baseline_receipt["startup"]["head"],
                       "one_cells": baseline_receipt["startup"]["one_cells"]}
        startup_native = replay_dense(native, expectation)
        startup_canonical = replay_dense(canonical, {**expectation, "state": mapping[84]})
        require(startup_native["steps"] == startup_canonical["steps"] == receipt["startup"]["steps"],
                "Native/canonical startup times differ")
        records.append({"variant": name, "working_states": len(order), "rows": len(native),
                        "canonical_halt": 221, "native_halt": 254, "bijection_verified": True,
                        "native_sha256": sha256(native_bytes).hexdigest(),
                        "canonical_sha256": sha256(canonical_bytes).hexdigest(),
                        "positive_diagrams": diagrams,
                        "startup": {k: v for k, v in startup_native.items() if k != "one_cells"},
                        "canonical_startup_steps": startup_canonical["steps"]})
    require(len({r["canonical_sha256"] for r in records}) == 3, "Canonical variants identical")
    require(all(r["canonical_sha256"] != baseline_receipt["canonical_sha256"] for r in records),
            "Variant is only a renaming of baseline")
    result = {"status": "INDEPENDENT_ALTERNATIVES_PAYLOAD_AUDIT_PASS",
              "checker_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
              "constant_facts": sum(len(x) for x in invariant.values()),
              "state103_facts": invariant[103], "variants": records,
              "inherited_archive_chain": archive_chain(archive, "K221_Construction_2026-10-20.zip"),
              "proof_scope": "All initial binary tapes from state 0 and any integer head; inductive baseline invariant, whole-tape positive macro joins. Finite startup confirms the exact complete baseline endpoint only, not nonhalting.",
              "logical_boundary": "The inherited ordinary Con(ZFC) calibration is transported; no new proof-assistant theorem, PA-internal endpoint, unconditional nonhalting, or minimality assertion."}
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
