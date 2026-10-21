#!/usr/bin/env python3
"""Independent finite certificate for the CM215 whole-tape equivalence.

Only the two literal native tables are read.  No inherited verifier,
runtime record, blank trace, or source-program theorem is imported.
The finite computation checks the hypotheses of the window-lifting and
positive-stuttering lemmas proved in proof_audit.tex.  It is not a kernel
check, and it does not itself prove K215's ZFC consistency calibration.
"""

import argparse
import hashlib
import itertools
import json
from pathlib import Path

PARENT_SHA = "9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2"
CANDIDATE_SHA = "e5907f08e0752eada0e25bbf33680341e80e5fe94b52b409aea1ed039edda252"
DENSE_SHA = "1f4f084f7293e2b042d5746039f793ff72ed429083b504970c939a5515e666cf"
REVISION = "b6c7087477e51c017003bd729e712c8969733223"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_table(path, expected_sha, halt=254):
    data = path.read_bytes()
    require(hashlib.sha256(data).hexdigest() == expected_sha, "Wrong table bytes: " + str(path))
    start, rows = None, {}
    for line in data.decode().splitlines():
        if line.startswith("#! start "):
            require(start is None, "Duplicate start")
            start = int(line[9:])
        if not line or line.startswith("#"):
            continue
        q, b, w, d, z = line.split()
        require(b in ("0", "1") and w in ("0", "1") and d in ("L", "R"), "Invalid action")
        key = int(q), int(b)
        require(key not in rows, "Duplicate row")
        rows[key] = int(w), 1 if d == "R" else -1, int(z)
    states = {q for q, b in rows}
    require(start == 0 and len(states) == 215 and len(rows) == 430, "Wrong machine convention")
    require(set(rows) == set(itertools.product(states, (0, 1))), "Incomplete working table")
    require({z for w, d, z in rows.values()} - states == {halt}, "Wrong halt")
    return rows, states


def invariant(q, left, current, right):
    return ((q != 52 or left == 1)
            and (q != 176 or current == 1 or left == 0)
            and (q != 156 or right == 1))


def phi(q):
    return 52 if q == 176 else q


def block(rows, q, cells, length):
    tape, head = cells.copy(), 0
    for i in range(length):
        require(head in tape, "Read outside certified local window")
        require((q, tape[head]) in rows, "Unexpected halt inside a block")
        w, direction, q = rows[q, tape[head]]
        tape[head] = w
        head += direction
    return q, head, tape


def check(parent, candidate, dense, canonicalization):
    old, states = read_table(parent, PARENT_SHA)
    new, new_states = read_table(candidate, CANDIDATE_SHA)
    require(states == new_states, "Working-state domains differ")
    require(phi(0) == 0 and phi(254) == 254, "Boundary state map")
    require(all(phi(q) in states for q in states), "Working state mapped to halt")
    changed = sorted(key for key in old if old[key] != new[key])
    require(changed == [(52, 0), (156, 1), (165, 0), (176, 0), (176, 1), (193, 0)],
            "Unexpected changed rows")

    checked = one = three = 0
    # A radius-2 old window determines every radius-1 new window after one
    # L/R move.  Enumerating all 32 patterns therefore covers every tape.
    # The new blocks below read/write only positions -1 and 0; comparing
    # the entire finite window also proves equality of the whole tape,
    # because no cell outside it is modified by either machine.
    for q in sorted(states):
        for bits in itertools.product((0, 1), repeat=5):
            cells = dict(zip(range(-2, 3), bits))
            if not invariant(q, cells[-1], cells[0], cells[1]):
                continue
            checked += 1
            w, direction, target = old[q, cells[0]]
            old_tape = cells.copy()
            old_tape[0] = w
            require(invariant(target, *(old_tape[direction + k] for k in (-1, 0, 1))),
                    f"Invariant failure at {q}, {bits}")
            length = 3 if q in (52, 176) and cells[0] == 0 else 1
            actual = block(new, phi(q), cells, length)
            require(actual == (phi(target), direction, old_tape),
                    f"Block failure at {q}, {bits}")
            if length == 1:
                one += 1
            else:
                three += 1

    initial = all(invariant(0, *bits) for bits in itertools.product((0, 1), repeat=3))
    require(initial, "Initial invariant not valid on arbitrary tape")
    # The halt has no action in either table, and phi fixes it.  All other
    # controls in the old domain map to working controls in the new one.
    require(all((254, b) not in old and (254, b) not in new for b in (0, 1)), "Halt has a row")
    dense_rows, dense_states = read_table(dense, DENSE_SHA, halt=215)
    mapping = {int(k): int(v) for k, v in json.loads(canonicalization.read_text())["native_to_dense"].items()}
    require(set(mapping) == states | {254}, "Renaming source domain")
    require(set(mapping.values()) == set(range(216)), "Renaming target range")
    require(mapping[0] == 0 and mapping[254] == 215, "Renaming initial/terminal")
    require(dense_rows == {(mapping[q], b): (w, d, mapping[z]) for (q, b), (w, d, z) in new.items()},
            "Dense table is not the supplied renaming")
    return {
        "status": "PASS_FINITE_HYPOTHESES",
        "proof_status": "Ordinary all-tape theorem; finite certificate checked independently; no new kernel endpoint",
        "revision": REVISION,
        "parent_sha256": PARENT_SHA,
        "candidate_sha256": CANDIDATE_SHA,
        "dense_sha256": DENSE_SHA,
        "dense_bijection_checked": True,
        "working_states": len(states), "rows": len(old),
        "all_state_windows": 32 * len(states),
        "invariant_valid_windows": checked,
        "one_step_windows": one, "three_step_windows": three,
        "invariant_start_all_tapes": initial,
        "changed_rows": changed,
        "relation": "same complete tape and head; phi(176)=52; all other controls fixed",
        "scope": "All binary initial tapes and all initial head positions, initial control0",
        "dependency": "Primary K215 consistency calibration is inherited, not rederived",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    root = Path(__file__).resolve().parent
    parser.add_argument("--parent", type=Path, default=root / "k215.native.tm")
    parser.add_argument("--candidate", type=Path, default=root / "cm215.native.tm")
    parser.add_argument("--dense", type=Path, default=root / "cm215.tm")
    parser.add_argument("--canonicalization", type=Path, default=root / "cm215-canonicalization.json")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    report = json.dumps(check(args.parent, args.candidate, args.dense, args.canonicalization), indent=2) + "\n"
    if args.output:
        args.output.write_text(report)
    print(report, end="")


if __name__ == "__main__":
    main()
