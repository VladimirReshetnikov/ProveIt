#!/usr/bin/env python3
"""Independent finite local certificate for K215 -> CM215.

No code from either machine package is imported. This exhausts all radius-two
binary windows, not bounded runs: a radius-one invariant after a single TM
step depends on at most the old radius-two window. The accompanying proof
explains why the checks imply all-tape equihalting from control zero.

Python is not a proof-assistant kernel. This is a finite certificate checker
and a reproducible bridge specification for a subsequent kernel proof.
"""
from pathlib import Path
from itertools import product
from collections import Counter
import argparse
import hashlib
import json

PIN = "b6c7087477e51c017003bd729e712c8969733223"
EXPECTED = {
    "k215.native.tm": "9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2",
    "marker215.native.tm": "e5907f08e0752eada0e25bbf33680341e80e5fe94b52b409aea1ed039edda252",
    "marker215.tm": "1f4f084f7293e2b042d5746039f793ff72ed429083b504970c939a5515e666cf",
}

def require(condition, message):
    if not condition:
        raise ValueError(message)

def read_table(path):
    raw = path.read_bytes()
    require(hashlib.sha256(raw).hexdigest() == EXPECTED[path.name],
            f"wrong pinned table bytes: {path.name}")
    table = {}
    start = None
    for line in raw.decode("ascii").splitlines():
        if line.startswith("#! start "):
            require(start is None, "duplicate start")
            start = int(line[9:])
        elif line and not line.startswith("#"):
            q, b, w, d, z = line.split()
            q, b, w, z = map(int, (q, b, w, z))
            require(b in (0, 1) and w in (0, 1) and d in ("L", "R"),
                    "invalid binary transition")
            require((q, b) not in table, "duplicate transition")
            table[q, b] = (w, -1 if d == "L" else 1, z)
    require(start is not None, "missing initial state")
    states = {q for q, _ in table}
    require(set(table) == set(product(states, (0, 1))), "partial working state")
    require(start in states, "initial state not working")
    return start, table, states

def phi(q):
    return 52 if q == 176 else q

def invariant(q, h, tape):
    if q == 52:
        return tape[h - 1] == 1
    if q == 176:
        return tape[h] == 1 or tape[h - 1] == 0
    if q == 156:
        return tape[h + 1] == 1
    return True

def step(table, config):
    q, h, tape = config
    # A read beyond the represented window is an error, never an implicit zero.
    require(h in tape, "unrepresented tape read")
    w, d, z = table[q, tape[h]]
    out = dict(tape)
    out[h] = w
    return z, h + d, out

def check(input_dir):
    start, old, states = read_table(input_dir / "k215.native.tm")
    new_start, new, new_states = read_table(input_dir / "marker215.native.tm")
    dense_start, dense, dense_states = read_table(input_dir / "marker215.tm")
    require(start == new_start == dense_start == 0, "wrong initial controls")
    require(len(states) == 215 and len(old) == 430 and new_states == states,
            "incorrect state or row census")
    require({z for _, _, z in old.values()} - states == {254}, "old terminals")
    require({z for _, _, z in new.values()} - states == {254}, "new terminals")
    require(phi(254) == 254 and all(phi(q) in new_states for q in states),
            "terminal reflection fails")
    mapping = {int(q): int(z) for q, z in json.loads(
        (input_dir / "canonicalization.json").read_text())["native_to_dense"].items()}
    require(set(mapping) == states | {254}, "incomplete dense map")
    require(set(mapping.values()) == set(range(216)), "nonbijective dense map")
    require(mapping[0] == 0 and mapping[254] == 215, "dense start/halt")
    require(dense_states == set(range(215)), "dense state labels")
    require(dense == {(mapping[q], b): (w, d, mapping[z])
                      for (q, b), (w, d, z) in new.items()}, "dense table mismatch")

    changes = [{"state": q, "read": b, "old": old[q, b], "new": new[q, b]}
               for q, b in sorted(old) if old[q, b] != new[q, b]]
    require(len(changes) == 6, "not the six-row construction")
    # For ordinary states the action is literally the same, modulo target phi.
    for (q, b), (w, d, z) in old.items():
        if q not in (52, 176):
            require(new[phi(q), b] == (w, d, phi(z)), "outer step mismatch")

    counts = Counter()
    invariant_rejections = Counter()
    for q in sorted(states):
        for bits in product((0, 1), repeat=5):
            tape = dict(zip(range(-2, 3), bits))
            counts["all_local_windows"] += 1
            require(invariant(start, 0, tape), "initial invariant")
            if not invariant(q, 0, tape):
                invariant_rejections[q] += 1
                continue
            counts["admissible_local_windows"] += 1
            target = step(old, (q, 0, tape))
            require(invariant(*target), f"noninductive invariant at {q}, {bits}")
            counts["inductiveness_checks"] += 1
            duration = 3 if q in (52, 176) and tape[0] == 0 else 1
            candidate = (phi(q), 0, tape)
            for _ in range(duration):
                require(candidate[0] != 254, "premature target halt")
                candidate = step(new, candidate)
            require(candidate == (phi(target[0]), target[1], target[2]),
                    f"local simulation failure at {q}, {bits}")
            counts[f"length_{duration}_blocks"] += 1
    require(counts == {"all_local_windows": 6880,
                      "admissible_local_windows": 6840,
                      "inductiveness_checks": 6840,
                      "length_1_blocks": 6824,
                      "length_3_blocks": 16}, "unexpected certificate census")
    # An action-count invariant distinguishes the two labelled machines even
    # after state renaming; allowing reflection also fails this count test.
    old_dirs = Counter(d for _, d, _ in old.values())
    new_dirs = Counter(d for _, d, _ in new.values())
    require(old_dirs != new_dirs and old_dirs != Counter({-d: n for d, n in new_dirs.items()}),
            "direction census does not distinguish graphs")
    return {
        "status": "PASS_FINITE_LOCAL_CERTIFICATE",
        "proof_assistant_checked": False,
        "repository_pin": PIN,
        "inputs_sha256": EXPECTED,
        "working_states": 215,
        "transition_rows": 430,
        "invariant": {"52": "left = 1", "176": "current = 1 or left = 0",
                      "156": "right = 1", "others": "True"},
        "counts": dict(counts),
        "rejected_windows_by_control": dict(sorted(invariant_rejections.items())),
        "dense_bijection_verified": True,
        "changes": changes,
        "direction_counts": {"K215": {"L": old_dirs[-1], "R": old_dirs[1]},
                             "CM215": {"L": new_dirs[-1], "R": new_dirs[1]}},
        "scope": "Universal local premises of all-tape equihalting from control 0; "
                 "not a bounded-run test, not a fresh end-to-end kernel proof.",
    }

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inputs", type=Path, default=Path(__file__).parent / "inputs")
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    result = check(args.inputs)
    encoded = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.out:
        args.out.write_text(encoded)
    print(encoded, end="")

if __name__ == "__main__":
    main()
