#!/usr/bin/env python3
"""Check every local case of the invariant-based CM215 simulation.

The input tables use the repository's identical dense canonicalization.
The window is not a bounded-tape approximation: the checker rejects a read
outside the three observed cells.  Unobserved cells are unchanged on each
side of a checked block.  The general induction is proved in the Lean files.
"""
from hashlib import sha256
from itertools import product
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent


def table(path):
    transitions = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        q, b, w, direction, q2 = line.split()
        q, b, w, q2 = map(int, (q, b, w, q2))
        assert b in (0, 1) and w in (0, 1)
        assert direction in ("L", "R") and (q, b) not in transitions
        transitions[q, b] = w, 1 if direction == "R" else -1, q2
    assert set(transitions) == set(product(range(215), (0, 1)))
    assert all(0 <= q2 <= 215 for _, _, q2 in transitions.values())
    return transitions


def phi(q):
    return 52 if q == 170 else q


def invariant(q, h, cells):
    return ((q != 52 or cells[h-1] == 1)
            and (q != 170 or cells[h] == 1 or cells[h-1] == 0)
            and (q != 151 or cells[h+1] == 1))


def advance(transitions, q, h, cells):
    assert h in cells, "A local block inspected an unobserved tape cell"
    w, d, q2 = transitions[q, cells[h]]
    cells = dict(cells)
    cells[h] = w
    return q2, h + d, cells


def main():
    old_path, new_path = HERE / "baseline215.tm", HERE / "marker215.tm"
    assert sha256(old_path.read_bytes()).hexdigest() == (
        "fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090")
    assert sha256(new_path.read_bytes()).hexdigest() == (
        "1f4f084f7293e2b042d5746039f793ff72ed429083b504970c939a5515e666cf")
    old, new = table(old_path), table(new_path)
    changed = [list(k) for k in old if old[k] != new[k]]
    assert len(changed) == 6
    incoming = lambda q: {k: v for k, v in old.items() if v[2] == q}
    assert incoming(52) == {(183, 1): (1, 1, 52), (184, 1): (1, 1, 52)}
    assert incoming(170) == {
        (151, 1): (1, 1, 170), (160, 0): (0, 1, 170),
        (184, 0): (0, 1, 170)}
    assert incoming(151) == {(182, 1): (1, -1, 151)}
    checked, long_blocks = 0, 0
    for q in range(215):
        for bits in product((0, 1), repeat=3):
            cells = dict(zip((-1, 0, 1), bits))
            if not invariant(q, 0, cells):
                continue
            expected = advance(old, q, 0, cells)
            assert invariant(*expected)
            steps = 3 if q in (52, 170) and cells[0] == 0 else 1
            actual = phi(q), 0, cells
            for _ in range(steps):
                assert actual[0] != 215, "Intermediate halt"
                actual = advance(new, *actual)
            assert actual == (phi(expected[0]), expected[1], expected[2])
            checked += 1
            long_blocks += steps == 3
    assert checked == 1710 and long_blocks == 4
    result = {
        "status": "PASS",
        "baseline_sha256": sha256(old_path.read_bytes()).hexdigest(),
        "marker_sha256": sha256(new_path.read_bytes()).hexdigest(),
        "working_states": 215,
        "transition_rows": 430,
        "changed_dense_rows": changed,
        "admissible_state_window_cases": checked,
        "three_step_cases": long_blocks,
        "window_offsets": [-1, 0, 1],
        "scope": "Complete local hypotheses; global arbitrary-tape induction is in Lean",
        "source_commit": "b6c7087477e51c017003bd729e712c8969733223",
    }
    (HERE / "marker_certificate.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
