#!/usr/bin/env python3
"""Independent certificate checker using Python integer and infinity bounds.

The C++ worklist and widening code are not imported or reproduced. This checks
the supplied assertions directly against source instruction transfer.
"""
import hashlib
import json
import math
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "verification"))
from core import program

N = 10
ZERO = 9
INF = math.inf


def close(a):
    if a is None:
        return None
    a = [row.copy() for row in a]
    # Domain is N^9; coordinate nine is the fixed constant zero.
    for i in range(9):
        a[ZERO][i] = min(a[ZERO][i], 0)
    for k in range(N):
        for i in range(N):
            for j in range(N):
                a[i][j] = min(a[i][j], a[i][k] + a[k][j])
    return None if any(a[i][i] < 0 for i in range(N)) else a


def guarded(a, r, positive):
    if a is None:
        return None
    a = [row.copy() for row in a]
    if positive:
        a[ZERO][r] = min(a[ZERO][r], -1)
    else:
        a[r][ZERO] = min(a[r][ZERO], 0)
    return close(a)


def shifted(a, r, change):
    if a is None:
        return None
    offset = [change if i == r else 0 for i in range(N)]
    return [[a[i][j] + offset[i] - offset[j] for j in range(N)] for i in range(N)]


def included(a, b):
    return a is None or (b is not None and all(a[i][j] <= b[i][j]
                                              for i in range(N) for j in range(N)))


def main():
    path = ROOT / "verification/dbm_certificate.txt"
    lines = path.read_text().splitlines()
    count, reported_iterations, reported_edges = map(int, lines[0].split())
    _, ops = program()
    assert count == len(ops) == len(lines) - 1
    bounds = []
    noncanonical = []
    for expected, line in enumerate(lines[1:]):
        row = list(map(int, line.split()))
        assert len(row) == 102 and row[0] == expected and row[1] in (0, 1)
        if row[1]:
            bounds.append(None)
            continue
        a = [[INF if row[2 + 10*i + j] >= 100000000 else row[2 + 10*i + j]
              for j in range(N)] for i in range(N)]
        b = close(a)
        assert b is not None
        if a != b:
            noncanonical.append(expected)
        bounds.append(b)
    initial = [2] + [0] * 9
    assert bounds[25] is not None
    assert all(initial[i] - initial[j] <= bounds[25][i][j]
               for i in range(N) for j in range(N))

    checked = 0
    unreachable_edges = 0
    for pc, op in enumerate(ops):
        a = bounds[pc]
        if op[0] == "halt":
            successors = []
        elif op[0] == "jump":
            successors = [(op[1], a)]
        elif op[0] == "inc":
            successors = [(op[2], shifted(a, op[1], 1))]
        elif op[0] == "dec":
            successors = [(op[2], guarded(a, op[1], False)),
                          (op[3], shifted(guarded(a, op[1], True), op[1], -1))]
        else:
            raise AssertionError(op)
        for dest, image in successors:
            assert 0 <= dest < count
            assert included(image, bounds[dest]), (pc, dest)
            if image is None:
                unreachable_edges += 1
            else:
                checked += 1

    # Separately compare the C++ analysis input to the actual parsed source.
    native_input = ROOT / "verification/dbm_input.txt"
    raw = native_input.read_text().splitlines()
    assert int(raw[0]) == len(ops)
    assert len(raw) == len(ops) + 1
    for op, line in zip(ops, raw[1:]):
        expected = {"halt": lambda: [0, -1, -1, -1],
                    "jump": lambda: [3, -1, -1, op[1]],
                    "inc": lambda: [1, op[1], -1, op[2]],
                    "dec": lambda: [2, op[1], op[2], op[3]]}[op[0]]()
        assert list(map(int, line.split())) == expected

    result = {
        "ok": True,
        "certificate_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "source_sha256": hashlib.sha256((ROOT / "inputs/pa196/PA196/Program.lean").read_bytes()).hexdigest(),
        "sites": count,
        "nonempty_transfer_edges_checked": checked,
        "empty_transfer_edges_checked": unreachable_edges,
        "reported_edges_match": checked == reported_edges,
        "bottom_sites": [i for i, a in enumerate(bounds) if a is None],
        "noncanonical_sites": noncanonical,
        "cpp_input_matches_source": True,
        "initial_vector_satisfies_site_25": True,
    }
    Path(__file__).with_name("dbm_invariant_check.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
