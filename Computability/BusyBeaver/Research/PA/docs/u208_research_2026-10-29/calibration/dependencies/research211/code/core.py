"""Strict literal-table utilities; no optimization or search."""
from pathlib import Path
import hashlib
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def read_table(path):
    table, starts = {}, []
    for line in Path(path).read_text().splitlines():
        if line.startswith("#! start "):
            starts.append(int(line[9:]))
        if not line or line.startswith("#"):
            continue
        parts = line.split()
        require(len(parts) == 5, "A transition must have five fields")
        q, bit, write, direction, target = parts
        q, bit, write, target = map(int, (q, bit, write, target))
        require(q >= 0 and target >= 0, "Negative state")
        require(bit in (0, 1) and write in (0, 1), "Nonbinary symbol")
        require(direction in ("L", "R"), "Invalid move")
        require((q, bit) not in table, "Duplicate transition")
        table[q, bit] = write, 1 if direction == "R" else -1, target
    require(starts == [0], "Exactly one start declaration, state 0, is required")
    return table


def encode(table):
    return ("#! start 0\n" + "".join(
        f"{q} {bit} {write} {'R' if move == 1 else 'L'} {target}\n"
        for (q, bit), (write, move, target) in sorted(table.items())
    )).encode("ascii")


def census(table, count, halt):
    states = {q for q, _ in table}
    require(len(states) == count, "Wrong working-state count")
    require(set(table) == {(q, bit) for q in states for bit in (0, 1)},
            "Incomplete table")
    require(0 in states and halt not in states, "Start/halt convention")
    require(all(w in (0, 1) and d in (-1, 1) for w, d, _ in table.values()),
            "Invalid transition")
    require({z for _, _, z in table.values()} - states == {halt},
            "Target closure")
    reached, queue = {0}, [0]
    for q in queue:
        for bit in (0, 1):
            target = table[q, bit][2]
            if target != halt and target not in reached:
                reached.add(target)
                queue.append(target)
    require(reached == states, "A working state is graph-unreachable")
    return states


def write_json(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + "\n")
