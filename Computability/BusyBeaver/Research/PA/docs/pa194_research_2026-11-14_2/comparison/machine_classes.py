#!/usr/bin/env python3
"""Classify five-column Turing machine tables up to renaming of states.

usage: machine_classes.py <table.tm> [<table.tm> ...]

A table has one row "state read write move next" for each state and each read symbol 0, 1,
with move L or R. Lines that start with "#" are comments. A next label without rows of its own
is the halting state.

Start state. A comment containing "start N" declares the start N. Without such a comment the
start is taken to be 0 when the states are labelled 0, 1, ..., n-1, which is the convention of
the packets for their dense tables; this is a convention and not a fact of the file, and some
packets ship tables numbered 0, 1, ..., n-1 whose state 0 is not the start. A table with other
labels and no such comment has no start here. Compare tables by the table class.

machine class   SHA-256 of the transition list in the order in which a traversal from the start
                discovers the states, reading 0 before 1 at each state. Two tables with a start
                have the same machine class exactly when one is the other with its states
                renamed, start to start, as far as the states reachable from the start go. For a
                table whose states are all reachable this is the graph_class_sha256 of
                pa196-vs-u208/archive-audit/catalog.py.
table class     the least machine class over all choices of the start among the states from
                which the most states are reachable. Two tables have the same table class
                exactly when one is the other with its states renamed, whatever the start.
"""
import hashlib
import json
import re
import sys


def parse(data):
    rows = {}
    declared = None
    for line in data.decode("ascii").splitlines():
        if not line.strip():
            continue
        if line.lstrip().startswith("#"):
            m = re.search(r"\bstart\s*(\d+)", line)
            if m and declared is None:
                declared = int(m.group(1))
            continue
        q, b, w, d, n = line.split()
        q, b, w, n = int(q), int(b), int(w), int(n)
        if b not in (0, 1) or w not in (0, 1) or d not in ("L", "R") or (q, b) in rows:
            raise ValueError("invalid row: " + line)
        rows[q, b] = (w, d, n)
    states = {q for q, b in rows}
    if not states or any((q, b) not in rows for q in states for b in (0, 1)):
        raise ValueError("a state lacks a row")
    if declared is not None:
        start = declared
    elif sorted(states) == list(range(len(states))):
        start = 0
    else:
        start = None
    if start is not None and start not in states:
        raise ValueError("the start has no rows")
    return rows, states, start, declared is not None


def rooted(rows, states, start, mirror=False, loose=False):
    """Return (class, number of states reachable from start).

    mirror exchanges L and R; loose ignores the symbol and the move of a halting transition.
    Both are used only to test whether further identifications would merge anything.
    """
    index = {start: 0}
    order = [start]
    out = []
    for q in order:
        for b in (0, 1):
            w, d, n = rows[q, b]
            if mirror:
                d = "L" if d == "R" else "R"
            if n in states:
                if n not in index:
                    index[n] = len(index)
                    order.append(n)
                out.append((w, d, index[n]))
            else:
                out.append((0, "R", -1) if loose else (w, d, -1))
    return hashlib.sha256(json.dumps(out, separators=(",", ":")).encode()).hexdigest(), len(order)


def classify(data):
    rows, states, start, declared = parse(data)
    by_root = {q: rooted(rows, states, q) for q in states}
    most = max(r for _, r in by_root.values())
    table = min(h for h, r in by_root.values() if r == most)
    info = {"states": len(states), "start": start, "declared": declared, "table": table,
            "halting": sorted({n for w, d, n in rows.values()} - states),
            "roots": {h for h, r in by_root.values() if r == most}}
    if start is None:
        info["machine"] = None
        info["reachable"] = most
    else:
        info["machine"], info["reachable"] = by_root[start]
        a = rooted(rows, states, start, loose=True)[0]
        b = rooted(rows, states, start, mirror=True, loose=True)[0]
        info["loose"] = min(a, b)
    return info


if __name__ == "__main__":
    for path in sys.argv[1:]:
        i = classify(open(path, "rb").read())
        start = "none" if i["start"] is None else "%d (%s)" % (i["start"], "declared" if i["declared"] else "by convention")
        print("%s\tstates=%d\treachable=%d\tstart=%s\tmachine=%s\ttable=%s" % (
            path, i["states"], i["reachable"], start, i["machine"] or "-", i["table"]))
