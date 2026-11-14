#!/usr/bin/env python3
"""Binary TM structural comparisons; no assertion of logical correctness.

The fingerprint convention agrees with ProveIt PA/docs/machine_classes.py.
The whole-table comparison is used only for tables admitting a spanning root.
Hash inequality certifies distinct canonical strings; a hash match is only an
overlap candidate, never used here to establish equivalence of computations.
"""
import hashlib
import json
import re


def parse(data):
    rows = {}
    declared = None
    for line in data.decode("ascii").splitlines():
        line = line.strip()
        if not line:
            continue
        if line.startswith("#"):
            m = re.search(r"\bstart\s*(\d+)", line)
            if m and declared is None:
                declared = int(m[1])
            continue
        q, b, w, d, n = line.split()
        q, b, w, n = map(int, (q, b, w, n))
        if min(q, n) < 0 or b not in (0, 1) or w not in (0, 1) or d not in ("L", "R") or (q, b) in rows:
            raise ValueError("invalid or duplicate transition")
        rows[q, b] = w, d, n
    states = {q for q, b in rows}
    if not states or any((q, b) not in rows for q in states for b in (0, 1)):
        raise ValueError("incomplete binary table")
    if declared is not None and declared not in states:
        raise ValueError("declared start is not a working state")
    halts = {n for w, d, n in rows.values()} - states
    return rows, states, declared, halts


def rooted(rows, states, start, loose=False):
    index = {start: 0}
    order = [start]
    actions = []
    for q in order:
        for b in (0, 1):
            w, d, n = rows[q, b]
            if n in states:
                if n not in index:
                    index[n] = len(order)
                    order.append(n)
                actions.append((w, d, index[n]))
            else:
                actions.append((0, "R", -1) if loose else (w, d, -1))
    encoded = json.dumps(actions, separators=(",", ":")).encode("ascii")
    return hashlib.sha256(encoded).hexdigest(), len(order)


def fingerprint(rows, states, loose=False):
    values = [rooted(rows, states, q, loose=loose) for q in states]
    largest = max(n for h, n in values)
    return min(h for h, n in values if n == largest), largest


def transform(rows, mirror=False, complement=False):
    return {(q, b ^ complement): (w ^ complement,
             ("R" if d == "L" else "L") if mirror else d, n)
            for (q, b), (w, d, n) in rows.items()}


def variants(data, loose=False):
    rows, states, declared, halts = parse(data)
    result = []
    for mirror in (False, True):
        for complement in (False, True):
            h, reachable = fingerprint(transform(rows, mirror, complement), states, loose=loose)
            result.append({"mirror": mirror, "complement": complement,
                           "fingerprint": h, "max_reachable": reachable})
    return result
