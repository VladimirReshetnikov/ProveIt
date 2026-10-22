#!/usr/bin/env python3
"""Finite replay of K215's maintained symbolic checks and direct read footprints.

This is an independent Python transcription of KRuntimeCore.sstep, KHome.home,
KHomeReady.exec and KSim.checkEdge at the pinned commit. It is an engineering
audit, not a proof-assistant certificate. No received generator is executed.
"""
from __future__ import annotations
import argparse
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path

PIN = "6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95"
SK = [51, 36, 25, 48, 32, 33, 22, 55, 60]
PHYS = [6, 2, 0, 4, 3, 7, 8, 5, 1]
HOME = [2, 3, 5, 9, 15, 23, 34, 50]
B = lambda b: ("bit", int(b))
R = lambda b, a, c: ("run", int(b), a, c)
X = lambda kind="none", r=0: ("box", kind, r)


def read_table(path):
    table = {}
    for line in path.read_text().splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        q, b, w, direction, n = line.split()
        key = (int(q), int(b))
        assert key not in table
        table[key] = (int(w), direction == "R", int(n))
    return table


def ready(table):
    """Check the 15 scan rows and the exact 18-step boundary window."""
    deps = set()
    def get(q, b):
        deps.add((q, b))
        return table.get((q, b))
    for i, q in enumerate(HOME):
        if get(q, 1) != (1, False, 2):
            return False, deps
        if i < 7 and get(q, 0) != (0, False, HOME[i + 1]):
            return False, deps
    cells = {i: int(i == 1) for i in range(-8, 2)}
    original = dict(cells)
    q, h = 2, 0
    for _ in range(18):
        if h not in cells:
            return False, deps
        row = get(q, cells[h])
        if row is None:
            return False, deps
        w, right, q = row
        cells[h] = w
        h += 1 if right else -1
    return q == 84 and h == 2 and cells == original, deps


def oracle(q, br, x):
    _, kind, r = x
    if kind == "none":
        if q in SK:
            r = SK.index(q)
            return (1 if r == 0 else 3), X("mark", r), False
    elif kind == "mark" and r < 9:
        if q == 64:
            return 40, X("inc", r), False
        if q == 0 and br is not None and br[0] == r:
            return (97, X(), False) if br[1] else (40, X("dec", r), True)
    return None


def home(s):
    q, onl, left, right = s
    if q != 2 or not onl:
        return None
    rev = list(reversed(left))
    while rev and (rev[0] == B(0) or rev[0][:2] == ("run", 0)):
        rev.pop(0)
    if not rev or rev.pop(0) != B(1):
        return None
    i = 0
    for seg in reversed(rev):
        if seg[0] == "bit":
            i = 0 if seg[1] else i + 1
            if i >= 8:
                return None
        elif seg[0] == "run":
            _, b, a, c = seg
            if b:
                i = i if c == 0 else 0
            elif a == 0 and i + c < 8:
                i += c
            else:
                return None
        else:
            return None
    return (84, False, (B(1),), tuple(rev) + right)


def sstep(table, br, s, deps, counts):
    q, onl, left, right = s
    def get(b):
        deps.add((q, b))
        counts[(q, b)] += 1
        return table.get((q, b))
    if onl:
        if not left:
            return (q, False, (), (B(0),) + right), False
        seg, rest = left[0], left[1:]
        if seg[0] == "bit":
            return (q, False, rest, (seg,) + right), False
        if seg[0] == "box":
            return None
        _, b, a, c = seg
        row = get(b)
        if row is not None and row[1] is False and row[2] == q:
            return (q, True, rest, (R(row[0], a, c),) + right), False
        if c:
            return (q, True, (B(b), R(b, a, c - 1)) + rest, right), False
        if a == 0:
            return (q, True, rest, right), False
        return None
    if not right:
        return None
    seg, rest = right[0], right[1:]
    if seg[0] == "bit":
        row = get(seg[1])
        if row is None:
            return None
        w, goes_right, nq = row
        if goes_right:
            return (nq, False, (B(w),) + left, rest), True
        return (nq, True, left, (B(w),) + rest), True
    if seg[0] == "run":
        _, b, a, c = seg
        row = get(b)
        if row is not None and row[1] is True and row[2] == q:
            return (q, False, (R(row[0], a, c),) + left, rest), False
        if c:
            return (q, False, left, (B(b), R(b, a, c - 1)) + rest), False
        if a == 0:
            return (q, False, left, rest), False
        return None
    if rest:
        return None
    answer = oracle(q, br, seg)
    if answer is not None:
        nq, box, extra = answer
        return (nq, True, ((B(1),) + left) if extra else left, (box,)), False
    row = get(0)
    if row is not None and row[:2] == (0, False):
        return (row[2], True, left, (seg,)), True
    return None


def norm(segments, trim=False):
    out = []
    for seg in segments:
        if seg[0] == "bit":
            seg = R(seg[1], 0, 1)
        if seg[0] == "run":
            if seg[2:] == (0, 0):
                continue
            if out and out[-1][:2] == seg[:2]:
                old = out.pop()
                seg = R(seg[1], old[2] + seg[2], old[3] + seg[3])
        out.append(seg)
    if trim and out and out[-1][:2] == ("run", 0):
        out.pop()
    return tuple(out)


def matches(s, t):
    return (s[:2] == t[:2] and norm(s[3]) == norm(t[3])
            and norm(s[2], True) == norm(t[2], True))


def inc(path):
    bits = list(path)
    for i in range(len(bits) - 1, -1, -1):
        bits[i] ^= 1
        if bits[i]:
            break
    return tuple(bits)


def strip(b, k, path):
    bits = list(path)
    while k and bits:
        if bits.pop() == b:
            k -= 1
    return tuple(bits)


def target(path, overflow, box):
    growth = int(box[1] == "dec")
    return (84, False, (B(1),), tuple(map(B, path))
            + (R(0, 1, 64 + int(overflow) + growth - len(path)), B(1), box))


def run(table, path, br, tgt, fast):
    s = (84, False, (B(1),), tuple(map(B, path)) + (R(0, 1, 64 - len(path)), B(1), X()))
    moved = False
    deps, counts, shortcuts = set(), Counter(), 0
    for step in range(4000):
        hit = s[0] == 230 if tgt is None else matches(s, tgt)
        if moved and hit:
            return {"steps": step, "queries": sum(counts.values()),
                    "home_shortcuts": shortcuts, "reads": sorted(deps)}
        accelerated = home(s) if fast else None
        if accelerated is not None:
            s, progress = accelerated, True
            shortcuts += 1
        else:
            nxt = sstep(table, br, s, deps, counts)
            if nxt is None:
                raise AssertionError(("symbolic failure", path, br, step, s))
            s, progress = nxt
        moved = moved or progress
    raise AssertionError(("fuel exhausted", path, br))


def obligations(sites):
    for idx, (text, op, r) in enumerate(sites):
        path = tuple(map(int, text))
        assert len(path) <= 48
        if op in ("CI", "CD"):
            assert r < 9
        if op == "CI":
            yield idx, "inc", path, None, target(inc(path), all(path), X("inc", PHYS[r]))
        elif op == "CD":
            pre = strip(0, 1, path)
            yield idx, "zero", path, (PHYS[r], True), target(inc(pre), all(pre), X())
            yield idx, "nonzero", path, (PHYS[r], False), target(inc(path), all(path), X("dec", PHYS[r]))
        elif op == "CB":
            pre = strip(0, r, path)
            yield idx, "break", path, None, target(inc(pre), all(pre), X())
        elif op == "CC":
            yield idx, "continue", path, None, target(strip(1, r, path), False, X())
        elif op == "CH":
            yield idx, "halt", path, None, None
        else:
            raise AssertionError(op)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inputs", type=Path, default=Path(__file__).parent / "inputs")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    table_file, sites_file = args.inputs / "k215_k230labels.tm", args.inputs / "sites215.json"
    table, sites = read_table(table_file), json.loads(sites_file.read_text())
    assert len(table) == 430 and len(sites) == 4751
    fast, ready_deps = ready(table)
    assert fast, "current production table must pass Home readiness"
    rows, frequency = [], Counter()
    for idx, branch, path, br, tgt in obligations(sites):
        ans = run(table, path, br, tgt, fast)
        ans.update(site=idx, branch=branch)
        rows.append(ans)
        frequency.update(map(tuple, ans["reads"]))
    assert len(rows) == 6176
    summary = {
        "pin": PIN,
        "status": "PASS_FINITE_PYTHON_REPLAY_NOT_KERNEL_CERTIFICATE",
        "input_sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                         for p in (table_file, sites_file)},
        "leaves": len(sites), "outcomes": len(rows),
        "home_ready": fast, "home_gate_reads": sorted(ready_deps),
        "home_gate_distinct_rows": len(ready_deps),
        "symbolic_steps": sum(x["steps"] for x in rows),
        "direct_queries": sum(x["queries"] for x in rows),
        "distinct_queried_rows": len(frequency),
        "home_shortcuts": sum(x["home_shortcuts"] for x in rows),
        "distinct_footprints": len({tuple(map(tuple, x["reads"])) for x in rows}),
        "footprint_size_min": min(len(x["reads"]) for x in rows),
        "footprint_size_max": max(len(x["reads"]) for x in rows),
        "footprint_size_mean": sum(len(x["reads"]) for x in rows) / len(rows),
        "row_frequencies": [[q, b, v] for (q, b), v in sorted(frequency.items())],
        "conditions_not_discharged": [
            "No target-table BoxLemmas proof or new machine endpoint is claimed.",
            "Home readiness is checked separately from each direct footprint.",
            "Python replay is not kernel instantiation of the new Lean transport theorem.",
            "No build-time improvement is measured by these query counts."
        ]}
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / "runtime_audit.json").write_text(json.dumps(summary, indent=2) + "\n")
    with gzip.GzipFile(filename=str(args.out / "runtime_footprints.json.gz"), mode="wb", mtime=0) as f:
        f.write((json.dumps(rows, separators=(",", ":")) + "\n").encode())
    print(json.dumps({k: v for k, v in summary.items()
                      if k not in ("row_frequencies", "home_gate_reads")}, indent=2))


if __name__ == "__main__":
    main()
