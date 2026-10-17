#!/usr/bin/env python3
"""Segment bisimulation between the decoder tree Prog254 and the 219-node DAG.

Both programs run in Wade's path semantics. Between two register tests a
path program only increments, breaks and continues, none of which read a
register, so a run is a sequence of *segments*: from a test site, follow the
leaves on the instruction pointer alone, collecting the increments, up to the
next `decnz` or `halt` leaf. Two programs halt on the same register files if
there is a set of related pairs of test sites (both `halt`, or both
`decnz r` on the same register) such that, for each outcome of the test, the
two segments increment every register equally often and end at a related
pair; the start pair is the pair of segments from the empty pointer.

This script explores that relation from the start pair and writes it as a
certificate (one entry per related pair: the two test-site pointers and the
indices of the successor pairs for the nonzero and zero outcomes). It is the
counterpart of upstream `Bisim.v`/`Cert254.v` (Jeff's verification of
Mira-Cult's machine, busy-beaver 297ab8df); the certificate here is
regenerated independently and is untrusted: the Lean kernel re-checks it.

Usage (from the repository root):
    py -I Computability/BusyBeaver/Research/ZFC/bisim254.py [--stats] [--out FILE]
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[4]
ZFC = REPO / "Computability/BusyBeaver/Lean/BusyBeaver/ZFC"
EDGE = r"\(?\.(node|inc|decnz|brk|cont|halt)(?:\s+(\d+))?\)?"


def edge(kind: str, arg: str | None) -> tuple[str, int]:
    return (kind, int(arg) if arg else 0)


def load_prog254() -> list[tuple]:
    text = (ZFC / "Prog254.lean").read_text(encoding="utf-8")
    rows = {}
    for m in re.finditer(r"^\s*\(" + EDGE + r",\s*" + EDGE + r"\),?\s*--\s*(\d+)\s*$", text, re.M):
        rows[int(m.group(5))] = (edge(m.group(1), m.group(2)), edge(m.group(3), m.group(4)))
    assert sorted(rows) == list(range(6459)), len(rows)
    return [rows[i] for i in range(6459)]


def load_dag254() -> list[tuple]:
    text = (ZFC / "Dag254.lean").read_text(encoding="utf-8")
    rows = {}
    for m in re.finditer(r"^\s*\|\s*(\d+)\s*=>\s*\(" + EDGE + r",\s*" + EDGE + r"\)", text, re.M):
        rows[int(m.group(1))] = (edge(m.group(2), m.group(3)), edge(m.group(4), m.group(5)))
    assert sorted(rows) == list(range(219)), len(rows)
    return [rows[i] for i in range(219)]


class Prog:
    def __init__(self, rows):
        self.rows = rows
        self.fuel = len(rows) + 1
        self.bitsteps = 0

    def tsite(self, P):
        """Leaf reached from P and the bits read (zero padded)."""
        n, i = 0, 0
        for _ in range(self.fuel):
            b = P[i] if i < len(P) else False
            e = self.rows[n][1 if b else 0]
            i += 1
            self.bitsteps += 1
            if e[0] != "node":
                Q = [P[j] if j < len(P) else False for j in range(i)]
                return e, Q
            n = e[1]
        return None


def inc_path(Q):
    Q = list(Q)
    i = len(Q) - 1
    while i >= 0 and Q[i]:
        Q[i] = False
        i -= 1
    if i < 0:
        return Q  # overflow: all zeros, same length (the root restarts)
    Q[i] = True
    return Q


def strip_path(b, k, Q):
    Q = list(Q)
    while k > 0 and Q:
        x = Q.pop()
        if x == b:
            k -= 1
    return Q


def brk(k, Q):
    return inc_path(strip_path(False, k, Q))


def cont(k, Q):
    return strip_path(True, k, Q)


def seg(p: Prog, P, fuel=1000):
    incs = []
    for _ in range(fuel):
        s = p.tsite(P)
        if s is None:
            return None
        (kind, a), Q = s
        if kind == "inc":
            incs.append(a)
            P = inc_path(Q)
        elif kind == "brk":
            P = brk(a, Q)
        elif kind == "cont":
            P = cont(a, Q)
        elif kind in ("decnz", "halt"):
            return incs, P
        else:
            return None
    return None


def counts(l):
    d = {}
    for r in l:
        d[r] = d.get(r, 0) + 1
    return d


def build(p1: Prog, p2: Prog):
    """Explore related test-site pairs; return entries (P1, P2, j, k)."""
    index: dict[tuple, int] = {}
    entries: list[list] = []
    work: list[int] = []

    def pair_of(A, B):
        s1, s2 = seg(p1, A), seg(p2, B)
        if s1 is None or s2 is None:
            raise SystemExit(f"segment failure from {A} / {B}")
        (l1, P1), (l2, P2) = s1, s2
        if counts(l1) != counts(l2):
            raise SystemExit(f"increment mismatch from {A} / {B}: {l1} vs {l2}")
        key = (tuple(P1), tuple(P2))
        if key not in index:
            index[key] = len(entries)
            entries.append([P1, P2, None, None])
            work.append(index[key])
        return index[key]

    pair_of([], [])
    while work:
        i = work.pop()
        P1, P2 = entries[i][0], entries[i][1]
        (e1, Q1), (e2, Q2) = p1.tsite(P1), p2.tsite(P2)
        if e1[0] == "halt" and e2[0] == "halt":
            entries[i][2] = entries[i][3] = 0
            continue
        if e1[0] != "decnz" or e2[0] != "decnz" or e1[1] != e2[1]:
            raise SystemExit(f"unrelated test sites {P1}:{e1} / {P2}:{e2}")
        entries[i][2] = pair_of(inc_path(Q1), inc_path(Q2))
        entries[i][3] = pair_of(brk(1, Q1), brk(1, Q2))
    return entries


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--stats", action="store_true")
    ap.add_argument("--out", type=Path)
    args = ap.parse_args()
    p254, dag = Prog(load_prog254()), Prog(load_dag254())
    entries = build(p254, dag)
    print(f"{len(entries)} related test-site pairs")
    if args.stats:
        # Cost of one full check in each direction (what the kernel will evaluate).
        p254.bitsteps = dag.bitsteps = 0
        for P1, P2, _, _ in entries:
            for p, P in ((p254, P1), (dag, P2)):
                (kind, _), Q = p.tsite(P)
                if kind == "decnz":
                    seg(p, inc_path(Q))
                    seg(p, brk(1, Q))
        print(f"walk bit-steps per direction: Prog254 {p254.bitsteps}, dag254 {dag.bitsteps}")
        print(f"max pointer length: {max(max(len(e[0]), len(e[1])) for e in entries)}")
    if args.out:
        args.out.write_text(json.dumps(entries), encoding="utf-8")
    return 0


if __name__ == "__main__":
    sys.exit(main())
