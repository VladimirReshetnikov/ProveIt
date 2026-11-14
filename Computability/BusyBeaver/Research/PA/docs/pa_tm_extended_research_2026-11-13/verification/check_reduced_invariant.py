#!/usr/bin/env python3
"""Check the final joint assertions, independently of the narrowing process."""
import hashlib
import json
import sys
from pathlib import Path
from check_dbm_invariant import ROOT, close, guarded, shifted, included, INF

sys.path.insert(0, str(ROOT / "verification"))
from core import program


def reduced(a, masks):
    masks = set(masks)
    if a is None or not masks:
        return None, frozenset()
    a = [row.copy() for row in a]
    while True:
        for r in range(9):
            if all(not (m >> r) & 1 for m in masks):
                a[r][9] = min(a[r][9], 0)
            if all((m >> r) & 1 for m in masks):
                a[9][r] = min(a[9][r], -1)
        a = close(a)
        if a is None:
            return None, frozenset()
        implications = [(r, s) for r in range(9) for s in range(9)
                        if r != s and a[r][s] <= 0]
        zero = [r for r in range(9) if a[r][9] <= 0]
        positive = [r for r in range(9) if a[9][r] <= -1]
        keep = {m for m in masks
                if all(not (m >> r) & 1 for r in zero)
                and all((m >> r) & 1 for r in positive)
                and all(not (m >> r) & 1 or (m >> s) & 1 for r, s in implications)}
        if not keep:
            return None, frozenset()
        if keep == masks:
            return a, frozenset(masks)
        masks = keep


def main():
    source = ROOT / "inputs/pa196/PA196/Program.lean"
    path = Path(__file__).with_name("reduced_certificate.txt")
    lines = path.read_text().splitlines()
    count, rounds, reported_edges, reported_failures = map(int, lines[0].split())
    _, ops = program()
    assert count == len(ops) == len(lines) - 1
    states = []
    patterns = 0
    for pc, line in enumerate(lines[1:]):
        fields = list(map(int, line.split()))
        assert len(fields) == 110 and fields[0] == pc and fields[1] in (0, 1)
        maskbits = sum(x << (64*k) for k, x in enumerate(fields[102:]))
        masks = frozenset(m for m in range(512) if (maskbits >> m) & 1)
        if fields[1]:
            assert not masks
            states.append((None, masks))
            continue
        a = [[INF if fields[2+10*i+j] >= 100000000 else fields[2+10*i+j]
              for j in range(10)] for i in range(10)]
        aa, mm = reduced(a, masks)
        assert aa == a and mm == masks
        states.append((a, masks))
        patterns += len(masks)
    a0, m0 = states[25]
    initial = [2] + [0]*9
    assert 1 in m0 and a0 is not None
    assert all(initial[i]-initial[j] <= a0[i][j] for i in range(10) for j in range(10))
    checked = 0
    empty_edges = 0
    for pc, op in enumerate(ops):
        a, masks = states[pc]
        if op[0] == "halt":
            images = []
        elif op[0] == "jump":
            images = [(op[1], a, masks)]
        elif op[0] == "inc":
            r = op[1]
            images = [(op[2], shifted(a, r, 1), {m | (1 << r) for m in masks})]
        elif op[0] == "dec":
            r = op[1]
            mz = {m for m in masks if not (m >> r) & 1}
            mp = {m for m in masks if (m >> r) & 1}
            images = [(op[2], guarded(a, r, False), mz),
                      (op[3], shifted(guarded(a, r, True), r, -1),
                       mp | {m & ~(1 << r) for m in mp})]
        else:
            raise AssertionError(op)
        for dest, image, image_masks in images:
            aa, mm = reduced(image, image_masks)
            target, target_masks = states[dest]
            assert included(aa, target), (pc, dest, "bounds")
            assert mm <= target_masks, (pc, dest, "patterns")
            if aa is None:
                empty_edges += 1
            else:
                checked += 1
    result = {
        "ok": True,
        "certificate_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "sites": count,
        "site_pattern_pairs": patterns,
        "checked_nonempty_joint_edges": checked,
        "checked_empty_joint_edges": empty_edges,
        "bottom_sites": [i for i, (a, _) in enumerate(states) if a is None],
        "reported_edges_match": checked == reported_edges,
        "initial_configuration_included": True,
    }
    Path(__file__).with_name("reduced_invariant_check.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
