#!/usr/bin/env python3
"""Reconstruct the 239-state machine from the pinned 240-state table.

This is an exact finite construction check, not an inference about nonhalting.
No machine-producing module or saved verification receipt is trusted as input.
"""
from pathlib import Path
from hashlib import sha256
import argparse
import json
import sys

if not __debug__ or sys.flags.optimize:
    raise RuntimeError("Run with assertions enabled; -O is not supported.")

ROOT = Path(__file__).resolve().parents[1]
PINS = {
    "reference/zfc240_old.tm": "547dd69da66f66dd48238a53d34b52a3ce85bb6c7d01534dd1cfb815507f248f",
    "reference/zfc240.tm": "508b55a6dfdf96a42f09c49e410e078ae7478a1d0257d78d25503b4da24541cd",
    "machines/zfc239_old.tm": "76a9574ac0385b96dbd558fa852a222e1d9025e48e34dc3590384146726d2a9b",
    "machines/zfc239.tm": "4447a2423907f2b96e8bcd6c88ed2d1e353f925fb8cf36ca913224ddce5914ba",
    "machines/sites_logical.json": "74b1e7f73cc3ffe7761e36ab2d57a26e0ba34d3ac624f2472799e6ac41d5a51d",
}


def read(path):
    result, start = {}, None
    for line in path.read_text().splitlines():
        if line.startswith("#! start "):
            assert start is None
            start = int(line.split()[-1])
        elif line and not line.startswith("#"):
            q, b, w, d, t = line.split()
            q, b, w, t = map(int, (q, b, w, t))
            assert b in (0, 1) and w in (0, 1) and d in ("L", "R")
            assert (q, b) not in result
            result[q, b] = w, d, t
    return start, result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", type=Path, default=ROOT)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    for name, wanted in PINS.items():
        assert sha256((args.root / name).read_bytes()).hexdigest() == wanted, name
    start, old = read(args.root / "reference/zfc240_old.tm")
    assert start == 95 and len(old) == 480
    assert old[80, 0] == (0, "R", 25)
    assert old[91, 1] == (0, "L", 50)
    assert old[169, 0] == (0, "R", 57)
    assert old[169, 1] == (0, "R", 56)
    assert [key for key, row in old.items() if row[2] == 169] == [(147, 0)]
    new = dict(old)
    new[80, 0] = 0, "L", 106
    new[91, 1] = 1, "L", 167
    new[147, 0] = 0, "R", 80
    del new[169, 0]
    del new[169, 1]
    assert read(args.root / "machines/zfc239_old.tm") == (95, new)
    states = {q for q, _ in new}
    assert len(states) == 239 and len(new) == 478
    assert all((q, b) in new for q in states for b in (0, 1))
    assert {t for _, _, t in new.values()} - states == {254}
    order = [95] + sorted(states - {95})
    rename = dict(zip(order, range(239))) | {254: 239}
    canonical = {(rename[q], b): (w, d, rename[t])
                 for (q, b), (w, d, t) in new.items()}
    assert read(args.root / "machines/zfc239.tm") == (0, canonical)
    mapping = json.loads((args.root / "machines/renumbering.json").read_text())
    assert mapping == {"start": 0, "dispatcher": 84, "halt": 239,
                       "old_to_new": {str(q): n for q, n in rename.items()}}
    halt_rows = [[q, b, w, d, t] for (q, b), (w, d, t) in canonical.items() if t == 239]
    assert len(halt_rows) == 1
    reachable = {0}
    pending = [0]
    while pending:
        q = pending.pop()
        if q == 239:
            continue
        for b in (0, 1):
            t = canonical[q, b][2]
            if t not in reachable:
                reachable.add(t)
                pending.append(t)
    assert reachable == set(range(240))
    sites = json.loads((args.root / "machines/sites_logical.json").read_text())
    assert len(sites) == 6455
    assert sum(2 if op == "CD" else 1 for _, op, _ in sites) == 8386
    result = {
        "status": "EXACT_CONSTRUCTION_AND_RENUMBERING_PASS",
        "working_states": 239, "symbols": 2, "tapes": 1,
        "transition_rows": 478, "start": 0, "dispatcher": 84, "halt": 239,
        "deleted_inherited_state": 169,
        "changed_rows": [[*key, list(old[key]), list(new[key])]
                         for key in sorted(new) if old[key] != new[key]],
        "unique_canonical_halt_row": halt_rows[0],
        "graph_reachable_working_states": len(reachable - {239}),
        "graph_reachability_scope": "Graph reachability does not assert blank-run reachability or minimality.",
        "pins": PINS,
        "checker_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
