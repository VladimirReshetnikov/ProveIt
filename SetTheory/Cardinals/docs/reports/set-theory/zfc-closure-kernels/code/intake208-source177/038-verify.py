#!/usr/bin/env python3
"""Independent finite table and complete blank-start corroboration.

The general conclusion comes from MarkerFold.v, not from these finite runs.
"""
from pathlib import Path
import hashlib, json, argparse
from generate_tables import NAMES, parse, render

def advance(rows, c):
    q, h, cells = c
    w, d, z = rows[q, int(h in cells)]
    if w:
        cells.add(h)
    else:
        cells.discard(h)
    return z, h + (1 if d == "R" else -1), cells

def one_run(old, new):
    a, b = (0, 0, set()), (0, 0, set())
    long_blocks = 0
    target_steps = 0
    for n in range(95714):
        q, h, cells = a
        if q == 124 and h - 1 not in cells:
            raise AssertionError("one-marker invariant")
        if q == 127 and h - 1 in cells:
            raise AssertionError("zero-marker invariant")
        duration = 3 if q in (124, 127) and h not in cells else 1
        long_blocks += (duration == 3)
        a = advance(old, a)
        for _ in range(duration):
            b = advance(new, b)
        target_steps += duration
        q, h, cells = a
        if b != (124 if q == 127 else q, h, cells):
            raise AssertionError(f"whole-tape synchronization at parent step {n+1}")
    return {"parent_steps": 95714, "target_steps": target_steps,
            "three_step_blocks": long_blocks, "state": a[0], "head": a[1],
            "one_cells": len(a[2]),
            "complete_one_positions": sorted(a[2])}

def verify(root):
    if render(root) != (root / "MarkerTables.v").read_text():
        raise AssertionError("literal Coq binding")
    tables = {name: parse(root / (name + ".tm")) for name in NAMES}
    old = tables["K215"]
    summary = {"scope": "Finite exact rows and full blank-prefix corroboration; not unbounded proof", "machines": {}}
    for name, rows in tables.items():
        states = {q for q, _ in rows}
        assert len(rows) == 430 and len(states) == 215
        assert set(rows) == {(q, bit) for q in states for bit in (0, 1)}
        assert 254 not in states
        assert all(z in states | {254} for _, _, z in rows.values())
        reached, pending = {0}, [0]
        while pending:
            q = pending.pop()
            for bit in (0, 1):
                z = rows.get((q, bit), (None, None, None))[2]
                if z is not None and z not in reached:
                    reached.add(z)
                    pending.append(z)
        assert reached - {254} == states
        diff = [{"row": list(key), "old": old[key], "new": value}
                for key, value in sorted(rows.items()) if old[key] != value]
        record = {"sha256": hashlib.sha256((root / (name + ".tm")).read_bytes()).hexdigest(),
                  "working_states": len(states), "rows": len(rows),
                  "graph_reachable_working_states": len(reached - {254}), "changes": diff}
        if name != "K215":
            assert len(diff) == 4
            record["blank_synchronization"] = one_run(old, rows)
        summary["machines"][name] = record
    canonical = json.loads((root / "M125.canonicalization.json").read_text())
    mapping = {int(k): v for k, v in canonical["native_to_dense"].items()}
    assert len(mapping) == 216 and set(mapping.values()) == set(range(216))
    assert mapping[0] == 0 and mapping[254] == 215
    dense = parse(root / "M125.dense.tm")
    assert {(mapping[q], bit): (w, d, mapping[z])
            for (q, bit), (w, d, z) in tables["M125"].items()} == dense
    summary["dense_M125"] = {"rows": len(dense), "halt": 215,
        "sha256": hashlib.sha256((root / "M125.dense.tm").read_bytes()).hexdigest(),
        "finite_exact_renaming": True}
    return summary

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = verify(Path(__file__).resolve().parent)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({name: {k: v for k, v in rec.items() if k not in ("changes", "blank_synchronization")}
                      for name, rec in result["machines"].items()}, indent=2))
