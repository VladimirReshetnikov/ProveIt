#!/usr/bin/env python3
"""Run all unbounded instruction proofs for the literal 238-state machine.

The attributed affine/list engine is unchanged. This driver pins its bytes,
validates all source guards, and treats every incomplete proof as a failure.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys
import time
import symbolic_runtime as s

ROOT = Path(__file__).resolve().parents[1]
ENGINE_SHA = "c22f1709a39277c59d163c613e250f27a9e239004a83f643f3bd7d44ad57f145"
HELPER_SHA = "0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346"
TABLE_SHA = "069942be27db9736875ea042320e51ac3b1eac7116cbe01cdce520fa6056f78c"
SITES_SHA = "7fd152d1f5371d2a561d4ad1870d241683b010ce7b7a27399b95363a4537cfb6"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    if not __debug__ or sys.flags.optimize:
        raise SystemExit("Assertions must be enabled.")
    table_path, sites_path = ROOT / "machines/zfc_combined238_old.tm", ROOT / "machines/sites_logical.json"
    assert digest(Path(s.__file__)) == ENGINE_SHA
    assert digest(Path(s.r.__file__)) == HELPER_SHA
    assert digest(table_path) == TABLE_SHA and digest(sites_path) == SITES_SHA
    table, sites = s.r.table(table_path), json.loads(sites_path.read_text())
    working = {q for q, b in table}
    assert len(working) == 238 and len(table) == 476
    assert set(table) == {(q, b) for q in working for b in (0, 1)}
    assert {n for w, d, n in table.values()} - working == {254}
    leaves = set()
    for p, op, arg in sites:
        assert isinstance(p, str) and 0 < len(p) <= 48 and set(p) <= {"0", "1"}
        assert p not in leaves
        leaves.add(p)
        assert op in ("CI", "CD", "CB", "CC", "CH")
        if op in ("CI", "CD"):
            assert type(arg) is int and 0 <= arg < 9
        elif op in ("CB", "CC"):
            assert type(arg) is int and arg >= 1
        else:
            assert arg is None
    prefixes = {p[:i] for p in leaves for i in range(len(p))}
    assert len(leaves) == len(sites) == 6455
    assert not leaves & prefixes
    assert all(p + b in leaves | prefixes for p in prefixes for b in "01")
    lemmas, blocks = s.prove_blocks(table)
    print("Four exact one-block induction schemas proved.", flush=True)
    start = time.monotonic()
    cases, used = [], set()
    for i, site in enumerate(sites):
        for positive in ((False, True) if site[1] == "CD" else (False,)):
            answer = s.case(table, lemmas, site, positive)
            used.update(answer.pop("rows"))
            answer.pop("trace")
            cases.append({"site_index": i, "positive": positive, **answer})
            if len(cases) % 1000 == 0:
                print(f"Proved {len(cases)} of 8386 guards ({time.monotonic()-start:.1f}s).", flush=True)
    assert len(cases) == 8386
    assert used == set(table), "Some literal rows were not exercised"
    total = sum(c["symbolic_steps"] for c in cases)
    minimum = min(c["duration"][0] for c in cases)
    assert (total, minimum) == (2255513, 13)
    result = {
        "status": "UNIVERSAL_238_MATHEMATICAL_PASS",
        "working_states": 238, "transition_rows": 476, "cases": len(cases),
        "symbolic_steps": total, "minimum_actual_steps": minimum,
        "table_sha256": TABLE_SHA, "sites_sha256": SITES_SHA,
        "engine_sha256": ENGINE_SHA, "helper_sha256": HELPER_SHA,
        "driver_sha256": digest(Path(__file__)),
        "blocks": blocks, "directly_used_rows": sorted(used),
        "seconds": time.monotonic() - start,
        "scope": "All natural primary registers, every decrement guard, arbitrary natural extra gap and first spare, arbitrary finite remaining spare list; complete tape endpoints and positive durations. Ordinary mathematical proof, not a proof-assistant kernel endpoint.",
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    args.output.with_name(args.output.stem + "_cases.json").write_text(json.dumps(cases, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k not in ("blocks", "directly_used_rows")}, indent=2))


if __name__ == "__main__":
    main()
