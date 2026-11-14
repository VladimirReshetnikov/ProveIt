#!/usr/bin/env python3
"""Replay every final-table primitive contract over arbitrary natural inputs.

This driver uses the inherited symbolic engine unmodified. Its induction rules
are described in paper/runtime.tex; it is not a proof-assistant kernel.
"""
from pathlib import Path
import json
import sys
import time
from core import census, read_table, require, sha256, write_json

if not __debug__ or sys.flags.optimize:
    raise RuntimeError("Runtime verification requires assertions: do not use -O or PYTHONOPTIMIZE.")
import symbolic_runtime as symbolic

ROOT = Path(__file__).resolve().parents[1]


def main():
    started = time.monotonic()
    native_path = ROOT / "machine/u211.native.tm"
    source_path = ROOT / "machine/sites.json"
    table = read_table(native_path)
    states = census(table, 211, 254)
    sites = json.loads(source_path.read_text())
    require(len(sites) == 3909, "Wrong source-site count")
    mapping = {int(k): int(v) for k, v in
               json.loads((ROOT / "inputs/legacy_mapping.json").read_text()).items()}
    for state in states | {254}:
        mapping.setdefault(state, state + 1000)
    require(len({mapping[q] for q in states | {254}}) == 212,
            "Legacy state relabeling is not injective")
    require(mapping[84] == 96 and mapping[254] == 254,
            "Dispatcher or halt relabeled incorrectly")
    relabeled = {(mapping[q], bit): (write, move, mapping[target])
                 for (q, bit), (write, move, target) in table.items()}
    lemmas, blocks = symbolic.prove_blocks(relabeled)
    cases, used = [], set()
    for index, site in enumerate(sites):
        for positive in ((False, True) if site[1] == "CD" else (False,)):
            result = symbolic.case(relabeled, lemmas, site, positive)
            used.update(result["rows"])
            result["rows"] = sorted(result["rows"])
            result.pop("trace")
            cases.append({"index": index, "positive": positive, **result})
        if index % 500 == 0:
            print(f"Runtime: {index + 1}/3909 sites, {len(cases)} contracts", flush=True)
    for block in blocks:
        for event in block["trace"]:
            used.add(tuple(event[1][:2]))
    require(used == set(relabeled), "The final literal table is not fully covered")
    require(len(cases) == 5084, "Wrong contract count")
    steps = sum(case["symbolic_steps"] for case in cases)
    minimum = min(case["duration"][0] for case in cases)
    require(steps == 1280108 and minimum == 5, "Certificate changed")
    summary = {
        "status": "UNIVERSAL_PRIMITIVE_CONTRACTS_PASS",
        "cases": len(cases), "site_count": len(sites),
        "working_states": len(states), "literal_rows": len(used),
        "symbolic_steps": steps, "minimum_duration_constant": minimum,
        "header_base": symbolic.HEADER_BASE,
        "arbitrary_natural_primary_registers": 9,
        "arbitrary_natural_extra_gap": True,
        "arbitrary_nonempty_finite_spare_register_list": True,
        "whole_tape_including_zero_exterior": True,
        "native_sha256": sha256(native_path.read_bytes()),
        "source_sha256": sha256(source_path.read_bytes()),
        "blocks": blocks,
        "seconds": round(time.monotonic() - started, 3),
        "proof_status": "Executable symbolic induction, not a kernel-checked PA endpoint",
    }
    write_json(ROOT / "evidence/runtime.json", summary)
    (ROOT / "evidence/runtime_cases.json").write_text(
        json.dumps(cases, separators=(",", ":")) + "\n")
    print(json.dumps({k: v for k, v in summary.items() if k != "blocks"}, indent=2))


if __name__ == "__main__":
    main()
