#!/usr/bin/env python3
"""Replay and audit the exact K217 whole-tape runtime derivations.

Python 3.10+; standard library only.  --upstream is the extracted directory
K218_Dominated_Rho8_2026-10-20.  Only its pinned symbolic engine and helper are
imported.  The machine and source arguments must be the frozen native-label
K217 files; the canonical BFS table uses different labels and is not accepted.

Full mode reconstructs all 6,176 symbolic cases, replays blank startup, and
writes runtime.json, runtime_cases.json, startup.json, and runtime217_audit.json.
Receipt-only mode checks those existing receipts (also accepted as .json.gz)
without reconstructing the symbolic derivations.  It does independently replay
the stored finite startup trace and checks the exact pinned case-receipt bytes.

The full run is executable mathematical evidence using unary/list induction;
it is not a proof-assistant kernel certificate.  Logical/source calibration is
a separate obligation.  No bound here restricts register values or concrete
primitive runtimes; the engine's 4,000-step cap bounds proof construction only.
"""

from collections import Counter
import argparse
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import time


TABLE_HASH = "c902a3c5e81176230a2213d631e2e691573c167fb03e9bdb09ef5c88154f3099"
SITES_HASH = "9eac900e83742470893ea433cb0868e9ff6296f905cd6f3359b7a2c0e3114655"
CASES_HASH = "c944cc9461a2756b127e470a243b06c19a9a3c18b104c568dd0209b01417469e"
STARTUP_HASH = "6360ca7266524eb68415f97677a2655109ad44c5ce88afac5e5a4cefe1299af4"
DEPENDENCIES = {
    "binary/code/runtime/symbolic_runtime.py":
        "7ca30fd11def00e973d8f30997e51fa2dd87ae2eff311ea8c9fc4ac08c9d774f",
    "binary/code/runtime/independent_runtime.py":
        "0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346",
    "binary/code/inputs/legacy_mapping.json":
        "26a4bff859adcc510f1faf4364a597681fec014a136bc1d00dc9ce1904ad6bbf",
}
ENGINE = "binary/code/runtime/symbolic_runtime.py"
HELPER = "binary/code/runtime/independent_runtime.py"
MAPPING = "binary/code/inputs/legacy_mapping.json"
PHY = (6, 2, 0, 4, 3, 7, 8, 5, 1)
SEED_STEPS = 312617
SEED_REGISTERS = [3, 0, 0, 0, 3, 0, 0, 0, 0]
SCOPE = (
    "All independent natural primary values at every decrement guard, "
    "arbitrary natural gap, arbitrary first spare value, arbitrary finite "
    "remaining spare list, and the complete zero exterior. Unary and list "
    "induction; not proof-assistant kernel checked. Logical/source semantics "
    "must be calibrated separately."
)


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def read_receipt(directory, name):
    path = directory / name
    if path.is_file():
        raw = path.read_bytes()
    else:
        path = directory / (name + ".gz")
        need(path.is_file(), f"Missing receipt: {name} or {name}.gz")
        with gzip.open(path, "rb") as stream:
            raw = stream.read()
    return json.loads(raw), raw


def write_json(path, value):
    raw = (json.dumps(value, indent=2) + "\n").encode("utf-8")
    path.write_bytes(raw)
    return raw


def read_inputs(args):
    table_raw = args.table.read_bytes()
    sites_raw = args.sites.read_bytes()
    need(sha(table_raw) == TABLE_HASH, "Table bytes do not match native K217")
    need(sha(sites_raw) == SITES_HASH, "Source bytes do not match K217")
    for relative, expected in DEPENDENCIES.items():
        need(sha((args.upstream / relative).read_bytes()) == expected,
             f"Upstream dependency hash mismatch: {relative}")
    table = {}
    starts = []
    for line in table_raw.decode("ascii").splitlines():
        if line.startswith("#! start "):
            starts.append(int(line[9:]))
            continue
        if not line or line.startswith("#"):
            continue
        q, b, w, direction, target = line.split()
        q, b, w, target = map(int, (q, b, w, target))
        need((q, b) not in table and b in (0, 1) and w in (0, 1)
             and direction in ("L", "R"), "Invalid or duplicate table row")
        table[q, b] = (w, 1 if direction == "R" else -1, target)
    states = {q for q, _ in table}
    need(starts == [0] and len(states) == 217 and len(table) == 434,
         "Initial-state or working-state census mismatch")
    need(set(table) == {(q, b) for q in states for b in (0, 1)},
         "Incomplete transition table")
    need({target for _, _, target in table.values()} - states == {254},
         "Unexpected halt or transition target")
    reachable = {0}
    pending = [0]
    for q in pending:
        for b in (0, 1):
            target = table[q, b][2]
            if target != 254 and target not in reachable:
                reachable.add(target)
                pending.append(target)
    need(reachable == states, "Unreachable working state")
    sites = json.loads(sites_raw)
    need(isinstance(sites, list) and len(sites) == 4751, "Wrong site census")
    for pc, op, arg in sites:
        need(isinstance(pc, str) and 0 < len(pc) <= 64 and set(pc) <= {"0", "1"},
             "Invalid source address")
        need(op in ("CI", "CD", "CB", "CC", "CH"), "Invalid source operation")
        if op == "CH":
            need(arg is None, "Invalid halt argument")
        elif op in ("CI", "CD"):
            need(type(arg) is int and 0 <= arg < 9, "Invalid register index")
        else:
            need(type(arg) is int and arg >= 1, "Invalid control argument")
    leaves = {pc for pc, _, _ in sites}
    prefixes = {pc[:i] for pc in leaves for i in range(len(pc))}
    need(len(leaves) == len(sites) and not leaves & prefixes,
         "Duplicate or non-prefix-free source")
    need(all(p + b in leaves | prefixes for p in prefixes for b in ("0", "1")),
         "Source is not a complete binary tree")
    mapping = {int(k): int(v) for k, v in
               json.loads((args.upstream / MAPPING).read_bytes()).items()}
    for q in states | {254}:
        mapping.setdefault(q, q + 1000)
    inverse = {mapping[q]: q for q in states | {254}}
    need(len(inverse) == 218 and mapping[84] == 96 and mapping[254] == 254,
         "Legacy-state relabeling is not the required injection")
    legacy = {(mapping[q], b): (w, d, mapping[z])
              for (q, b), (w, d, z) in table.items()}
    return table, sites, legacy, inverse


def import_exact(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    need(spec is not None and spec.loader is not None, "Cannot load pinned module")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def seed_frame():
    """Independent finite-support encoding of the complete known seed."""
    head, gap = -5, 80
    physical = [None] * 9
    for logical, physical_index in enumerate(PHY):
        physical[physical_index] = SEED_REGISTERS[logical]
    ones = {head - 1, head + 64 + gap}
    position = head + 64 + gap + 1
    for value in physical + [1] * 130:
        position += 1
        ones.update(range(position, position + value + 1))
        position += value + 1
    need(len(ones) == 277, "Internal seed encoding error")
    return ones


def replay_startup(table, trace=None):
    q, head, ones = 0, 0, set()
    generated = [] if trace is None else trace
    if trace is not None:
        need(len(trace) == SEED_STEPS, "Wrong startup trace length")
    for tick in range(SEED_STEPS):
        bit = int(head in ones)
        need((q, bit) in table, f"Startup undefined at step {tick}")
        write, direction, target = table[q, bit]
        event = [q, head, bit, write, direction, target]
        if trace is None:
            generated.append(event)
        else:
            need(trace[tick] == event, f"Startup trace mismatch at step {tick}")
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        q, head = target, head + direction
    need((q, head) == (84, -5) and ones == seed_frame(),
         "Startup did not produce the complete calibrated seed")
    return {
        "status": "CALIBRATED_DIRTY_ROOT_SEED", "steps": SEED_STEPS,
        "state": q, "head": head, "gap": 80,
        "registers": SEED_REGISTERS.copy(), "spares": [1] * 130,
        "one_cells": sorted(ones), "trace": generated,
    }


def full_replay(args, table, sites, legacy):
    helper = import_exact("independent_runtime", args.upstream / HELPER)
    engine = import_exact("symbolic_runtime", args.upstream / ENGINE)
    need(helper.PHY == PHY and engine.r is helper, "Unexpected imported helper")
    begun = time.monotonic()
    startup = replay_startup(table)
    startup_raw = write_json(args.out / "startup.json", startup)
    print(f"STARTUP PASS: {SEED_STEPS} steps, exact 277-cell support", flush=True)
    lemmas, blocks = engine.prove_blocks(legacy)
    cases = []
    for index, site in enumerate(sites):
        for positive in ((False, True) if site[1] == "CD" else (False,)):
            answer = engine.case(legacy, lemmas, site, positive)
            answer["rows"] = sorted(answer["rows"])
            answer.pop("trace")
            cases.append({"site_index": index, "positive": positive, **answer})
        if (index + 1) % 1000 == 0:
            print(f"SITES {index + 1}/4751; CASES {len(cases)}/6176; "
                  f"SECONDS {time.monotonic() - begun:.3f}", flush=True)
    report = {
        "status": "UNIVERSAL_MATHEMATICAL_PASS",
        "table_sha256": TABLE_HASH, "sites_sha256": SITES_HASH,
        "checker_sha256": DEPENDENCIES[ENGINE],
        "helper_sha256": DEPENDENCIES[HELPER], "working_states": 217,
        "site_count": len(sites), "expected_cases": 6176,
        "proved_cases": len(cases), "failures": [], "blocks": blocks,
        "seconds": time.monotonic() - begun,
        "startup_status": startup["status"],
        "source_semantics": "Separate obligation. Quantified runtime certificate only.",
        "scope": SCOPE,
    }
    report_raw = write_json(args.out / "runtime.json", report)
    cases_raw = write_json(args.out / "runtime_cases.json", cases)
    return report, cases, startup, report_raw, cases_raw, startup_raw


def audit(table, sites, legacy, inverse, data, receipt_only):
    report, cases, startup, report_raw, cases_raw, startup_raw = data
    need(sha(cases_raw) == CASES_HASH, "Exact case-receipt hash mismatch")
    need(sha(startup_raw) == STARTUP_HASH, "Exact startup-receipt hash mismatch")
    for key, expected in {
        "status": "UNIVERSAL_MATHEMATICAL_PASS", "table_sha256": TABLE_HASH,
        "sites_sha256": SITES_HASH, "checker_sha256": DEPENDENCIES[ENGINE],
        "helper_sha256": DEPENDENCIES[HELPER], "working_states": 217,
        "site_count": 4751, "expected_cases": 6176, "proved_cases": 6176,
        "failures": [], "startup_status": "CALIBRATED_DIRTY_ROOT_SEED",
    }.items():
        need(report.get(key) == expected, f"Runtime receipt mismatch: {key}")
    expected_guards = [(i, p) for i, (_, op, _) in enumerate(sites)
                       for p in ((False, True) if op == "CD" else (False,))]
    need(len(expected_guards) == len(cases) == 6176, "Wrong guarded-case census")
    need([(c["site_index"], c["positive"]) for c in cases] == expected_guards,
         "Missing, duplicated, reordered, or wrong guarded case")
    rows, kinds = set(), Counter()
    for case in cases:
        need(type(case["site_index"]) is int and type(case["positive"]) is bool,
             "Wrong guard representation")
        clock, motion = case["duration"], case["motion"]
        need(len(clock) == 13 and all(type(x) is int and x >= 0 for x in clock)
             and clock[0] > 0, "A case lacks a positive affine clock")
        need(len(motion) == 13 and all(type(x) is int for x in motion),
             "Invalid affine displacement")
        count = case["symbolic_steps"]
        need(type(count) is int and 0 < count < 4000,
             "Invalid symbolic proof-construction length")
        need(set(case["kinds"]) <= {"literal", "unary", "list"}
             and all(type(x) is int and x >= 0 for x in case["kinds"].values())
             and sum(case["kinds"].values()) == count, "Rule-use count mismatch")
        kinds.update(case["kinds"])
        for row in case["rows"]:
            need(len(row) == 2 and tuple(row) in legacy, "Receipt uses a foreign row")
            rows.add((inverse[row[0]], row[1]))
    need(rows == set(table), "Primitive derivations do not cover all 434 rows")
    replayed = replay_startup(table, startup["trace"])
    need(startup == replayed, "Startup receipt metadata mismatch")
    return {
        "status": "RECEIPT_AUDIT_PASS" if receipt_only else "FULL_REPLAY_AND_AUDIT_PASS",
        "symbolic_derivations_reconstructed_in_this_run": not receipt_only,
        "receipt_only_limitation": (
            "Audits the exact pinned previous receipts and replays finite startup; "
            "does not reconstruct the 6176 symbolic proofs."
        ) if receipt_only else None,
        "table_sha256": TABLE_HASH, "sites_sha256": SITES_HASH,
        "upstream_dependencies_sha256": DEPENDENCIES,
        "runtime_receipt_sha256": sha(report_raw),
        "case_receipt_sha256": sha(cases_raw),
        "startup_receipt_sha256": sha(startup_raw),
        "working_states": 217, "transition_rows": 434,
        "source_sites": 4751, "ordered_guarded_cases": len(cases),
        "all_affine_clocks_have_nonnegative_integer_coefficients": True,
        "minimum_actual_steps": min(c["duration"][0] for c in cases),
        "maximum_constant_clock": max(c["duration"][0] for c in cases),
        "affine_slot_order": ["constant", "gap"] + [f"r{i}" for i in range(9)]
            + ["first_spare_value", "remaining_spare_list_width"],
        "symbolic_steps": sum(c["symbolic_steps"] for c in cases),
        "maximum_symbolic_steps": max(c["symbolic_steps"] for c in cases),
        "symbolic_rule_uses": dict(kinds),
        "primitive_direct_native_rows": len(rows),
        "all_table_rows_used_by_primitive_derivations": True,
        "startup": {k: v for k, v in startup.items() if k != "trace"},
        "startup_trace_independently_replayed": True,
        "scope": SCOPE,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--upstream", type=Path, required=True)
    parser.add_argument("--table", type=Path, required=True)
    parser.add_argument("--sites", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--receipt-only", action="store_true")
    parser.add_argument("--receipts", type=Path,
                        help="Existing receipt directory; required with --receipt-only")
    args = parser.parse_args()
    need(__debug__ and sys.flags.optimize == 0,
         "Enabled assertions are required; do not use -O or PYTHONOPTIMIZE")
    need(args.receipt_only == (args.receipts is not None),
         "Use --receipt-only and --receipts together, or omit both")
    sys.dont_write_bytecode = True
    table, sites, legacy, inverse = read_inputs(args)
    args.out.mkdir(parents=True, exist_ok=True)
    if args.receipt_only:
        report, report_raw = read_receipt(args.receipts, "runtime.json")
        cases, cases_raw = read_receipt(args.receipts, "runtime_cases.json")
        startup, startup_raw = read_receipt(args.receipts, "startup.json")
        data = report, cases, startup, report_raw, cases_raw, startup_raw
    else:
        data = full_replay(args, table, sites, legacy)
    result = audit(table, sites, legacy, inverse, data, args.receipt_only)
    result["driver_sha256"] = sha(Path(__file__).read_bytes())
    write_json(args.out / "runtime217_audit.json", result)
    print(json.dumps({k: v for k, v in result.items()
                      if k not in ("startup", "affine_slot_order")}, indent=2), flush=True)


if __name__ == "__main__":
    main()
