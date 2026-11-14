#!/usr/bin/env python3
"""Recheck the bundled finite evidence; this is not a Lean kernel build.

Run with ordinary Python 3.10+ (not python -O), from any working directory.
No network access or third-party Python packages are needed.
"""
from collections import deque
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
LOGS = ROOT / "verification/logs"
sys.path.insert(0, str(ROOT / "verification"))

TABLE_HASH = "e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8"
SOURCE_HASH = "8c7c6c6884ecbb8f56e893404bb81162db15ef3dd6fd3212881a93994d63d872"
LABELS_HASH = "44983c537d1287d5947dec3bd8e2f9ba43657368fe8ebe75899d2ede54e7c1a3"


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run_script(relative, *args, cwd=None):
    script = ROOT / relative
    result = subprocess.run([sys.executable, str(script), *map(str, args)],
                            cwd=cwd or ROOT, capture_output=True, text=True)
    (LOGS / (script.stem + ".txt")).write_text(result.stdout + result.stderr)
    need(result.returncode == 0,
         f"Failed: {relative}; see verification/logs/{script.stem}.txt")
    print(f"PASS {relative}", flush=True)
    return result.stdout


def read_table(path):
    rows = {}
    for line in path.read_text().splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        q, b, w, d, n = line.split()
        q, b, w, n = map(int, (q, b, w, n))
        need(b in (0, 1) and w in (0, 1) and d in ("L", "R"), "Bad transition")
        need((q, b) not in rows, "Duplicate transition")
        rows[q, b] = w, d, n
    states = {q for q, _ in rows}
    need(set(rows) == {(q, b) for q in states for b in (0, 1)}, "Incomplete table")
    halts = {n for w, d, n in rows.values()} - states
    need(len(halts) == 1, "Expected one halt label")
    return rows, states, halts.pop()


def canonical(rows, states, halt, start=0):
    names = {start: 0}
    queue = deque([start])
    code = []
    while queue:
        q = queue.popleft()
        for b in (0, 1):
            w, d, n = rows[q, b]
            if n == halt:
                target = "H"
            else:
                if n not in names:
                    names[n] = len(names)
                    queue.append(n)
                target = names[n]
            code.append([names[q], b, w, d, target])
    need(set(names) == states, "Graph-unreachable working state")
    return hashlib.sha256(json.dumps(code, separators=(",", ":")).encode()).hexdigest()


def main():
    need(__debug__, "Do not use python -O: bundled certificate checkers use assertions.")
    LOGS.mkdir(exist_ok=True)
    started = time.monotonic()
    data = ROOT / "inputs/pa196"
    need(digest(data / "data/pa196.tm") == TABLE_HASH, "Published table hash mismatch")
    need(digest(data / "PA196/Program.lean") == SOURCE_HASH, "Source program hash mismatch")
    need(digest(data / "PA196/Conjugacy.lean") == LABELS_HASH, "Native label map mismatch")
    rows, states, halt = read_table(data / "data/pa196.tm")
    need(states == set(range(196)) and halt == 196 and len(rows) == 392,
         "Unexpected table domain")
    need([(q, b, w, d, n) for (q, b), (w, d, n) in rows.items() if n == halt]
         == [(63, 1, 1, "R", 196)], "Unexpected halt transitions")

    # Literal simulation from the fully blank two-way tape.
    q, head, ones = 0, 0, set()
    for step in range(58154):
        need((q, int(head in ones)) in rows, f"Early halt at step {step}")
        w, direction, q = rows[q, int(head in ones)]
        (ones.add if w else ones.discard)(head)
        head += 1 if direction == "R" else -1
    physical = [0, 0, 0, 0, 0, 0, 2, 0, 0] + [1] * 26
    right = [1] + [0] * 47 + [1]
    for value in physical:
        right += [0] + [1] * (value + 1)
    expected = {-1} | {i for i, bit in enumerate(right) if bit}
    need(q == 75 and head == -2 and {x - head for x in ones} == expected,
         "Startup is not the exact canonical source seed")
    startup = {"ok": True, "literal_steps": 58154, "literal_state": q,
               "native_state": 84, "absolute_head": head, "one_cells": len(ones),
               "logical_registers": [2] + [0] * 8, "physical_file": physical,
               "source_site": 25, "entire_tape_matches": True}
    print("PASS exact blank startup", flush=True)

    run_script("comparison/compare_all.py", "--output", ROOT / "comparison/reproduction.json")
    certificates = {}
    for kind in ("zero", "dbm", "reduced"):
        run_script(f"verification/check_{kind}_invariant.py")
        certificates[kind] = json.loads((ROOT / f"verification/{kind}_invariant_check.json").read_text())
        need(certificates[kind]["ok"], f"Failed {kind} invariant")

    import core
    native, labels = core.machine()
    generic = core.validate(native, core.contracts())
    need(generic["ok"] and generic["contracts"] == 4959, "Generic baseline contracts failed")
    print("PASS 4,959 generic symbolic contracts", flush=True)

    # Import last: this module deliberately installs a stronger box oracle.
    import flexible_core
    cases, omitted = flexible_core.flex_contracts()
    generalized = flexible_core.validate_flex(native, cases)
    need(generalized["ok"] and generalized["contracts"] == 4954,
         "Generalized baseline contracts failed")
    need([c[0] for c in omitted] == [7, 8, 3773, 3774, 3775],
         "Unexpected omitted source cases")
    print("PASS 4,954 refined symbolic contracts", flush=True)

    countermodel = run_script("verification/t_replacement_countermodel.py").strip()
    need(countermodel.startswith("23328 finite schema checks pass"), "Countervaluation check changed")

    run_script("auxiliary196/closing_patches.py", cwd=ROOT / "auxiliary196")
    variants = json.loads((ROOT / "auxiliary196/closing_patch_receipt.json").read_text())
    need(len(variants) == 4, "A closing variant failed")
    classes = [canonical(rows, states, halt)]
    masks = json.loads((ROOT / "verification/zero_invariants.json").read_text())["reachable_masks"]
    allowed = int(masks[3692])
    for variant in variants:
        reg = variant["register"]
        need(all(not (mask >> reg) & 1 for mask in range(512) if allowed >> mask & 1),
             "Closing register zero precondition not certified")
        path = ROOT / "auxiliary196" / variant["table"]
        rr, ss, hh = read_table(path)
        need(ss == states and hh == halt, "Closing variant changed state convention")
        changed = [k for k in rows if rows[k] != rr[k]]
        need(changed == [(193, 1)], "Closing variant is not the asserted one-row patch")
        need(digest(path) == variant["sha256"], "Closing table hash mismatch")
        need(variant["validation"]["ok"] and variant["startup_exact"], "Closing validation failed")
        classes.append(canonical(rr, ss, hh))
    need(len(set(classes)) == 5, "Closing variants are not five distinct rooted classes")

    result = {"status": "PASS_BUNDLED_EXECUTABLE_EVIDENCE",
              "strict_target_met": False, "smallest_accepted_working_states": 196,
              "new_lean_kernel_biconditional": False,
              "published_table_sha256": TABLE_HASH,
              "startup": startup, "invariant_certificates": certificates,
              "generic_contracts": generic, "refined_contracts": generalized,
              "omitted_cases": omitted, "closing_variants": variants,
              "distinct_rooted_classes_including_baseline": len(set(classes)),
              "t_countervaluation_finite_supplement": countermodel,
              "elapsed_seconds": round(time.monotonic() - started, 3),
              "scope": "Exact finite data checks and symbolic contracts using unchanged register-engine lemmas; not a full upstream Lean rebuild or a state-count lower bound."}
    output = ROOT / "verification/verification_results.json"
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(f"PASS: {output.relative_to(ROOT)}; target below 196 remains unmet.", flush=True)


if __name__ == "__main__":
    main()
