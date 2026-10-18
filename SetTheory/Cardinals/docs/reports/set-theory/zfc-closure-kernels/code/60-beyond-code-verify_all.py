#!/usr/bin/env python3
"""Portable integration check for the delivered Beyond 252 research packet.

Uses the standard library. Does not invoke a proof assistant or rerun the
full searches. Component outputs are written in a temporary directory.
"""
from __future__ import annotations
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def checksum(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_manifest():
    path = ROOT / "SHA256SUMS"
    if not path.exists():
        return {"status": "not_present_during_assembly"}
    count = 0
    for line in path.read_text().splitlines():
        expected, relative = line.split("  ", 1)
        target = ROOT / relative
        require(target.resolve().is_relative_to(ROOT), "manifest path escapes root")
        require(checksum(target) == expected, "hash mismatch: " + relative)
        count += 1
    return {"status": "PASS", "files": count}


def verify_compound_coverage():
    # Independent reconstruction of this exact local family, not a trace replay.
    import frozen_support as a
    table = a.read_table((ROOT / "data/zfc_permutation252_old.tm").read_bytes())
    states = sorted({q for q, bit in table})
    protected_targets = {table[k][2] for k in a.BOX_PAIRS}
    eligible = [q for q in states if q != 96 and q not in protected_targets
                and all((q, b) not in a.BOX_PAIRS for b in (0, 1))]
    expected = [(q, r) for q in eligible for r in states if q != r]
    data = json.loads((ROOT / "results/compound_folds.json").read_text())
    rows = data["recipes"]
    require(len(eligible) == 221 and len(expected) == 55471, "wrong fold family")
    require([(x[0], x[1]) for x in rows] == expected, "incomplete/duplicate fold ledger")
    require(all(x[2] is not None for x in rows), "unreported survivor")
    require(data["status"] == "completed" and data["completed"] == 55471,
            "incomplete recorded search")
    require(data["checks"] == 127788 and not data["survivors"], "summary mismatch")
    require(data["driver_sha256"] == checksum(ROOT / "code/compound_fold.py"),
            "portable driver differs from full recorded replay")
    return {"status": "PASS", "recipes": 55471, "trace_replayed": False}


def verify_altered_bootstraps():
    from verify_baseline import parse_table, literal_zipper
    meta = json.loads((ROOT / "data/renumbering.json").read_text())
    expected = meta["blank_prefix"]["all_one_positions"]
    answers = []
    for name in ("prefill255", "direct255"):
        path = ROOT / "data" / (name + ".tm")
        start, table = parse_table(path)
        working = {q for q, bit in table}
        require(len(working) == 255 and len(table) == 510, "wrong altered table size")
        require(254 not in working and start == 64, "wrong label convention")
        require(set(table) == {(q, b) for q in working for b in (0, 1)},
                "incomplete table")
        require(all(t in working | {254} for w, d, t in table.values()),
                "unknown transition target")
        q, head, ones, _, _, _ = literal_zipper(table, start, 82552, 254)
        require((q, head, ones) == (96, 2, expected), "altered bootstrap mismatch")
        answers.append({"table": name, "status": "PASS", "sha256": checksum(path),
                        "steps": 82552, "one_cells": len(ones)})
    return answers


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if not __debug__:
        parser.error("Assertions must be enabled; do not use -O or -OO.")
    began = time.monotonic()
    result = {
        "scope": "Portable executable integration; imported Box contracts assumed; "
                 "no new kernel theorem or sub252 machine; full search traces not all replayed.",
        "python": sys.version.split()[0],
        "manifest": verify_manifest(),
        "compound_coverage": verify_compound_coverage(),
        "altered_bootstraps": verify_altered_bootstraps(),
    }
    print("PASS manifest/recorded fold coverage/exact altered bootstraps", flush=True)
    with tempfile.TemporaryDirectory(prefix="beyond252-check-") as dirname:
        scratch = Path(dirname)
        jobs = [
            ("baseline", "code/verify_baseline.py", []),
            ("semantic-seeds", "code/semantic_seeds.py", ["--audit"]),
            ("negation-macros", "negation/verify.py", []),
            ("prefill255-runtime", "negation/verify_runtime.py",
             ["--output", str(scratch / "prefill.json")]),
            ("fusion252-coverage", "fusion/verify_coverage.py",
             ["--output", str(scratch / "coverage.json")]),
            ("fusion252-phase-replay", "fusion/phase_followup.py",
             ["--output", str(scratch / "phase.json")]),
            ("direct255-runtime", "fusion/verify_runtime.py",
             ["--output", str(scratch / "direct.json")]),
            ("scanner-layout-replay", "exploratory/verify_layouts.py",
             ["--output", str(scratch / "layout.json")]),
        ]
        for cap in (1, 2, 8, 32):
            jobs.append((f"zones-{cap}", "code/verify_zones.py",
                         ["--graph", str(ROOT / "data/program_cases.json"),
                          "--zone", str(ROOT / f"data/zones{cap}.txt")]))
        if (ROOT / "fusion/verify_direct_coverage.py").exists():
            jobs.append(("direct255-fusion-coverage", "fusion/verify_direct_coverage.py",
                         ["--output", str(scratch / "direct-coverage.json")]))

        def run(job):
            name, script, options = job
            t0 = time.monotonic()
            proc = subprocess.run([sys.executable, "-B", str(ROOT / script), *options],
                                  cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                  stderr=subprocess.STDOUT, timeout=300)
            if proc.returncode:
                raise RuntimeError(name + " failed:\n" + proc.stdout[-12000:])
            return {"name": name, "status": "PASS", "script": script,
                    "script_sha256": checksum(ROOT / script),
                    "seconds": round(time.monotonic() - t0, 3),
                    "output_sha256": hashlib.sha256(proc.stdout.encode()).hexdigest()}

        checks = []
        with ThreadPoolExecutor(max_workers=3) as pool:
            futures = {pool.submit(run, job): job[0] for job in jobs}
            for future in as_completed(futures):
                item = future.result()
                checks.append(item)
                print("PASS " + item["name"], flush=True)
        result["checks"] = sorted(checks, key=lambda x: x["name"])
    result.update(status="PASS", seconds=round(time.monotonic() - began, 3))
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "checks"}, indent=2))


if __name__ == "__main__":
    main()
