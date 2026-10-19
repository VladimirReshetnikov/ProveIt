#!/usr/bin/env python3
"""Reproduce the delivered 236-state checks on private working copies.

Default: manifest, source, construction, all-tape fold, canonical startup,
and exact equational packet checks. --full adds the quantified runtime.
Python 3.10+ standard library only. Run without -O or -OO.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_manifest():
    checked = []
    for line in (ROOT / "MANIFEST.sha256").read_text().splitlines():
        digest, name = line.split("  ", 1)
        path = (ROOT / name).resolve()
        if not path.is_relative_to(ROOT) or not path.is_file():
            raise RuntimeError("Invalid or missing manifest path: " + name)
        if sha(path) != digest:
            raise RuntimeError("Manifest mismatch: " + name)
        checked.append(name)
    if len(checked) != len(set(checked)):
        raise RuntimeError("Duplicate manifest entry")
    return len(checked)


def bindings():
    groups = [
        ["candidate236/ingredients/composed237_old.tm", "source/baseline237_old.tm"],
        ["candidate236/ingredients/reassociated237_old.tm", "source/rotated237_old.tm"],
        ["candidate236/sites_logical.json", "source/rotated_sites.json"],
        ["source/baseline_sites.json", "provenance/source103/boundary224_sites.json"],
    ]
    for group in groups:
        if len({sha(ROOT / path) for path in group}) != 1:
            raise RuntimeError("Cross-file identity failed: " + repr(group))
    pins = {
        "candidate236/zfc_reassociate236.tm":
            "d4302309401891d68b93c393e4ad6e24d2abf993dede4a61baa2d3e0c1c53c8e",
        "candidate236/zfc_reassociate236_old.tm":
            "ff059535876bc9e1e1e63174ebfd1c10a91c1a818ba0c3f8c4ef2ac51a3cfcc3",
        "candidate236/sites_logical.json":
            "1ebe9691507b2d3236951a31d6b9a7ef548a2cdf90525cd57051992f8ac2626f",
        "provenance/source103/baseline_sites.json":
            "74b1e7f73cc3ffe7761e36ab2d57a26e0ba34d3ac624f2472799e6ac41d5a51d",
    }
    for path, digest in pins.items():
        if sha(ROOT / path) != digest:
            raise RuntimeError("Pinned input changed: " + path)
    r = json.loads((ROOT / "evidence/runtime236.json").read_text())
    if r["status"] != "UNIVERSAL_MATHEMATICAL_PASS":
        raise RuntimeError("No accepted final runtime receipt")
    for key, path in [
        ("table_sha256", "candidate236/zfc_reassociate236_old.tm"),
        ("sites_sha256", "candidate236/sites_logical.json"),
        ("checker_sha256", "verification/check236_runtime.py"),
        ("engine_sha256", "verification/symbolic_runtime.py"),
        ("helper_sha256", "verification/independent_runtime.py"),
    ]:
        if r[key] != sha(ROOT / path):
            raise RuntimeError("Runtime receipt binding mismatch: " + key)
    if (r["working_states"], r["transition_rows"], r["cases"],
        r["symbolic_steps"], len(r["directly_used_rows"])) != (236, 472, 8386, 2267815, 472):
        raise RuntimeError("Unexpected final runtime census")
    return {"cross_file_groups": groups, "exact_pins": pins, "runtime_receipt_bound": True}


def work(out, full, manifest_count, binding_report):
    started = time.monotonic()
    copied = out / "work"
    for name in ["candidate236", "source", "equational", "verification", "provenance"]:
        shutil.copytree(ROOT / name, copied / name,
                        ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
    commands = []

    def run(name, script, *arguments):
        command = [sys.executable, "-B", str(copied / script), *map(str, arguments)]
        print("Checking " + name + "...", flush=True)
        log = out / (name + ".log")
        t = time.monotonic()
        with log.open("w") as stream:
            result = subprocess.run(command, cwd=copied, stdout=stream,
                                    stderr=subprocess.STDOUT, check=False)
        commands.append({"check": name, "command": command,
                         "returncode": result.returncode,
                         "seconds": time.monotonic() - t, "log": log.name})
        if result.returncode:
            print(log.read_text(), file=sys.stderr)
            raise RuntimeError("Check failed: " + name)
        print("PASS " + name, flush=True)

    run("source103", "source/check_rotation_certificate.py",
        "--baseline", copied / "provenance/source103/baseline_sites.json",
        "--certificate", copied / "provenance/source103/rotation_certificate.json",
        "--candidate", copied / "provenance/source103/boundary224_sites.json",
        "--report", out / "source103.json")
    run("new_source", "source/build_and_check_source.py")
    run("literal_build", "candidate236/build236.py")
    run("local_fold", "candidate236/check_local_fold.py")
    run("canonical_and_blank_startup", "candidate236/check_canonical_boot.py")
    run("equational667_663", "equational/build_e667.py",
        "--output", out / "equational667_663")
    run("equational639", "equational/build_e639.py",
        "--output", out / "equational639")

    # Compare every exact syntax/transport checkpoint, not elapsed-time metadata.
    for names, fresh in [
        (["E667", "E663"], out / "equational667_663"),
        (["E668", "E643", "E639"], out / "equational639"),
    ]:
        for name in names:
            for ext in [".bits", ".bin", ".bitlength", ".equations", ".json"]:
                relative = "equational/generated/" + name + ext
                if sha(fresh / (name + ext)) != sha(ROOT / relative):
                    raise RuntimeError("Equational reconstruction mismatch: " + relative)
    print("PASS all five exact equational checkpoint files", flush=True)

    if full:
        run("runtime236", "verification/check236_runtime.py",
            "--table", copied / "candidate236/zfc_reassociate236_old.tm",
            "--sites", copied / "candidate236/sites_logical.json",
            "--states", "236", "--output", out / "runtime236.json")
        fresh = json.loads((out / "runtime236.json").read_text())
        original = json.loads((ROOT / "evidence/runtime236.json").read_text())
        for key in original:
            if key != "seconds" and fresh[key] != original[key]:
                raise RuntimeError("Full runtime receipt changed: " + key)
        if sha(out / "runtime236_cases.json") != sha(ROOT / "evidence/runtime236_cases.json"):
            raise RuntimeError("Per-case symbolic certificates changed")
    report = {
        "status": "FULL_REPLAY_PASS" if full else "QUICK_REPLAY_PASS",
        "manifest_files_checked": manifest_count,
        "bindings": binding_report, "commands": commands,
        "symbolic_runtime_repeated": full,
        "seconds": time.monotonic() - started,
        "scope": "Executable finite-premise and symbolic induction checks; inherited source calibration remains explicit. No new proof-assistant endpoint.",
    }
    (out / "replay_receipt.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in
                     ["status", "manifest_files_checked", "symbolic_runtime_repeated", "seconds"]},
                    indent=2), flush=True)


def main():
    if not __debug__ or sys.flags.optimize:
        raise SystemExit("Run without -O/-OO: verification assertions are required.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--full", action="store_true")
    parser.add_argument("--output", type=Path,
                        help="new directory for copies, logs, and fresh receipts")
    args = parser.parse_args()
    count = check_manifest()
    binding_report = bindings()
    if args.output:
        out = args.output.resolve()
        out.mkdir(parents=True, exist_ok=False)
        work(out, args.full, count, binding_report)
        print("Fresh replay artifacts: " + str(out))
    else:
        with tempfile.TemporaryDirectory(prefix="zfc236-replay-") as tmp:
            work(Path(tmp), args.full, count, binding_report)


if __name__ == "__main__":
    main()
