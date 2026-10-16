#!/usr/bin/env python3
"""Finite, offline reproduction of the accompanying research artifacts.

No unbounded proof search, network request, dependency installation, or
implicit proof-assistant invocation occurs. Use Python without -O.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def manifest_check():
    manifest = json.loads((ROOT / "MANIFEST.json").read_text())
    for name, expected in manifest["files"].items():
        path = ROOT / name
        if not path.is_file():
            raise ValueError("missing distributed file: " + name)
        if path.stat().st_size != expected["bytes"] or digest(path) != expected["sha256"]:
            raise ValueError("distributed file changed: " + name)
    return len(manifest["files"])


def execute(args):
    env = dict(os.environ)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    result = subprocess.run(
        [sys.executable, "-B", *map(str, args)],
        cwd=ROOT, env=env, text=True, capture_output=True, check=False,
    )
    if result.returncode:
        raise RuntimeError(
            "finite check failed: " + str(args[0]) + "\n"
            + result.stdout + result.stderr
        )
    return result


def run_json(script, output, *args):
    execute([ROOT / script, *args, "--output", output])
    return json.loads(output.read_text())


def compare_result(actual, reference):
    expected = json.loads((ROOT / reference).read_text())
    if actual != expected:
        raise AssertionError("finite result differs from saved evidence: " + reference)


def check_table(name, count):
    path = ROOT / name
    transitions = {}
    for line in path.read_text().splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        fields = line.split()
        if len(fields) != 5:
            raise ValueError("malformed transition in " + name)
        q, read, write, move, target = fields
        q, read, write, target = map(int, (q, read, write, target))
        if not (0 <= q < count and read in (0, 1) and write in (0, 1)
                and move in ("L", "R") and 0 <= target <= count):
            raise ValueError("invalid transition convention in " + name)
        if (q, read) in transitions:
            raise ValueError("duplicate transition in " + name)
        transitions[q, read] = (write, move, target)
    expected = {(q, bit) for q in range(count) for bit in (0, 1)}
    if set(transitions) != expected:
        raise ValueError("table is not complete for its declared working states: " + name)
    if not any(target == count for _, _, target in transitions.values()):
        raise ValueError("no transition to declared terminal label: " + name)
    if "#! start 0" not in path.read_text().splitlines():
        raise ValueError("start convention missing: " + name)
    return {"working_states": count, "rows": len(transitions),
            "start": 0, "blank": 0, "terminal": count, "sha256": digest(path),
            "scope": "static table completeness, not an execution or simulation proof"}


def optional_repository_audit(repo, temporary):
    repo = repo.resolve()
    expected_commit = "96836f9eea3540e96322c3d28c7127a582aae223"
    actual = subprocess.check_output(
        ["git", "-C", str(repo), "rev-parse", "HEAD"], text=True
    ).strip()
    if actual != expected_commit:
        raise ValueError("optional source audit requires pinned ProveIt HEAD")
    expected = json.loads((ROOT / "results/psc-identity-obstruction.json").read_text())
    source_dir = repo / "Computability/BusyBeaver/Research/ZFC"
    for name, sha in expected["source_sha256"].items():
        if digest(source_dir / name) != sha:
            raise ValueError("pinned source file changed: " + name)
    actual = run_json(
        "code/psc_identity_obstruction_check.py", temporary / "psc-source.json",
        "--repo", repo, "--limit", "100000",
    )
    compare_result(actual, "results/psc-identity-obstruction.json")
    return actual


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="write an additional JSON summary")
    parser.add_argument("--repo", type=Path, help="also inspect the exact pinned ProveIt source")
    args = parser.parse_args()
    if not __debug__:
        raise RuntimeError("Do not use Python -O; regression programs use assertions.")
    checked_files = manifest_check()
    print("Distributed file hashes: OK")
    with tempfile.TemporaryDirectory(prefix="zfc-research-reproduction-") as temporary:
        temp = Path(temporary)
        kernel = run_json("code/test_binder_kernel.py", temp / "kernel.json")
        compare_result(kernel, "results/binder-kernel.json")
        print("Binding semantics, PSC adapter, malformed inputs, deep syntax: OK")
        wire = run_json("code/test_binder_wire.py", temp / "wire.json")
        compare_result(wire, "results/binder-wire.json")
        print("Strict binary grammar, roundtrips, truncations, finite census: OK")
        audit = run_json("audit_artifacts/binder_independent_audit.py", temp / "audit.json")
        compare_result(audit, "audit_artifacts/binder_independent_audit.json")
        print("Independent implementation audit: OK")
        rm = run_json("compiler/recheck_included_certificate.py", temp / "rm.json", "--self-test")
        print("Independent 4,533-pair register-program certificate and negative control: OK")
        tables = {
            name: check_table(name, count)
            for name, count in [
                ("machines/benchmark-zfc-253.tm", 253),
                ("machines/raw-candidate-old_rho6-248.tm", 248),
                ("machines/raw-candidate-dual_rho6-248.tm", 248),
                ("compiler/original-269.tm", 269),
                ("compiler/psc_ir-283.tm", 283),
            ]
        }
        print("Five complete numeric machine tables: OK")
        evidence = {
            "scope": "finite reproduction; no consistency or end-to-end TM claim",
            "success": True, "manifest_files_verified": checked_files,
            "binder_kernel": kernel, "binary_codec": wire,
            "independent_audit": audit, "register_certificate": rm,
            "tables": tables, "lean_automatically_invoked": False,
            "network_used": False, "unbounded_search_run": False,
        }
        if args.repo:
            evidence["actual_source_obstruction_audit"] = optional_repository_audit(args.repo, temp)
            print("Pinned actual-template obstruction audit: OK")
        if args.output:
            args.output.write_text(json.dumps(evidence, indent=2) + "\n")
    print("All requested finite checks passed. See formal/ and results/ for separate Lean proofs.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
