#!/usr/bin/env python3
"""Offline replay of the research packet, with exact frozen-output comparisons.

Run without -O. All computations use Python's standard library. Generated
outputs go to a new directory; the delivered certificates remain unchanged.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent
VENDOR = ROOT / "vendor/ProveIt"
ZFC = VENDOR / "Computability/BusyBeaver/Research/ZFC"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path):
    return json.loads(path.read_text())


def verify_manifest() -> int:
    manifest = ROOT / "MANIFEST.sha256"
    if not manifest.is_file():
        raise SystemExit("MANIFEST.sha256 is missing")
    count = 0
    for line in manifest.read_text().splitlines():
        digest, relative = line.split("  ", 1)
        path = (ROOT / relative).resolve()
        assert ROOT in path.parents, ("unsafe manifest path", relative)
        assert path.is_file() and sha(path) == digest, ("digest mismatch", relative)
        count += 1
    return count


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path,
                        help="new or empty directory for generated results; default is a new /tmp directory")
    parser.add_argument("--verify-only", action="store_true",
                        help="verify the delivered manifest without replaying computations")
    args = parser.parse_args()
    if not __debug__:
        parser.error("Assertions are required; do not use Python -O")
    if sys.version_info < (3, 10):
        parser.error("Python 3.10 or newer is required")
    files = verify_manifest()
    print(f"PASS manifest: {files} files", flush=True)
    if args.verify_only:
        return

    work = args.output_dir.resolve() if args.output_dir else Path(tempfile.mkdtemp(prefix="zfc-sub252-replay-"))
    if work == ROOT or ROOT in work.parents:
        parser.error("Use an output directory outside the delivered packet")
    if work.exists() and any(work.iterdir()):
        parser.error("Output directory must be new or empty")
    work.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    records = []
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")

    def run(label: str, script: Path, *extra) -> None:
        print(f"RUN {label}", flush=True)
        command = [sys.executable, str(script), *map(str, extra)]
        t = time.monotonic()
        log = work / (label + ".log")
        with log.open("w") as stream:
            completed = subprocess.run(command, cwd=ROOT, env=env, stdout=stream,
                                       stderr=subprocess.STDOUT, timeout=600)
        if completed.returncode:
            print(log.read_text()[-6000:], file=sys.stderr)
            raise RuntimeError(f"{label} failed; see {log}")
        records.append({"name": label, "status": "PASS", "seconds": time.monotonic()-t,
                        "log": log.name})

    baseline = work / "baseline-audit.json"
    run("baseline", ZFC / "candidate252_independent_audit.py", "--repo", VENDOR,
        "--source-table", ZFC / "candidate-permutation252/zfc_permutation252_old.tm",
        "--scratch", work / "baseline-scratch", "--output", baseline)
    b = read(baseline)
    assert b["status"] == "all_finite_checks_passed"
    assert (b["working_states"], b["total_rows"], b["literal_boot_steps"]) == (252, 504, 82552)
    assert b["affine_audit"]["passed_cases"] == 8391
    assert b["frame"]["all_other_cells_zero"] and b["frame"]["logical_primary"] == [0]*9

    seeds = work / "foundation-seed-evidence.json"
    run("foundation-seeds", ROOT / "research/logical_reduction/foundation_seed254.py",
        "--limit", 65536, "--upstream-seed", ZFC / "safe_seed254.py", "--output", seeds)
    assert read(seeds) == read(ROOT / "research/logical_reduction/foundation-seed-evidence.json")
    hf = work / "hf-embedding-audit.json"
    run("hf-embedding", ROOT / "research/proof_audit/verify_hf_embedding.py",
        "--max-vertices", 4, "--output", hf)
    assert read(hf) == read(ROOT / "research/proof_audit/hf-embedding-audit.json")

    machine = work / "machine_reduction"
    shutil.copytree(ROOT / "research/machine_reduction", machine,
                    ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
    # The nested wrapper compares all seven core JSON/table byte hashes with
    # its frozen manifest. Recomputing masks changes timing metadata only.
    run("machine-controls", machine / "replay.py", VENDOR, "--recompute-masks")
    assert read(machine / "value-analysis-32.json")["values"] == read(
        ROOT / "research/machine_reduction/value-analysis-32.json")["values"]
    audit = ROOT / "research/proof_audit"
    role = work / "role-input-audit.json"
    run("role-inputs", audit / "audit_role_inputs.py", "--candidate-dir", machine, "--output", role)
    role_data = read(role)
    assert role_data["mask_transfer_inclusions_checked"] == 8384
    assert (role_data["move_occurrences"], role_data["accepted_zero_destination_moves"]) == (972, 970)
    expected_role = read(audit / "role-input-audit.json")
    # The mask file has freshly measured elapsed time. Compare the actual
    # assertions and all macro records, ignoring only source-byte digests.
    assert {k:v for k,v in role_data.items() if k != "source_sha256"} == {
        k:v for k,v in expected_role.items() if k != "source_sha256"}
    epsilon = work / "epsilon-progress-audit.json"
    run("epsilon-progress", audit / "epsilon_progress_audit.py",
        machine / "allocation-certificate.json", "--output", epsilon)
    assert read(epsilon) == read(audit / "epsilon-progress-audit.json")
    compacted = work / "compacted-control-audit.json"
    run("compacted-control", audit / "audit_compacted_control.py",
        machine / "allocated-dag.json", machine / "allocated-dag-compacted.json",
        "--output", compacted)
    assert read(compacted) == read(audit / "compacted-control-audit.json")

    # Check the saved partial search's accounting without rerunning its
    # wall-clock-bounded search or treating rejection as impossibility.
    search = read(ROOT / "research/joint_actions/joint-actions-degree2-v2.json")
    assert search["planned"] == 46*1004**2 == 46368736
    assert search["pruned"] == 2825507 and search["remaining"] == 43543229
    assert search["survivors"] == []
    assert search["planned"] == search["pruned"] + search["remaining"]
    assert sum(g["planned"] for g in search["groups"]) == search["planned"]
    assert sum(g["pruned"] for g in search["groups"]) == search["pruned"]
    assert sha(ROOT / "research/joint_actions/search_joint_actions.py") == search["script_sha256"]

    controls = read(machine / "frozen/complete-table-controls.json")["results"]
    assert [c["evidence"]["working_states"] for c in controls] == [314, 888]
    result = {
        "status": "PASS offline packet replay",
        "scope": "Executable finite audits and exact frozen artifact reproduction; no new kernel run or sub-252 endpoint",
        "python": platform.python_version(),
        "manifest_files_verified": files,
        "stages": records,
        "baseline": {"states": 252, "conditional_cases": 8391, "literal_blank_steps": 82552},
        "semantic_seed_counts": {"formulas": 13962, "stacks": 4082, "additional_formulas": 446, "additional_stacks": 31},
        "allocation": {"edges": 5480, "erased_transfers": 598, "retained_transfers": 372,
                       "epsilon_cycles": 0, "longest_epsilon_chain": 4},
        "complete_control_states": [314, 888],
        "joint_search_accounting_checked": True,
        "elapsed_seconds": time.monotonic()-started,
    }
    destination = work / "reproduction.json"
    destination.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))
    print(f"Evidence: {destination}")


if __name__ == "__main__":
    main()
