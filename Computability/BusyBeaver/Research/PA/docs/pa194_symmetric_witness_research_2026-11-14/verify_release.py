#!/usr/bin/env python3
"""Offline integrity, complete machine replay, and exact novelty verification."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
NAMES = ("PA194H5XS", "PA194JH5XS")
WITNESS_SHA256 = "cc51ef4f2858e37cc72c5079bb6f8b0d86ce0ed9eae1aed428c1bd69baffb4cc"


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, required=True)
    args = parser.parse_args()
    require(__debug__ and not sys.flags.optimize, "Run with Python assertions enabled.")
    work = args.work.resolve()
    require(not work.exists(), "Choose a fresh nonexistent work directory.")
    require(work != ROOT and ROOT not in work.parents, "Put replay output outside the release.")
    checks = []
    manifest = ROOT / "SHA256SUMS"
    count = 0
    for line in manifest.read_text().splitlines():
        digest, relative = line.split("  ", 1)
        path = (ROOT / relative).resolve()
        require(ROOT in path.parents and path.is_file(), "Invalid manifest path: " + relative)
        require(sha(path) == digest, "Integrity mismatch: " + relative)
        count += 1
    checks.append(dict(check="release_integrity", status="PASS", files=count))
    print("release integrity PASS:", count, "files", flush=True)
    witness = ROOT / "references/pa194_witness_research_2026-11-15.zip"
    require(sha(witness) == WITNESS_SHA256, "Imported witness archive mismatch.")
    for name in NAMES:
        require((ROOT / "machines" / name / "machine.tm").read_bytes() ==
                (ROOT / "comparison/candidates" / (name + ".tm")).read_bytes(),
                "Novelty candidate is not the delivered machine: " + name)
    checks.append(dict(check="reference_and_candidate_binding", status="PASS"))
    print("reference and candidate binding PASS", flush=True)

    work.mkdir(parents=True)
    environment = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")

    def run(label, command):
        start = time.monotonic()
        log = work / (label + ".log")
        with log.open("w") as stream:
            result = subprocess.run([sys.executable, "-B", *map(str, command)],
                                    cwd=ROOT, env=environment, stdout=stream,
                                    stderr=subprocess.STDOUT)
        require(result.returncode == 0, label + " failed; see " + str(log))
        checks.append(dict(check=label, status="PASS", seconds=time.monotonic()-start))
        print(label, "PASS", flush=True)

    run("machines", [ROOT / "verify.py", "--work", work / "machine-replay"])
    run("novelty", [ROOT / "comparison/verify_novelty.py", "--output", work / "novelty.json"])
    receipt = {
        "status": "PASS",
        "source_commit": "3c3bf00e3132d31d328a7bcfe79761ef238eced3",
        "checks": checks,
        "machines": {name: sha(ROOT / "machines" / name / "machine.tm") for name in NAMES},
        "scope": "Integrity, construction, full symbolic source/physical checks and exact graph novelty. The absolute iPRA calibration is an attributed written mathematical theorem; this is not proof-kernel verification. Bounded discovery searches are retained separately.",
    }
    (work / "verification.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
