#!/usr/bin/env python3
"""Verify the complete PA194NS release without modifying its delivered files.

Default: integrity, reconstruction, command algebra, novelty, both symbolic
physical checks, complete startup, and exact receipt binding.
--quick omits the two symbolic physical replays; it is not a full proof replay.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    if not __debug__ or sys.flags.optimize:
        raise RuntimeError("Assertions must be enabled; do not use Python -O.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--work", type=Path)
    args = parser.parse_args()
    manifest = json.loads((ROOT / "MANIFEST.json").read_text())
    for relative, expected in manifest["files"].items():
        if digest(ROOT / relative) != expected:
            raise AssertionError("Release integrity failure: " + relative)
    print("Release integrity: PASS", len(manifest["files"]), "files", flush=True)
    if args.work:
        args.work.mkdir(parents=True, exist_ok=False)
        work = args.work.resolve()
    else:
        work = Path(tempfile.mkdtemp(prefix="pa194ns-release-check-"))

    def run(script, *parameters):
        subprocess.run([sys.executable, "-B", str(ROOT / script),
                        *map(str, parameters)], check=True)

    run("proof/check_commands.py", "--output", work / "commands.json")
    parameters = ["--output", work / "construction"]
    if args.quick:
        parameters.append("--quick")
    run("construction/build.py", *parameters)
    for name in ("machine.tm", "machine.native.tm", "raw.native.tm",
                 "sites.json", "instructions.json", "folds.json", "labels.json"):
        if (work / "construction" / name).read_bytes() != (ROOT / "machine" / name).read_bytes():
            raise AssertionError("Reconstructed artifact differs: " + name)
    run("comparison/check_novelty.py", ROOT / "machine/machine.tm",
        "--output", work / "novelty.json")
    novelty = json.loads((work / "novelty.json").read_text())
    assert novelty["result"] == "NOVEL" and not novelty["matches"]
    assert novelty["prior_table_byte_forms"] == 51
    assert novelty["prior_action_graph_classes"] == 28
    if not args.quick:
        run("verification/check.py", "--output", work / "independent")
        fresh = json.loads((work / "independent/receipt.json").read_text())
        prior = json.loads((ROOT / "verification/recorded/receipt.json").read_text())
        for key, value in prior.items():
            if key != "elapsed_seconds":
                assert fresh[key] == value, key
        assert (work / "independent/contracts.json").read_bytes() == (ROOT / "verification/recorded/contracts.json").read_bytes()
    result = {"status": "PASS", "mode": "quick" if args.quick else "full",
              "integrity_files": len(manifest["files"]),
              "both_symbolic_physical_replays": not args.quick,
              "literal_machine_and_source_identical": True,
              "new_graph_in_pinned_corpus": True,
              "fresh_evidence": str(work), "kernel_checked": False}
    (work / "release_receipt.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2), flush=True)


if __name__ == "__main__":
    main()
