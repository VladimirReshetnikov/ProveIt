#!/usr/bin/env python3
"""Export an upper certificate, kernel-check its theorem, and audit its axioms."""

import argparse
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from common import ROOT, build_modules, directory_lock, run, source_snapshot, worker_count
from exact import inputs
from export import SHARD_SIZE, export

NS = "MoserWorm.UpperBound.Certificate"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificates", type=Path, default=ROOT / "certificates/upper")
    parser.add_argument(
        "--jobs", type=int, default=None, help="maximum workers (default: auto; cap: 12)"
    )
    args = parser.parse_args()
    if args.jobs is not None and args.jobs < 1:
        parser.error("jobs must be positive")
    jobs = worker_count(args.jobs, 12, 7 * 2**30)
    certificates = args.certificates.resolve()
    directory = (ROOT / "MoserWorm/UpperBound/Certificate/Generated").resolve()
    if certificates.is_relative_to(directory) or directory.is_relative_to(certificates):
        parser.error("certificate and generated-source directories must be disjoint")
    logs = ROOT / ".lake/logs/upper"
    with directory_lock(certificates), directory_lock(directory):
        print(f"Upper verification: checking certificate files; logs: {logs}", flush=True)
        sources = source_snapshot()
        snapshot, header, _ = inputs(certificates)
        if header["complete"] is not True:
            raise ValueError("upper certificate is incomplete")
        run(
            "soundness",
            ["lake", "build", NS + ".Kernel.Header", NS + ".Extraction", NS + ".GeometricSound"],
            logs,
        )
        print("Upper verification: exporting Lean proofs...", flush=True)
        manifest = export(certificates, directory)
        if manifest.get("complete") is not True:
            raise ValueError("generated upper certificate is incomplete")
        if manifest.get("inputs") != snapshot or manifest.get("shard_size") != SHARD_SIZE:
            raise ValueError("generated manifest does not match this run's inputs")
        build_modules(manifest["modules"], jobs, logs)
        run("theorem", ["lake", "--rehash", "build", "MoserWorm.UpperBound.Main"], logs)
        if source_snapshot() != sources:
            raise ValueError("sources changed during verification")
        if inputs(certificates)[0] != snapshot:
            raise ValueError("upper certificates changed during verification")
    print(f"Upper bound checked. Logs: {logs}")


if __name__ == "__main__":
    main()
