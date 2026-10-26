#!/usr/bin/env python3
"""Replay the delivered Lean checks in an existing ProveIt checkout.

No source patches are applied. Lake may use or create normal build metadata.
Supplementary Sidon checks require the baseline SidonPositions module to be built.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

BUNDLE = Path(__file__).resolve().parents[1]
BASE = "553a5f7a463cbaab8800ff8148fef0bc5a9e1b22"
CLOSING = "e652d21c413de59e4821f6e8e9b6a3a077bf5bfe"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", type=Path, required=True)
    ap.add_argument("--timeout", type=int, default=900)
    ap.add_argument("--include-supplementary", action="store_true")
    ap.add_argument("--output", type=Path, default=BUNDLE / "replay-results")
    args = ap.parse_args()
    repo = args.repo.resolve()
    if not (repo / "lakefile.toml").is_file():
        ap.error("--repo must be the ProveIt repository root")
    commit = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()
    if commit not in (BASE, CLOSING):
        ap.error("Use the report baseline or its recorded closing snapshot")
    expected = json.loads((BUNDLE / "evidence/source-targets.json").read_text())
    for entry in expected["files"]:
        path = repo / entry["path"]
        if not path.is_file() or digest(path) != entry["sha256"]:
            ap.error("Source changed: " + entry["path"])
    files = [
        "arithmetic/lean/IndexSpanFixture.lean",
        "lean/HelixPeriod.lean",
        "lean/GeometricRanges.lean",
        "syntax/ShellPairing.lean",
        "syntax/ListHeadMonotone.lean",
        "syntax/OrderFromMembership.lean",
        "geometry/StripWidthCore.lean",
    ]
    if args.include_supplementary:
        files += ["arithmetic/lean/SidonMomentCheck.lean",
                  "arithmetic/proposed/SidonPositions.lean"]
    args.output.mkdir(parents=True, exist_ok=True)
    results = []
    for index, relative in enumerate(files, 1):
        path = BUNDLE / relative
        if not path.is_file():
            results.append({"file": relative, "status": "missing"})
            print("MISSING", relative, flush=True)
            continue
        command = ["lake", "env", "lean", "-j1", str(path)]
        start = time.monotonic()
        try:
            run = subprocess.run(command, cwd=repo, text=True,
                                 stdout=subprocess.PIPE,
                                 stderr=subprocess.STDOUT,
                                 timeout=args.timeout)
            log = run.stdout
            passed = run.returncode == 0 and "sorryAx" not in log
            item = {"file": relative, "exit_code": run.returncode,
                    "status": "passed" if passed else "failed"}
        except subprocess.TimeoutExpired as error:
            log = error.stdout or ""
            if isinstance(log, bytes):
                log = log.decode("utf-8", "replace")
            item = {"file": relative, "status": "timeout"}
        log_path = args.output / f"{index:02d}-{path.stem}.log"
        log_path.write_text(log)
        item.update(source_sha256=digest(path), log_sha256=digest(log_path),
                    wall_seconds=round(time.monotonic() - start, 3))
        results.append(item)
        print(item["status"].upper(), relative, flush=True)
    output = {"source_commit": commit, "results": results,
              "note": "Wall times are observations, not performance claims."}
    (args.output / "results.json").write_text(json.dumps(output, indent=2) + "\n")
    return 0 if all(x["status"] == "passed" for x in results) else 1


if __name__ == "__main__":
    sys.exit(main())
