#!/usr/bin/env python3
"""Run the recorded complete test-module partition in fresh interpreters.

The default only lists the six commands and verifies the test-source digests.
Use --run to execute them, preserving new logs under reproduced/regression/.
The original recorded results are never replaced.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", action="store_true")
    parser.add_argument("--fast-source", type=Path, default=ROOT / "repro/fast")
    parser.add_argument("--output-dir", type=Path,
                        default=ROOT / "reproduced/regression")
    args = parser.parse_args()
    fast = args.fast_source.resolve()
    record = json.loads((ROOT / "provenance/full_tests.json").read_text())
    inventory = json.loads((ROOT / "provenance/full_tests_inventory.json").read_text())
    for item in inventory["module_inventory"]:
        path = fast / item["path"]
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != item["sha256"]:
            parser.error("test-source mismatch: " + str(path))
    modules = [name for batch in record["batches"] for name in batch["modules"]]
    expected = {item["module"] for item in inventory["module_inventory"]}
    assert len(modules) == len(set(modules)) == len(expected)
    assert set(modules) == expected
    results = []
    for batch in record["batches"]:
        command = [sys.executable, "-X", "faulthandler", "-m", "unittest",
                   *["tests." + name for name in batch["modules"]], "-v"]
        result = dict(batch=batch["batch"], modules=len(batch["modules"]),
                      expected_tests=batch["tests_loaded"], command=command)
        if args.run:
            args.output_dir.mkdir(parents=True, exist_ok=True)
            log_path = args.output_dir / ("batch_%d.log" % batch["batch"])
            started = time.perf_counter()
            with log_path.open("w") as log:
                process = subprocess.run(command, cwd=fast, stdout=log,
                                         stderr=subprocess.STDOUT)
            result.update(exit_code=process.returncode,
                          elapsed_seconds=time.perf_counter()-started,
                          log=str(log_path))
            print("Batch %d: exit %d" % (batch["batch"], process.returncode),
                  flush=True)
        results.append(result)
    summary = dict(mode="run" if args.run else "list",
                   modules=len(modules),
                   recorded_tests=record["tests_run"], batches=results)
    print(json.dumps(summary, indent=2))
    if args.run:
        (args.output_dir / "summary.json").write_text(json.dumps(summary, indent=2)+"\n")
    return int(any(r.get("exit_code", 0) for r in results))


if __name__ == "__main__":
    raise SystemExit(main())
