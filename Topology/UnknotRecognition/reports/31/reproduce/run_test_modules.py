"""Run every maintained test module with unmodified standard unittest semantics.

This records module batches explicitly; it does not label them a successful
single-process discovery run. Existing subprocess deadlines are not changed.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
from hashlib import sha256
import importlib.metadata
import json
from pathlib import Path
import platform
import re
import subprocess
import sys
from time import perf_counter


def now():
    return datetime.now(timezone.utc).isoformat()


def hashes(fast):
    return {
        str(path.relative_to(fast)): sha256(path.read_bytes()).hexdigest()
        for folder in ("fastunknot", "tests")
        for path in sorted((fast / folder).rglob("*.py"))
    }


def summary(output, code):
    counts = re.findall(r"Ran (\d+) tests? in ([0-9.]+)s", output)
    verdicts = re.findall(r"^(OK(?: \(.*\))?|FAILED \(.*\))$", output, re.M)
    result = {"exit_code": code, "status": verdicts[-1] if verdicts else "NO SUMMARY"}
    if counts:
        result.update(tests_run=int(counts[-1][0]), reported_seconds=float(counts[-1][1]))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fast", type=Path, default=Path.cwd())
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    fast, output = args.fast.resolve(), args.output.resolve()
    modules = sorted((fast / "tests").glob("test_*.py"))
    if not modules or not (fast / "fastunknot").is_dir():
        parser.error("--fast must be the maintained fast/ directory")
    logs = output / "module-logs"
    logs.mkdir(parents=True, exist_ok=True)
    try:
        regina = importlib.metadata.version("regina")
    except importlib.metadata.PackageNotFoundError:
        regina = None
    record = {
        "schema": "fastunknot.unittest-module-batches.v1",
        "scope": "All maintained test modules, each in its own standard unittest process",
        "fast": str(fast), "python": sys.version, "executable": sys.executable,
        "platform": platform.platform(), "regina_distribution_version": regina,
        "started_utc": now(), "planned_modules": [path.name for path in modules],
        "source_hashes_at_start": hashes(fast), "modules": [], "status": "RUNNING",
    }
    inventory_command = [sys.executable, "-B", "-c",
        "import unittest; print(unittest.defaultTestLoader.discover('tests').countTestCases())"]
    inventory = subprocess.run(inventory_command, cwd=fast, text=True,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (output / "test-inventory.log").write_text(inventory.stdout)
    record["inventory_command"] = inventory_command
    record["inventory_exit_code"] = inventory.returncode
    record["inventory_test_count"] = (
        int(inventory.stdout.strip())
        if inventory.returncode == 0 and inventory.stdout.strip().isdigit() else None
    )
    target = output / "full-suite-modules.json"

    def save():
        target.write_text(json.dumps(record, indent=2) + "\n")

    save()
    for path in modules:
        command = [sys.executable, "-B", "-m", "unittest", "discover",
                   "-s", "tests", "-p", path.name, "-v"]
        started, clock = now(), perf_counter()
        result = subprocess.run(command, cwd=fast, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log_name = path.stem + ".log"
        (logs / log_name).write_text(result.stdout)
        entry = {"module": path.name, "command": command, "started_utc": started,
                 "wall_seconds": perf_counter() - clock, "log": "module-logs/" + log_name,
                 **summary(result.stdout, result.returncode)}
        record["modules"].append(entry)
        save()
        print(json.dumps({key: entry.get(key) for key in
                          ("module", "status", "tests_run", "exit_code", "wall_seconds")}),
              flush=True)
    record["finished_utc"] = now()
    record["source_hashes_at_end"] = hashes(fast)
    first, last = record["source_hashes_at_start"], record["source_hashes_at_end"]
    record["source_files_changed_during_run"] = [
        path for path in sorted(set(first) | set(last)) if first.get(path) != last.get(path)
    ]
    record["tests_run"] = sum(entry.get("tests_run", 0) for entry in record["modules"])
    complete = (len(record["modules"]) == len(modules)
                and record["tests_run"] == record["inventory_test_count"])
    passed = all(entry["exit_code"] == 0 and entry["status"].startswith("OK")
                 for entry in record["modules"])
    record["status"] = ("ALL_TEST_MODULES_PASSED" if complete and passed
                         else "MODULE_BATCHES_REQUIRE_REVIEW")
    save()
    print(json.dumps({key: record[key] for key in
                      ("status", "tests_run", "inventory_test_count",
                       "source_files_changed_during_run")}), flush=True)
    return 0 if complete and passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
