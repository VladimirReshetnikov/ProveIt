#!/usr/bin/env python3
"""Run the eight focused release modules, without assuming tests is a package."""
import argparse
from datetime import datetime, timezone
import io
import json
import os
from pathlib import Path
import platform
import sys
import time
import unittest

MODULES = (
    "test_core_top_reduction.py",
    "test_core_top_template.py",
    "test_core_forest_exchange.py",
    "test_normal_cut_handlebodies.py",
    "test_core_handlebody.py",
    "test_core_primitive_annuli.py",
    "test_bundle_boundary_kernel.py",
    "test_source_handle_reduction.py",
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fast-dir", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    fast = args.fast_dir.resolve(strict=True)
    args.output_dir = args.output_dir.resolve()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    for relative in (
        "synthesis/data/core-three-handle-probe.json",
        "synthesis/data/handle-reducible-trefoil.json",
        "reports/57/results/discovery_corpus.json",
    ):
        if not (fast.parent / relative).is_file():
            raise FileNotFoundError(
                f"The pinned repository fixture is required: {fast.parent / relative}")
    # Existing CLI regression tests launch `python -m fastunknot` in this cwd.
    os.chdir(fast)
    sys.path.insert(0, str(fast))
    suite = unittest.TestSuite()
    counts = {}
    for filename in MODULES:
        if not (fast / "tests" / filename).is_file():
            raise FileNotFoundError(fast / "tests" / filename)
        tests = unittest.TestLoader().discover(str(fast / "tests"), pattern=filename)
        counts[filename] = tests.countTestCases()
        suite.addTests(tests)
    stream = io.StringIO()
    started = time.perf_counter()
    result = unittest.TextTestRunner(stream=stream, verbosity=2).run(suite)
    elapsed = time.perf_counter() - started
    (args.output_dir / "targeted_tests.txt").write_text(stream.getvalue(), encoding="utf-8")
    report = {
        "scope": "Eight focused modules; not the full repository suite",
        "utc": datetime.now(timezone.utc).isoformat(),
        "python": platform.python_version(),
        "fast_dir": str(fast),
        "module_counts": counts,
        "tests_run": result.testsRun,
        "failures": len(result.failures),
        "errors": len(result.errors),
        "skipped": len(result.skipped),
        "elapsed_seconds": elapsed,
        "successful": result.wasSuccessful(),
    }
    (args.output_dir / "targeted_tests.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    raise SystemExit(main())
