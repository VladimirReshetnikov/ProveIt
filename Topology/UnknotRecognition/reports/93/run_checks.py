#!/usr/bin/env python3
"""Run the delivered tests against the pinned, bundled native source."""

import argparse
import json
from pathlib import Path
import platform
import sys
import time
import unittest


ROOT = Path(__file__).resolve().parent
sys.path[:0] = [str(ROOT / "code"), str(ROOT / "native_snapshot")]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pattern", default="test_*.py")
    args = parser.parse_args()
    (ROOT / "results").mkdir(exist_ok=True)
    suite = unittest.defaultTestLoader.discover(str(ROOT / "tests"), pattern=args.pattern)
    started = time.perf_counter()
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    elapsed = time.perf_counter() - started
    try:
        import regina
        regina_version = regina.versionString()
    except ImportError:
        regina_version = None
    summary = dict(python=sys.version, platform=platform.platform(),
                   regina=regina_version, tests=result.testsRun,
                   failures=len(result.failures), errors=len(result.errors),
                   skipped=len(result.skipped), elapsed_seconds=elapsed,
                   success=result.wasSuccessful(), pattern=args.pattern)
    name = "validation_summary.json" if args.pattern == "test_*.py" else "focused_validation_summary.json"
    (ROOT / "results" / name).write_text(json.dumps(summary, indent=2) + "\n")
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    raise SystemExit(main())
