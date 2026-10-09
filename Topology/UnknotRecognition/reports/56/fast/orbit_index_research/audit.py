"""Run the independent graph/minimum audit and retain machine-readable evidence."""

import argparse
from contextlib import redirect_stdout
import hashlib
import io
import json
from pathlib import Path
import sys
import time
import unittest

FAST_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(FAST_ROOT))
from orbit_index_research.benchmark import source_manifest


def manifest():
    result = source_manifest()
    result['orbit_index_research/audit.py'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path,
                        default=FAST_ROOT / 'results' / 'orbit_index_audit.json')
    parser.add_argument('--log', type=Path,
                        default=FAST_ROOT / 'results' / 'orbit_index_tests.log')
    args = parser.parse_args()
    before = manifest()
    suite = unittest.defaultTestLoader.discover(str(FAST_ROOT / 'tests'),
                                               pattern='test_orbit_index.py')
    log = io.StringIO()
    stdout = io.StringIO()
    start = time.perf_counter()
    with redirect_stdout(stdout):
        result = unittest.TextTestRunner(stream=log, verbosity=2).run(suite)
    seconds = time.perf_counter() - start
    after = manifest()
    if before != after:
        raise AssertionError('a pinned source changed during the audit')
    content = log.getvalue() + stdout.getvalue()
    counts = [json.loads(line) for line in stdout.getvalue().splitlines()
              if line.startswith('{')]
    evidence = dict(schema='compiled-orbit-index-audit-v1', success=result.wasSuccessful(),
                    tests_run=result.testsRun, elapsed_seconds=seconds,
                    failures=len(result.failures), errors=len(result.errors),
                    counters=counts, source_manifest_before=before, source_manifest_after=after)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.log.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(evidence, indent=2) + '\n')
    args.log.write_text(content)
    print(json.dumps(evidence, indent=2))
    return 0 if result.wasSuccessful() else 1


if __name__ == '__main__':
    raise SystemExit(main())
