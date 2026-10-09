#!/usr/bin/env python3
"""Run the maintained suite and persist an explicit completion ledger."""
import argparse
import hashlib
import json
from pathlib import Path
import sys
import time
import unittest


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('fast_directory', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    fast = args.fast_directory.resolve()
    sys.path.insert(0, str(fast))
    output = args.output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()
    suite = unittest.defaultTestLoader.discover(str(fast / 'tests'))
    expected = suite.countTestCases()
    print(json.dumps({'phase': 'starting', 'discovered_tests': expected}), flush=True)
    with output.with_suffix('.log').open('w') as stream:
        result = unittest.TextTestRunner(stream=stream, verbosity=2).run(suite)
    ledger = {
        'completed': True,
        'discovered_tests': expected,
        'tests_run': result.testsRun,
        'successful': result.wasSuccessful(),
        'failures': [{'test': str(test), 'traceback': trace}
                     for test, trace in result.failures],
        'errors': [{'test': str(test), 'traceback': trace}
                   for test, trace in result.errors],
        'skipped': [{'test': str(test), 'reason': reason}
                    for test, reason in result.skipped],
        'seconds': time.monotonic() - start,
        'python': sys.version,
        'source_hashes': {
            str(path.relative_to(fast)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted((fast / 'fastunknot').rglob('*.py'))
        },
    }
    output.write_text(json.dumps(ledger, indent=2) + '\n')
    print(json.dumps({key: ledger[key] for key in
                      ['completed', 'discovered_tests', 'tests_run', 'successful', 'seconds']}),
          flush=True)
    return 0 if result.wasSuccessful() and result.testsRun == expected else 1


if __name__ == '__main__':
    raise SystemExit(main())
