"""Record actual validation counts for the factorial-free output strategy."""

import argparse
import json
from pathlib import Path
import platform
import sys
import time
import unittest


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, default=Path('output_test_results.json'))
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    sys.path.insert(0, str(root))
    suite = unittest.defaultTestLoader.discover(str(root/'tests'), pattern='test_output_forests.py')
    started = time.perf_counter()
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    tests = sys.modules['test_output_forests'].OutputForestTests
    data = {'python': sys.version, 'platform': platform.platform(),
            'seconds': time.perf_counter() - started,
            'test_methods': result.testsRun, 'failures': len(result.failures),
            'errors': len(result.errors), 'skips': len(result.skipped),
            'forest_oracle_cases': tests.forest_oracle_cases,
            'success': result.wasSuccessful(),
            'scope': 'Factorial-free output assignment kernel, independent full positive-pivot and top-tree oracles, producer-disabled positive and complete-negative replay, mutation and parity/resource controls.'}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(data, indent=2)+'\n')
    return 0 if result.wasSuccessful() else 1


if __name__ == '__main__':
    raise SystemExit(main())
