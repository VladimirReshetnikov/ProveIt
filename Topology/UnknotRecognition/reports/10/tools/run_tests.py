#!/usr/bin/env python3
"""Run every test and write exact comparison counts and environment metadata."""
import json
import platform
import sys
import time
import unittest
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tests'))
start = time.perf_counter()
suite = unittest.defaultTestLoader.discover(str(ROOT / 'tests'))
result = unittest.TextTestRunner(verbosity=2).run(suite)
import test_component_kernel as ck
import test_restart_entropy as re
report = {'python': sys.version, 'platform': platform.platform(),
          'test_methods': result.testsRun, 'failures': len(result.failures),
          'errors': len(result.errors), 'seconds': time.perf_counter() - start,
          'counts': {**ck.COUNTS, **re.COUNTS},
          'scope': 'kernel/reference-excerpt and abstract restart tests; not a full recognizer run'}
(ROOT / 'results').mkdir(exist_ok=True)
(ROOT / 'results' / 'tests.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
raise SystemExit(not result.wasSuccessful())
