"""Run the focused old/new geometry regression gate and preserve exact output."""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import sys
import time
import unittest


MODULES = [
    'test_interval_orbits', 'test_interval_orbit_verify', 'test_weighted_orbits',
    'test_normal_surface', 'test_normal_surface_orbits', 'test_normal_surface_certificate',
    'test_normal_boundary', 'test_normal_multiplicity', 'test_normal_components',
    'test_normal_components_integration', 'test_orbit_transversal', 'test_topology_spectrum',
    'test_normal_topology_spectrum',
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', default='topology_research/results')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    sys.path.insert(0, str(root))
    output = Path(args.output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    suite = unittest.TestSuite()
    for name in MODULES:
        suite.addTests(unittest.defaultTestLoader.discover(str(root / 'tests'),
                                                           pattern=name + '.py'))
    start = time.perf_counter()
    log = output / 'regression_tests.txt'
    with log.open('w') as stream:
        result = unittest.TextTestRunner(stream=stream, verbosity=2).run(suite)
    record = dict(test_methods=result.testsRun, failures=len(result.failures),
        errors=len(result.errors), skipped=len(result.skipped),
        seconds=time.perf_counter() - start, success=result.wasSuccessful(),
        python=sys.version, platform=platform.platform(), modules=MODULES,
        log_sha256=hashlib.sha256(log.read_bytes()).hexdigest())
    (output / 'regression_summary.json').write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps(record, indent=2))
    if not result.wasSuccessful():
        for case, trace in result.failures + result.errors:
            print(str(case))
            print(trace)
        raise SystemExit(1)


if __name__ == '__main__':
    main()
