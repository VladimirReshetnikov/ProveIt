#!/usr/bin/env python3
"""Focused additive-change regression suite, with optional Regina on sys.path."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import sys
import time
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT/'tests'))

MODULES = [
    'test_normal_support', 'test_normal_support_peeling',
    'test_normal_packed_components', 'test_normal_ray_blocks',
    'test_normal_support_diagram', 'test_normal_surface',
    'test_normal_surface_orbits', 'test_normal_surface_certificate',
    'test_normal_components', 'test_normal_coordinate_basis',
    'test_normal_multiplicity', 'test_normal_components_integration',
    'test_weighted_orbits', 'test_interval_orbit_verify',
    'test_weighted_fold_overlay', 'test_diagram_exterior',
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--regina-path', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.regina_path:
        sys.path.insert(0, str(args.regina_path.resolve()))
        # Maintained integration tests spawn isolated Regina workers. They
        # require the same optional dependency path as the parent process.
        os.environ['PYTHONPATH'] = str(args.regina_path.resolve()) + os.pathsep + os.environ.get('PYTHONPATH', '')
    sources = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
               for p in sorted((ROOT/'fastunknot').glob('*.py'))}
    started = time.perf_counter()
    result = unittest.TextTestRunner(verbosity=2).run(
        unittest.defaultTestLoader.loadTestsFromNames(MODULES))
    report = dict(schema='support-focused-regression-v1', python=sys.version,
                  modules=MODULES, tests_run=result.testsRun,
                  failures=[dict(test=str(t), traceback=s) for t, s in result.failures],
                  errors=[dict(test=str(t), traceback=s) for t, s in result.errors],
                  skipped=[dict(test=str(t), reason=s) for t, s in result.skipped],
                  passed=result.wasSuccessful(), seconds=time.perf_counter()-started,
                  production_sha256=sources)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    return 0 if result.wasSuccessful() else 1


if __name__ == '__main__':
    raise SystemExit(main())
